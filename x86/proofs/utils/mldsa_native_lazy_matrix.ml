(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the FULL proofs of the matrix-vector products of   *)
(* the x86-64 code of mldsa-native built with MLD_CONFIG_REDUCE_RAM          *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_lazy and _yvec_lazy, whose   *)
(* results are folded with mld_lazy_acc of common/mldsa_native_lazy.ml), the *)
(* x86-64 counterpart of arm/proofs/utils/mldsa_native_lazy_matrix.ml. Both  *)
(* copy rho from the structure mld_polymat_lazy into a buffer of 64 bytes on *)
(* the stack, as two 128-bit words, and store the indices j and i of each    *)
(* entry that they sample as the two bytes after it, so that                 *)
(* mldsa_poly_uniform reads the seed rho || j || i of 34 bytes               *)
(* (mld_matrix_seed). The bytes come from 8-bit registers holding small      *)
(* counters, whose values the simulation gives as word(val x MOD 256) of the *)
(* 64-bit register x (LAZY_BYTE_64), or through a byte of the stack and      *)
(* MOVZX (LAZY_BYTE_ZX). LAZY_RHO_OF_HALVES gives the 32 bytes of rho in the *)
(* buffer from the two stores, and LAZY_SEED the seed from rho and the two   *)
(* bytes after it. The loops of these products use the tools of              *)
(* common/fips204/properties/mldsa_native_lazy_matrix.ml (MLD_LAZY_TERM_TAC, *)
(* MLD_LAZY_ROW_TAC, MLD_LAZY_JOIN_TAC, MLD_LAZY_GEN_OLD_TAC, ...), shared   *)
(* with the AArch64 proofs.                                                  *)
(* ========================================================================= *)

needs "common/mldsa_native_lazy.ml";;
needs "common/fips204/properties/mldsa_native_lazy_matrix.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_matrix.ml";;

let LAZY_RHO_OF_HALVES = prove
 (`!a:int64 n s:x86state.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s =
        word(n MOD 340282366920938463463374607431768211456) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 340282366920938463463374607431768211456)
        ==> read (memory :> bytes(a,32)) s = n`,
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 128`)] THEN
  REWRITE_TAC[MLD_BYTES_32_OF_HALVES]);;

let LAZY_SEED = prove
 (`!a:int64 r i j s:x86state.
        read (memory :> bytes(a,32)) s = r /\
        read (memory :> bytes8(word_add a (word 32))) s = word j /\
        read (memory :> bytes8(word_add a (word 33))) s = word i /\
        i < 256 /\ j < 256
        ==> read (memory :> bytes(a,34)) s = mld_matrix_seed r i j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_matrix_seed; ARITH_RULE `34 = 32 + 2`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONJUNCT2 MLD_BYTES2] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let LAZY_BYTE_64 = prove
 (`!n. n < 256 ==> word(val(word n:int64) MOD 256):byte = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n < 2 EXP 64` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th])
  THENL [UNDISCH_TAC `n < 256` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

let LAZY_BYTE_ZX = prove
 (`!n. n < 256
       ==> word(val(word_zx(word_zx(word n:byte):int32):int64) MOD 256):byte =
           word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n < 256` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(*** The first column of mld_lazy_acc ***)

let MLD_POLY_OF_0 = prove
 (`!x:num->int32. mld_poly_of x 0 = x`,
  REWRITE_TAC[FUN_EQ_THM; mld_poly_of; MULT_CLAUSES; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The rows of a vector in memory are aligned as the vector is               *)
(* (LAZY_ALIGNED_ROW).                                                       *)
(* ------------------------------------------------------------------------- *)

let LAZY_ALIGNED_ROW = prove
 (`!w:int64 k. aligned 16 w ==> aligned 16 (word_add w (word(1024 * k)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALIGNED_WORD_ADD THEN
  ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE);;

(* ------------------------------------------------------------------------- *)
(* The 16-bit nonce kappa + c of the sampling of polynomial c of y, which    *)
(* the code computes with MOVZX, a 32-bit ADD of the column counter and      *)
(* another MOVZX (just the MOVZX for c = 0): LAZY_NONCE_TAC c rewrites the   *)
(* postcondition of mldsa_poly_uniform_gamma1 with the nonce as              *)
(* word(kappa + c), proving the equation on the values, modulo 2^16, with    *)
(* the nested reductions modulo powers of 2 collapsed (LAZY_MOD_MOD).        *)
(* ------------------------------------------------------------------------- *)

let LAZY_MOD_MOD =
  map (fun (m,n) ->
         GEN `x:num` (CONV_RULE NUM_REDUCE_CONV
          (SPECL [`x:num`; `2`; mk_small_numeral m; mk_small_numeral n]
                 MOD_MOD_EXP_MIN)))
      [16,16; 16,32; 16,64; 32,16; 32,32; 32,64; 64,16; 64,32; 64,64];;

let LAZY_NONCE_ADD = prove
 (`!a b. (a MOD 65536 + b MOD 4294967296) MOD 65536 = (a + b) MOD 65536`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC LAZY_MOD_MOD);;

let LAZY_NONCE_PROVE_TAC =
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_ADD;
              DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC LAZY_MOD_MOD THEN
  REWRITE_TAC[LAZY_NONCE_ADD; ADD_CLAUSES];;

let LAZY_NONCE_TAC c =
  let is_g1 t =
    match t with
      Const(n,_) -> String.length n >= 23 &&
                    String.sub n 0 23 = "mld_poly_uniform_gamma1"
    | _ -> false in
  let target = mk_comb(`word:num->int16`,
                       mk_binop `(+):num->num->num` `kappa:num` c) in
  FIRST_X_ASSUM(fun th ->
    let ct = concl th in
    if not (is_forall ct) || can (find_term ((=) `mld_polyvec`)) ct
    then NO_TAC else
    match find_terms (fun t -> is_comb t && is_comb(rator t) &&
                               is_comb(rator(rator t)) &&
                               is_g1(rator(rator(rator t)))) ct with
      [t] ->
        let nonce = rand(rator t) in
        let eth = prove(mk_eq(nonce,target),LAZY_NONCE_PROVE_TAC) in
        ASSUME_TAC(REWRITE_RULE[eth] th)
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The events of nested loops are handled with MLD_LAZY_GEN_OLD_TAC and      *)
(* MLD_LAZY_EVENTS_REASSOC_TAC (common/fips204/properties/                   *)
(* mldsa_native_lazy_matrix.ml); LAZY_APPEND_REASSOC3 is the reassociation   *)
(* that the x86-64 product needs for ENSURES_EVENTS_SEQUENCE_TAC.            *)
(* ------------------------------------------------------------------------- *)

let LAZY_APPEND_REASSOC3 = prove
 (`!a b c d:(A)list.
        APPEND (APPEND (APPEND a b) c) d = APPEND a (APPEND b (APPEND c d))`,
  REWRITE_TAC[APPEND_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The copy of rho to the buffer at base in the frame: LAZY_RHO_PREP_TAC, at *)
(* the start, gives the two 128-bit halves of rho at mat + 1024 and its      *)
(* bound and names the YMM registers that the code loads them into, and      *)
(* LAZY_RHO_STORED_TAC base s, after the stores, the 32 bytes at base.       *)
(* ------------------------------------------------------------------------- *)

let LAZY_RHO_PREP_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
     `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl))
  THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rho < 2 EXP 256` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
     (can (term_match []
       `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o
      concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    MP_TAC(ISPECL [`word_add mat (word 1024):int64`; `32`;
                   `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SAMPLING_GHOST_REGS_TAC [`YMM1`; `YMM2`] "s0";;

let LAZY_RHO_STORED_TAC base s =
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  MP_TAC(SPECL [base; `rho:num`; s] LAZY_RHO_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The signing product (mld_polyvec_matrix_pointwise_montgomery_yvec_lazy)   *)
(* for l columns and k rows: the template of the events, with the first      *)
(* column apart (f_ev_..0), as its rows take another path, and for the other *)
(* columns the events up to the NTT of the polynomial of y (cb), the setting *)
(* of the row pointer (ib), the rows and the end of the column (ce); and the *)
(* parts of the invariants: the frame (from RSP at bot + 1495 up), the       *)
(* transformed vector y (YHAT), the vector w with the sums for the columns   *)
(* up to c, polynomial c of YHAT in scratch, and the rows of w before i      *)
(* (DONE) and from i (REST) in the inner loop.                               *)
(* ------------------------------------------------------------------------- *)

let LAZY_YVEC_ARGS = "w mat y scratch rp rho pc stackpointer returnaddress";;

let LAZY_YVEC_TEMPLATE ncols nrows =
  let lam =
    "\\(w:int64) (mat:int64) (y:int64) (scratch:int64) (rp:int64) " ^
    "(rho:num) (pc:num) (stackpointer:int64) (returnaddress:int64)." in
  let a = LAZY_YVEC_ARGS in
  let f n = "(f_ev_" ^ n ^ " " ^ a ^ ")"
  and fl n = "(f_ev_" ^ n ^ " " ^ a ^ " l)" in
  let col0 =
    "(APPEND (APPEND " ^ f "ce0" ^ " (APPEND (ENUMERATEL " ^ nrows ^
    " (\\k. f_ev_row0 " ^ a ^ " k)) " ^ f "ib0" ^ ")) " ^ f "cb0" ^ ")"
  and col =
    "(\\l. APPEND (APPEND " ^ fl "ce" ^ " (APPEND (ENUMERATEL " ^ nrows ^
    " (\\k. f_ev_row " ^ a ^ " l k)) " ^ fl "ib" ^ ")) " ^ fl "cb" ^ ")" in
  parse_term(lam ^ " APPEND " ^ f "epil" ^ " (APPEND (ENUMERATEL " ^
             string_of_int(int_of_string ncols - 1) ^ " " ^ col ^
             ") (APPEND " ^ col0 ^ " " ^ f "prol" ^
             ")) :(uarch_event)list");;

let LAZY_YVEC_FRAME =
  "read RSP s = word_add bot (word 1495) /\\
   read RBP s = word_add stackpointer (word 1662) /\\
   read (memory :> bytes64 (word_add stackpointer (word 1670))) s =
   returnaddress /\\
   read (memory :> bytes64 (word_add stackpointer (word 1662))) s =
   rbp_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1654))) s =
   r15_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1646))) s =
   r14_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1638))) s =
   r13_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1630))) s =
   r12_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1622))) s =
   rbx_init /\\
   ~read DF s /\\
   read (memory :> bytes64 (word_add bot (word 1503))) s = y /\\
   read (memory :> bytes64 (word_add bot (word 1511))) s = w /\\
   read (memory :> bytes64 (word_add bot (word 1519))) s =
   word_add bot (word 1527) /\\
   read (memory :> bytes (word_add bot (word 1527),32)) s = rho /\\
   read (memory :> bytes64 y) s = rp /\\
   read (memory :> bytes16 (word_add y (word 8))) s = word kappa /\\
   read (memory :> bytes (rp,64)) s = rhoprime";;

let LAZY_YVEC_YHAT g1 =
  "(mld_polyvec_map mld_poly_ntt
     (mld_polyvec (\\j. " ^ g1 ^ " rhoprime (word(kappa + j)))))";;

let LAZY_YVEC_W yhat n c =
  "(!j. j < " ^ n ^ "
        ==> read (memory :> bytes32 (word_add w (word(4 * j)))) s =
            mld_polyvec (\\r. mld_lazy_acc rho r " ^ yhat ^ " " ^ c ^ ") j)";;

let LAZY_YVEC_SCRATCH yhat c =
  "(!j. j < 256
        ==> read (memory :> bytes32 (word_add scratch (word(4 * j)))) s =
            mld_poly_of " ^ yhat ^ " " ^ c ^ " j)";;

let LAZY_YVEC_DONE yhat c =
  "(!j. j < 256 * i
        ==> read (memory :> bytes32 (word_add w (word(4 * j)))) s =
            mld_polyvec (\\r. mld_lazy_acc rho r " ^ yhat ^ " " ^ c ^ ") j)";;

let LAZY_YVEC_REST yhat n c =
  "(!j. 256 * i <= j /\\ j < " ^ n ^ "
        ==> read (memory :> bytes32 (word_add w (word(4 * j)))) s =
            mld_polyvec (\\r. mld_lazy_acc rho r " ^ yhat ^ " " ^ c ^ ") j)";;

(* ------------------------------------------------------------------------- *)
(* A FULL theorem from one for the vector t as the reduced-RAM code computes *)
(* it, as in arm/proofs/utils/mldsa_native_lazy_matrix.ml: th is the theorem *)
(* for MLD_LAZY_FULL0 stmt of                                                *)
(* common/fips204/properties/mldsa_native_lazy_matrix.ml (stmt with          *)
(* mld_compute_t_lazy for mld_compute_t and without the hypothesis on the    *)
(* bound of s1hat), and MLD_LAZY_FULL_OF_FULL0_TAC th lemtac proves stmt     *)
(* from it, with the facts that lemtac adds to the assumptions (from the     *)
(* hypotheses of stmt), which rewrite the postcondition of th to that of     *)
(* stmt. The events are the same, so that the SAFE theorem follows from th   *)
(* by SAFE_OF_FULL_TAC as from a FULL theorem.                               *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_FULL_OF_FULL0_TAC full0 lemtac =
  MP_TAC full0 THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC_ALL o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "ensures"
                             with Failure _ -> false)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM)) THEN
  lemtac THEN
  X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  ASM_SIMP_TAC[];;
