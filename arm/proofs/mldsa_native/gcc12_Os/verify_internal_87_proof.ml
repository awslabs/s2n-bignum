(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the proof (see verify_internal_87_spec.ml).  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/verify_internal_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

let VI87_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_EXEC;;

let VI87_MEXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL;;

let VI87_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The template of the events. The f_events arguments are ARGS below. The    *)
(* events split on the alignment of the stack (the buffers are at            *)
(* stackpointer + 5248 or + 5232), on the norm check of z (nf: the whole run *)
(* when it fails), on ext (hash or copy: from the start to join1, where mu   *)
(* is ready), mid (from join1 to the loop over the rows), the rows (row: one *)
(* whose hints unpack, rowf: the first one whose hints do not, after which   *)
(* the loop stops), and the end after the loop: hf when some hints do not    *)
(* unpack, and acc or rej after the hash and the compare of c~ otherwise.    *)
(* The number of rows done is K: 8, or the first failing row plus 1.         *)
(* ------------------------------------------------------------------------- *)

let VI87_ARGS =
  "sig m mlen pre prelen pk ext sigb pkb M PRE guard mf pc stackpointer " ^
  "returnaddress";;

let VI87_LAMBDA =
  "\\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (pk:int64) " ^
  "(ext:int64) (sigb:num->byte) (pkb:num->byte) (M:num) PRE " ^
  "(guard:int64) (mf:int64) (pc:num) (stackpointer:int64) " ^
  "(returnaddress:int64).";;

let VI87_HOK = "mld_unpack_hints_ret 75 8 (\\t. sigb(4544 + t)) i = word 0";;

let VI87_HINTSOK = "(!i. i < 8 ==> " ^ VI87_HOK ^ ")";;

let VI87_K =
  "(if " ^ VI87_HINTSOK ^ " then 8 else (minimal i. ~(" ^ VI87_HOK ^
  ")) + 1)";;

let VI87_NORMOK =
  "mld_polyvec_chknorm 7 (mld_polyvec_unpack 640 mld_polyz_unpack_19 " ^
  "(\\j. sigb(64 + j))) (word 524168) = word 0";;

let VI87_OK =
  "mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168 " ^
  "mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 sigb pkb " ^
  "(if word_zx ext = (word 0:int32) " ^
  "then mld_verify_mu 2592 pkb prelen PRE mlen M else M MOD 2 EXP 512)";;

let VI87_TEMPLATE_CASE x =
  let f n = "(f_ev_" ^ n ^ "_" ^ x ^ " " ^ VI87_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ "_" ^ x ^ " " ^ VI87_ARGS ^ " i)" in
  "(if " ^ VI87_NORMOK ^ " then " ^
  "APPEND (if " ^ VI87_HINTSOK ^ " then (if " ^ VI87_OK ^ " then " ^
  f "acc" ^ " else " ^ f "rej" ^ ") else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ VI87_K ^ " (\\i. if " ^ VI87_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if word_zx ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ")";;

let VI87_TEMPLATE =
  parse_term(VI87_LAMBDA ^ " if aligned 32 stackpointer then " ^
             VI87_TEMPLATE_CASE "a" ^ " else " ^ VI87_TEMPLATE_CASE "u" ^
             " :(uarch_event)list");;

(* ------------------------------------------------------------------------- *)
(* The same conditions in the proof, where the variable for PRE is PRE' (PRE *)
(* is also the predecessor function), and the values the code computes: mu,  *)
(* the vectors z and zhat, c, rho, and row i of w1' (the use of the hints on *)
(* caddq(invntt(reduce(A z - c t1 2^d)))) and its packing W1B.               *)
(* ------------------------------------------------------------------------- *)

let VI87_HOK_TM = parse_term VI87_HOK;;
let VI87_HINTSOK_TM = parse_term VI87_HINTSOK;;
let VI87_NORMOK_TM = parse_term VI87_NORMOK;;
let VI87_EXT0 = `word_zx (ext:int64) = (word 0:int32)`;;

let VI87_MU =
  `if word_zx (ext:int64) = (word 0:int32)
   then mld_verify_mu 2592 pkb prelen PRE' mlen M else M MOD 2 EXP 512`;;

let VI87_OK_TM =
  subst [VI87_MU,`mu:num`]
   `mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168
     mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 (sigb:num->byte)
     (pkb:num->byte) mu`;;

let VI87_RHO = `num_of_bytelist (list_of_seq (pkb:num->byte) 32)`;;

let VI87_Z =
  `mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. (sigb:num->byte)(64 + j))`;;

let VI87_ZHAT = mk_comb(`mld_polyvec_map mld_poly_ntt`,VI87_Z);;

let VI87_C = `num_of_bytelist (list_of_seq (sigb:num->byte) 64)`;;

let VI87_CP = mk_comb(`mld_poly_challenge 60 64`,VI87_C);;

let VI87_CPHAT = mk_comb(`mld_poly_ntt`,VI87_CP);;

let VI87_ACC =
  subst [VI87_RHO,`rho:num`; VI87_ZHAT,`zhat:num->int32`]
   `mld_polyvec_pointwise_acc_montgomery 7
     (\j. mld_polyvec_matrix_expand 7 rho (1792 * i + j)) zhat`;;

let VI87_T1 = `mld_polyt1_unpack (\j. (pkb:num->byte) (32 + 320 * i + j))`;;
let VI87_SHL = mk_comb(`mld_poly_shiftl`,VI87_T1);;
let VI87_NTT1 = mk_comb(`mld_poly_ntt`,VI87_SHL);;
let VI87_PWM =
  list_mk_comb(`mld_poly_pointwise_montgomery`,[VI87_NTT1;VI87_CPHAT]);;
let VI87_SUB = list_mk_comb(`mld_poly_sub`,[VI87_ACC;VI87_PWM]);;
let VI87_RED = mk_comb(`mld_poly_reduce`,VI87_SUB);;
let VI87_INVT = mk_comb(`mld_poly_invntt_tomont`,VI87_RED);;
let VI87_CADDQ = mk_comb(`mld_poly_caddq`,VI87_INVT);;
let VI87_HINTS = `mld_unpack_hints 75 (\t. (sigb:num->byte) (4544 + t)) i`;;
let VI87_UH = list_mk_comb(`mld_poly_use_hint_32`,[VI87_CADDQ;VI87_HINTS]);;

let VI87_W1B =
  subst [VI87_RHO,`rho:num`; VI87_ZHAT,`zhat:num->int32`;
         VI87_CPHAT,`cphat:num->int32`]
   `mld_polyvec_pack 128 mld_polyw1_pack_32
     (mld_polyvec
       (mld_verify_w1 7 mld_poly_use_hint_32 rho zhat cphat pkb 75
         (\t. (sigb:num->byte) (4544 + t))))`;;

let VI87_W1NUM =
  mk_comb(`num_of_bytelist`,
          mk_comb(mk_comb(`list_of_seq:(num->byte)->num->byte list`,VI87_W1B),
                  `1024`));;

(*** mld_verify_internal_ok for the parameters of ML-DSA-87 ***)

let VI87_OK_THM = GEN_ALL(prove
 (subst [VI87_W1B,`w1b:num->byte`]
  `mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168
       mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 (sigb:num->byte)
       (pkb:num->byte) mu <=>
     mld_polyvec_chknorm 7
       (mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(64 + j)))
       (word 524168) = word 0 /\
     (!i. i < 8
          ==> mld_unpack_hints_ret 75 8 (\t. sigb(4544 + t)) i = word 0) /\
     (!j. j < 64
          ==> sigb j =
              mld_shake256_byte 1088
               (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b 1024)) j)`,
  REWRITE_TAC[mld_verify_internal_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `64 + 7 * 640 + t = 4544 + t`;
              ARITH_RULE `64 + 8 * 128 = 1088`; ARITH_RULE `8 * 128 = 1024`]));;

(*** Equal byte arrays, and the outputs of mld_H87 with empty inputs ***)

let MLD_NUM_BYTELIST_EQ = prove
 (`!(f:num->byte) g len.
        num_of_bytelist(list_of_seq f len) = num_of_bytelist(list_of_seq g len)
        <=> (!i. i < len ==> f i = g i)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `bytelist_of_num len`) THEN
    MP_TAC(ISPEC `list_of_seq (f:num->byte) len` BYTELIST_OF_NUM_OF_BYTELIST) THEN
    MP_TAC(ISPEC `list_of_seq (g:num->byte) len` BYTELIST_OF_NUM_OF_BYTELIST) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `list_of_seq (f:num->byte) len = list_of_seq g len`
     MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL i:byte list->byte`) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    ASM_SIMP_TAC[]]);;

let VI87_H1 = prove
 (`!x. mld_shake256_byte (2592 + 0 + 0)
         (x + 2 EXP (8 * 2592) * (0 + 2 EXP (8 * 0) * 0)) =
       mld_shake256_byte 2592 x`,
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let VI87_H3 = prove
 (`!mu w. mld_shake256_byte (64 + 1024 + 0)
            (mu + 2 EXP (8 * 64) * (w + 2 EXP (8 * 1024) * 0)) =
          mld_shake256_byte 1088 (mu + 2 EXP 512 * w)`,
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ARITH_RULE `8 * 64 = 512`]);;

(* ------------------------------------------------------------------------- *)
(* Calls and the cleanup. The allowed variables of the events are the        *)
(* arguments of f_events, and in the loop body and after the loop the row    *)
(* index i and the generalized events so far (front, old). VI87_CLEANUP_TAC  *)
(* allowed n simulates the code from join3 (+0x248) to the return from state *)
(* n: the nine calls of mld_zeroize_6 for the buffers, the check of the      *)
(* canary and the restoring of the registers.                                *)
(* ------------------------------------------------------------------------- *)

let VI87_ALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `pk:int64`; `ext:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
   `PRE':num`; `guard:int64`; `mf:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let VI87_ALLOWED_LOOP =
  `front:(uarch_event)list`::`i:num`::VI87_ALLOWED;;

let VI87_ALLOWED_OLD = `old:(uarch_event)list`::VI87_ALLOWED;;

let VI87_CALL_GEN_TAC allowed name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc VI87_EXEC name ilist
   allowed n;;

let VI87_CALL_TAC = VI87_CALL_GEN_TAC VI87_ALLOWED;;
let VI87_LOOP_CALL_TAC = VI87_CALL_GEN_TAC VI87_ALLOWED_LOOP;;
let VI87_POST_CALL_TAC = VI87_CALL_GEN_TAC VI87_ALLOWED_OLD;;

let VI87_ZERO_TAC allowed n len =
  VI87_CALL_GEN_TAC allowed "H_ZERO"
   [`read X0 s`; mk_small_numeral len; `pc:num`; `read SP s`; `read X30 s`] n;;

(*** The cleanup from join3 (+0x22c): the nine zeroizations of the buffers   ***)
(*** (the polynomials at 20480 and 21504, the matrix, c-hat, z, c2, c~, mu   ***)
(*** and the buffer of w1'), the check of the canary and the return.        ***)

let VI87_CLEANUP_TAC allowed n =
  let z = VI87_ZERO_TAC allowed in
  VERIF_DROP_MEM_TAC (VERIF_KEEP_FRAME 5088 5200 74056) THEN
  ARM_STEPS_TAC VI87_EXEC ((n+1)--(n+3)) THEN z (n+4) 1024 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+5)--(n+7)) THEN z (n+8) 1024 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+9)--(n+11)) THEN z (n+12) 57344 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+13)--(n+15)) THEN z (n+16) 1024 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+17)--(n+19)) THEN z (n+20) 7168 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+21)--(n+23)) THEN z (n+24) 64 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+25)--(n+27)) THEN z (n+28) 64 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+29)--(n+32)) THEN z (n+33) 64 THEN
  ARM_STEPS_TAC VI87_EXEC ((n+34)--(n+36)) THEN z (n+37) 1024 THEN
  ARM_STEPS_TAC VI87_EXEC [n+38] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI87_EXEC ((n+39)--(n+56));;

(*** Words of the stack frame ***)

let VI87_SP k =
  mk_comb(`word_add (stackpointer:int64)`,
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(* ------------------------------------------------------------------------- *)
(* The prologue, to the norm check: the chunks of c~ that the code copies,   *)
(* the bytes of z for mldsa87_polyvecl_unpack_z, and the bound of the norm   *)
(* check as the code passes it.                                              *)
(* ------------------------------------------------------------------------- *)

let VI87_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5263 5248 5232;;

let VI87_SIG_CHUNKS_TAC =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `4627`; `sigb:num->byte`; `s0:armstate`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1;2;3];;

let VI87_BYTES_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let VI87_BND_TAC =
  let tm = `word_zx (word 524168:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let VI87_CHUNK_NORM_RULE th =
  REWRITE_RULE[WORD_ADD_0; EXP; DIV_1]
   (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) th);;

let VI87_M_CHUNKS_TAC =
  SUBGOAL_THEN `64 <= mlen` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral i;
                  `s0:armstate`] VERIF_BYTES128_OF_BYTES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o VI87_CHUNK_NORM_RULE)) [0;1;2;3];;

let VI87_PROLOGUE_TAC pretac =
  FULL_INIT_TAC THEN pretac THEN VI87_SIG_CHUNKS_TAC THEN
  ARM_STEPS_TAC VI87_EXEC (1--6) THEN MEXP_BUFFER_TAC VI87_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC VI87_EXEC (7--9) THEN
  ARM_STEPS_TAC VI87_EXEC [10] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI87_EXEC (11--40) THEN
  VI87_BYTES_SLICE_TAC
   `!j. j < 4480
        ==> read(memory :> bytes8(word_add sig (word(64 + j)))) s40 =
            (sigb:num->byte)(64 + j)` THEN
  VI87_CALL_TAC "H_UNPACKZ"
   [`read X0 s`; `read X1 s`; `\j. (sigb:num->byte)(64 + j)`; `pc:num`;
    `read SP s`; `read X30 s`] 41 THEN
  ARM_STEPS_TAC VI87_EXEC (42--45) THEN
  VI87_CALL_TAC "H_CHKNORM"
   [`read X0 s`; VI87_Z; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 46 THEN
  VI87_BND_TAC THEN
  ARM_STEPS_TAC VI87_EXEC (47--51) THEN VERIF_PC_TAC [VI87_NORMOK_TM];;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: the setup of the result -6 and the cleanup.         *)
(* ------------------------------------------------------------------------- *)

let VI87_NF_TAC =
  VI87_PROLOGUE_TAC ALL_TAC THEN ARM_STEPS_TAC VI87_EXEC [52] THEN
  VI87_CLEANUP_TAC VI87_ALLOWED 52 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VI87_OK_THM] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join1 (+0x118), where mu is ready, with the buffers at       *)
(* stackpointer + b: the matrix, z, t1 (the polynomial of t1 and the hints), *)
(* tmp, cp, buf (w1' packed, first tr), c2, c and mu at offsets 0, 57344,    *)
(* 64512, 65536, 66560, 67584, 68608, 68672 and 68736. The frame of the      *)
(* function is at stackpointer + 5088, with the saved registers, then the    *)
(* pointer pk, that of c, pre, prelen and ext (32 bits) at 5192 to 5228      *)
(* (the slot at 5184 holds mlen, later the address in buf of the next row of *)
(* w1'), and the canary at 74056.                                            *)
(* ------------------------------------------------------------------------- *)

let VI87_FRAME_FACTS b =
  let sp n = "word_add stackpointer (word " ^ string_of_int n ^ ")" in
  let q n v = "read (memory :> bytes64 (" ^ sp n ^ ")) s = " ^ v ^ " /\\\n    " in
  "read SP s = " ^ sp 5088 ^ " /\\\n    " ^
  q 5088 "x19_init" ^ q 5096 "x20_init" ^ q 5104 "x21_init" ^
  q 5112 "x22_init" ^ q 5120 "x23_init" ^ q 5128 "x24_init" ^
  q 5136 "x25_init" ^ q 5144 "x26_init" ^ q 5152 "x27_init" ^
  q 5160 "x28_init" ^ q 5168 "returnaddress" ^ q 5192 "pk" ^
  q 5200 (sp (b + 68672)) ^ q 5208 "pre" ^ q 5216 "word prelen" ^
  "read (memory :> bytes32 (" ^ sp 5228 ^ ")) s = word_zx (ext:int64) /\\\n    " ^
  q 74056 "canary" ^
  "read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
      s = guard /\\
    read (memory :> bytes64 guard) s = canary /\\
    read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
    read (memory :> bytes (ea,el)) s = ev /\\
    (!j. j < 4627
         ==> read (memory :> bytes8 (word_add sig (word j))) s = sigb j) /\\
    (!j. j < 2592
         ==> read (memory :> bytes8 (word_add pk (word j))) s = pkb j)";;

let VI87_JOIN1 b =
  let n k = string_of_int(b + k) in
  let s = "\\s. " ^ VI87_FRAME_FACTS b ^ " /\\
    read X19 s = word_add stackpointer (word " ^ n 0 ^ ") /\\
    read X20 s = word 0 /\\
    read X21 s = word_add stackpointer (word " ^ n 65536 ^ ") /\\
    read X22 s = word_add stackpointer (word " ^ n 64512 ^ ") /\\
    read X23 s = sig /\\
    read X24 s = word_add stackpointer (word " ^ n 67584 ^ ") /\\
    read X25 s = m /\\
    read X26 s = word_add stackpointer (word " ^ n 68608 ^ ") /\\
    read X27 s = word_add stackpointer (word " ^ n 57344 ^ ") /\\
    read X28 s = word_add stackpointer (word " ^ n 66560 ^ ") /\\
    (!j. j < 1792
         ==> read (memory :> bytes32
                    (word_add stackpointer
                      (word (" ^ n 57344 ^ " + 4 * j)))) s =
             VI87Z j) /\\
    read (memory :> bytes (word_add stackpointer (word " ^ n 68736 ^ "),64)) s =
      VI87MU /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68672 ^ "))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68688 ^ "))) s =
      mld_chunk128 sigb 1 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68704 ^ "))) s =
      mld_chunk128 sigb 2 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68720 ^ "))) s =
      mld_chunk128 sigb 3" in
  subst [VI87_MU,`VI87MU:num`; VI87_Z,`VI87Z:num->int32`] (parse_term s);;

(*** The loop invariant at loop1 for row i (the facts that need the rows  ***)
(*** before i to have succeeded are under that hypothesis)                ***)

let VI87_INV b =
  let n k = string_of_int(b + k) in
  let s = "\\i s. " ^ VI87_FRAME_FACTS b ^ " /\\
    read X19 s = word_add stackpointer (word " ^ n 0 ^ ") /\\
    read X21 s = word_add stackpointer (word " ^ n 65536 ^ ") /\\
    read X22 s = word_add stackpointer (word " ^ n 64512 ^ ") /\\
    read X23 s = sig /\\
    read X24 s = word_add stackpointer (word " ^ n 67584 ^ ") /\\
    read X26 s = word_add stackpointer (word " ^ n 68608 ^ ") /\\
    read X27 s = word_add stackpointer (word " ^ n 57344 ^ ") /\\
    read X28 s = word_add stackpointer (word " ^ n 66560 ^ ") /\\
    (!j. j < 14336
         ==> read (memory :> bytes32
                    (word_add stackpointer (word (" ^ n 0 ^ " + 4 * j)))) s =
             mld_polyvec_matrix_expand 7 VI87RHO j) /\\
    (!j. j < 1792
         ==> read (memory :> bytes32
                    (word_add stackpointer
                      (word (" ^ n 57344 ^ " + 4 * j)))) s =
             VI87ZHAT j) /\\
    (!j. j < 256
         ==> read (memory :> bytes32
                    (word_add stackpointer
                      (word (" ^ n 66560 ^ " + 4 * j)))) s =
             VI87CPHAT j) /\\
    read (memory :> bytes (word_add stackpointer (word " ^ n 68736 ^ "),64)) s =
      VI87MU /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68672 ^ "))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68688 ^ "))) s =
      mld_chunk128 sigb 1 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68704 ^ "))) s =
      mld_chunk128 sigb 2 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 68720 ^ "))) s =
      mld_chunk128 sigb 3 /\\
    ((!j. j < i ==> mld_unpack_hints_ret 75 8 (\\t. sigb(4544 + t)) j = word 0)
     ==> read X20 s = word i /\\
         read (memory :> bytes64 (word_add stackpointer (word 5184))) s =
           word_add stackpointer (word (" ^ n 67584 ^ " + 128 * i)) /\\
         (0 < i ==> read X25 s = word 0) /\\
         (!j. j < 128 * i
              ==> read (memory :> bytes8
                         (word_add stackpointer
                           (word (" ^ n 67584 ^ " + j)))) s =
                  VI87W1B j))" in
  subst [VI87_MU,`VI87MU:num`; VI87_W1B,`VI87W1B:num->byte`;
         VI87_RHO,`VI87RHO:num`; VI87_ZHAT,`VI87ZHAT:num->int32`;
         VI87_CPHAT,`VI87CPHAT:num->int32`]
        (parse_term s);;

let VI87_PC2 =
  parse_term("if " ^ VI87_HINTSOK ^
             " then pc + mldsa87_verify_internal_loop1_exit1" ^
             " else pc + mldsa87_verify_internal_loop1_exit2");;

(* ------------------------------------------------------------------------- *)
(* From the start to join1: the norm check passes, then mu is copied from m  *)
(* (ext nonzero, the 4 chunks of the 64 bytes at m) or computed (ext zero):  *)
(* tr, the first 64 bytes of SHAKE256(pk), by mld_H87, then mu by mld_H87 of *)
(* tr, pre and m, and the zeroing of tr.                                     *)
(* ------------------------------------------------------------------------- *)

let VI87_MU_OF_CHUNKS_TAC a s =
  MP_TAC(SPECL [a; `M:num`; `4`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC];;

let VI87_COPY_TAC b =
  ARM_STEPS_TAC VI87_EXEC [52;53] THEN
  VERIF_PC_TAC [VI87_EXT0] THEN ARM_STEPS_TAC VI87_EXEC (54--59) THEN
  VI87_MU_OF_CHUNKS_TAC (VI87_SP(b + 68736)) `s59:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

let VI87_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 2592)`;;

(*** The empty input of mld_H87 (NULL, length 0): its bytes are 0, and it    ***)
(*** does not overlap the stack of the call                                 ***)

let VI87_NULL_TAC s =
  SUBGOAL_THEN
   (subst [s,`s:armstate`] `read (memory :> bytes(word 0,0)) s = 0`)
   ASSUME_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64)
      (val(word_add stackpointer (word 4480):int64),608) (0,0)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[]; ALL_TAC];;

(*** tr, the first 64 bytes of SHAKE256 of the public key ***)

let VI87_TRNUM =
  subst [VI87_PKNUM,`p:num`]
   `num_of_bytelist (list_of_seq (mld_shake256_byte 2592 p) 64)`;;

let VI87_HASH_TAC b =
  ARM_STEPS_TAC VI87_EXEC [52;53] THEN VERIF_PC_TAC [VI87_EXT0] THEN
  ARM_STEPS_TAC VI87_EXEC (54--61) THEN
  MP_TAC(SPECL [`pk:int64`; `2592`; `pkb:num->byte`; `s61:armstate`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  VI87_NULL_TAC `s61:armstate` THEN
  VI87_CALL_TAC "H_H87"
   [`read X0 s`; `read X1 s`; `2592`; `read X3 s`; `0`; `read X5 s`; `0`;
    VI87_PKNUM; `0`; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 62 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VI87_H1]) THEN
  ARM_STEPS_TAC VI87_EXEC (63--70) THEN
  VI87_CALL_TAC "H_H87"
   [`read X0 s`; `read X1 s`; `64`; `read X3 s`; `prelen:num`; `read X5 s`;
    `mlen:num`; VI87_TRNUM; `PRE':num`; `M:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 71 THEN
  ARM_STEPS_TAC VI87_EXEC (72--74) THEN
  VI87_CALL_TAC "H_ZERO"
   [`read X0 s`; `64`; `pc:num`; `read SP s`; `read X30 s`] 75 THEN
  REWRITE_TAC[mld_verify_mu] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2 EXP (8 * 64)` (concl th)
    then REWRITE_RULE[ARITH_RULE `8 * 64 = 512`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* From join1 to the loop: the NTT of z, the expansion of the matrix from    *)
(* rho (32 bytes of pk), the challenge from c~ (its 4 chunks) and its NTT.   *)
(* ------------------------------------------------------------------------- *)

let VI87_MID_TAC b =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC VI87_EXEC (1--2) THEN
  VI87_CALL_TAC "H_VNTT"
   [`read X0 s`; VI87_Z; `pc:num`; `read SP s`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC VI87_EXEC (4--6) THEN
  MP_TAC(SPECL [`pk:int64`; `32`; `pkb:num->byte`; `s6:armstate`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  VI87_CALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; VI87_RHO; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 7 THEN
  ARM_STEPS_TAC VI87_EXEC (8--11) THEN
  MP_TAC(SPECL [VI87_SP(b + 68672); `sigb:num->byte`; `4`; `s11:armstate`]
               VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  VI87_CALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; VI87_C; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 12 THEN
  ARM_STEPS_TAC VI87_EXEC (13--14) THEN
  VI87_CALL_TAC "H_NTT" [`read X0 s`; VI87_CP; `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC VI87_EXEC [16] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_H_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body for row i: the rows before i succeeded and i < 8            *)
(* (VERIF_ROWS), the calls for row i up to the unpacking of its hints, and   *)
(* then either the use of the hints and the packing of the row, or the exit  *)
(* to loop1_exit2 if the hints do not unpack. The events before the row are  *)
(* kept opaque as front after the rows already done.                         *)
(* ------------------------------------------------------------------------- *)

let VI87_ROWS_TAC =
  MP_TAC(BETA_RULE(SPECL [mk_abs(`i:num`,VI87_HOK_TM); `8`; `i:num`]
                         VERIF_ROWS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(lhand(concl th)) &&
    fst(dest_forall(lhand(concl th))) = `j:num`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

let VI87_I_ZX = `word_zx(word_zx(word i:int64):int32):int64 = word i`;;

let VI87_I1_ZX =
  `word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
   word(i + 1)`;;

let VI87_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  VERIF_GEN_TAIL_TAC false "front" THEN
  FULL_INIT_TAC THEN VI87_ROWS_TAC THEN
  SUBGOAL_THEN (mk_conj(VI87_I_ZX,VI87_I1_ZX)) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC VI87_EXEC (1--5) THEN VERIF_REG_RULE_TAC[ASSUME VI87_I_ZX] THEN
  VI87_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`;
    mk_comb(`mld_polyvec_matrix_expand 7`,VI87_RHO); VI87_ZHAT; `i:num`;
    `pc:num`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC VI87_EXEC (7--10) THEN VERIF_REG_RULE_TAC[ASSUME VI87_I_ZX] THEN
  VI87_BYTES_SLICE_TAC
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word(32 + 320 * i + j)))) s10 =
            (pkb:num->byte)(32 + 320 * i + j)` THEN
  VI87_LOOP_CALL_TAC "H_T1"
   [`read X0 s`; `read X1 s`; `\j. (pkb:num->byte)(32 + 320 * i + j)`;
    `i:num`; `pc:num`; `read X30 s`] 11 THEN
  ARM_STEPS_TAC VI87_EXEC (12--13) THEN
  VI87_LOOP_CALL_TAC "H_SHIFTL"
   [`read X0 s`; VI87_T1; `pc:num`; `read X30 s`] 14 THEN
  ARM_STEPS_TAC VI87_EXEC (15--16) THEN
  VI87_LOOP_CALL_TAC "H_NTT"
   [`read X0 s`; VI87_SHL; `pc:num`; `read X30 s`] 17 THEN
  ARM_STEPS_TAC VI87_EXEC (18--20) THEN
  VI87_LOOP_CALL_TAC "H_PWM"
   [`read X0 s`; `read X1 s`; VI87_NTT1; VI87_CPHAT; `pc:num`;
    `read X30 s`] 21 THEN
  ARM_STEPS_TAC VI87_EXEC (22--24) THEN
  VI87_LOOP_CALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`; VI87_ACC; VI87_PWM; `pc:num`;
    `read X30 s`] 25 THEN
  ARM_STEPS_TAC VI87_EXEC (26--27) THEN
  VI87_LOOP_CALL_TAC "H_RED"
   [`read X0 s`; VI87_SUB; `pc:num`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC VI87_EXEC (29--30) THEN
  VI87_LOOP_CALL_TAC "H_INV"
   [`read X0 s`; VI87_RED; `pc:num`; `read X30 s`] 31 THEN
  ARM_STEPS_TAC VI87_EXEC (32--33) THEN
  VI87_LOOP_CALL_TAC "H_CADDQ"
   [`read X0 s`; VI87_INVT; `pc:num`; `read X30 s`] 34 THEN
  ARM_STEPS_TAC VI87_EXEC (35--38) THEN
  VERIF_REG_RULE_TAC[ASSUME VI87_I_ZX] THEN
  VI87_BYTES_SLICE_TAC
   `!j. j < 83
        ==> read(memory :> bytes8(word_add sig (word(4544 + j)))) s38 =
            (sigb:num->byte)(4544 + j)` THEN
  VI87_LOOP_CALL_TAC "H_HINTS"
   [`read X0 s`; `read X1 s`; `\t. (sigb:num->byte)(4544 + t)`; `i:num`;
    `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC VI87_EXEC (40--41);;

let VI87_PC_OK_TAC =
  ASM_CASES_TAC `i + 1 < 8` THENL
   [SUBGOAL_THEN `~(i + 1 = 8)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i + 1 < 8`; ASSUME `~(i + 1 = 8)`];
    SUBGOAL_THEN `i + 1 = 8` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN VI87_HINTSOK_TM ASSUME_TAC THENL
     [VERIF_IMP_CASE_TAC `~(i + 1 < 8)`; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~(i + 1 < 8)`; ASSUME `i + 1 = 8`;
                ASSUME VI87_HINTSOK_TM]];;

let VI87_JOIN_W1_TAC =
  DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[MATCH_MP (SPEC_ALL VERIF_W1B_ROW_32) (ASSUME `k < 128`)] THEN
      REWRITE_TAC[mld_verify_w1] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      FIRST_ASSUM(fun th ->
        MATCH_MP_TAC(REWRITE_RULE[GSYM ADD_ASSOC] th)) THEN
      FIRST_ASSUM ACCEPT_TAC]];;

let VI87_BODY_OK_TAC =
  VERIF_MP_CASE_TAC VI87_HOK_TM THEN
  ARM_STEPS_TAC VI87_EXEC (42--44) THEN
  VI87_LOOP_CALL_TAC "H_USEHINT"
   [`read X0 s`; `read X1 s`; VI87_CADDQ; VI87_HINTS; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC VI87_EXEC (46--49) THEN
  VERIF_REG_RULE_TAC[ASSUME VI87_I1_ZX] THEN
  VI87_LOOP_CALL_TAC "H_W1PACK"
   [`read X0 s`; `read X1 s`; VI87_UH; `pc:num`; `read X30 s`] 50 THEN
  ARM_STEPS_TAC VI87_EXEC (51--55) THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN W32_LOOP_TEST_TAC THEN
  CONJ_TAC THENL [VI87_PC_OK_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [VI87_JOIN_W1_TAC; ALL_TAC] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI87_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg VI87_HOK_TM) THEN VERIF_FINAL_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg VI87_HOK_TM)];
    ALL_TAC] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI87_BODY_TAC =
  VI87_BODY1_TAC THEN
  ASM_CASES_TAC VI87_HOK_TM THEN VERIF_PC_TAC [VI87_HOK_TM] THENL
   [VI87_BODY_OK_TAC; VI87_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop, if all hints unpack: c2 = the first 64 bytes of           *)
(* SHAKE256(mu || w1') by mld_H87, then the comparison of c~ and c2 by       *)
(* mld_ct_memcmp_3, which returns 0 iff they are equal, iff the signature is *)
(* accepted.                                                                 *)
(* ------------------------------------------------------------------------- *)

let VI87_C2NUM =
  subst [VI87_MU,`mu:num`; VI87_W1NUM,`w:num`]
   `num_of_bytelist (list_of_seq (mld_shake256_byte 1088 (mu + 2 EXP 512 * w))
                      64)`;;

let VI87_OK_EQ_TAC =
  SUBGOAL_THEN (mk_eq(mk_eq(VI87_C,VI87_C2NUM),VI87_OK_TM)) ASSUME_TAC THENL
   [REWRITE_TAC[VI87_OK_THM; ASSUME VI87_NORMOK_TM;
                EQT_INTRO(ASSUME VI87_HINTSOK_TM); MLD_NUM_BYTELIST_EQ];
    ALL_TAC];;

(*** The simulation evaluates 2 EXP 512 in the conditional PC, so the     ***)
(*** equivalence and the case are rewritten in that form                 ***)

let VI87_NRM = CONV_RULE(DEPTH_CONV NUM_EXP_CONV);;

let VI87_CMP_PC_TAC =
  W(fun (asl,w) ->
    let eqv = VI87_NRM(snd(find (fun (_,th) ->
      concl th = mk_eq(mk_eq(VI87_C,VI87_C2NUM),VI87_OK_TM)) asl)) in
    let case =
      try EQT_INTRO(VI87_NRM(snd(find (fun (_,th) ->
            concl th = VI87_OK_TM) asl)))
      with Failure _ ->
        EQF_INTRO(VI87_NRM(snd(find (fun (_,th) ->
            concl th = mk_neg VI87_OK_TM) asl))) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`)
             (concl th)
      then REWRITE_RULE[]
            (CONV_RULE(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)
              (REWRITE_RULE[eqv; case] th))
      else th));;

let VI87_W1_BYTES_TAC b s =
  MP_TAC(SPECL [VI87_SP(b + 67584); `1024`; VI87_W1B; s]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_32`)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC];;

let VI87_POST_OK_TAC b =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC VI87_EXEC (1--9) THEN
  VI87_W1_BYTES_TAC b `s9:armstate` THEN
  VI87_NULL_TAC `s9:armstate` THEN
  VI87_POST_CALL_TAC "H_H87"
   [`read X0 s`; `read X1 s`; `64`; `read X3 s`; `1024`; `read X5 s`; `0`;
    VI87_MU; VI87_W1NUM; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 10 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VI87_H3]) THEN
  ARM_STEPS_TAC VI87_EXEC (11--14) THEN
  MP_TAC(SPECL [VI87_SP(b + 68672); `sigb:num->byte`; `4`; `s14:armstate`]
               VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  VI87_POST_CALL_TAC "H_CMP"
   [`read X0 s`; `read X1 s`; `64`; VI87_C; VI87_C2NUM; `pc:num`;
    `read X30 s`] 15 THEN
  ARM_STEPS_TAC VI87_EXEC (16--17) THEN
  VI87_OK_EQ_TAC THEN
  ASM_CASES_TAC VI87_OK_TM THEN VI87_CMP_PC_TAC THENL
   [VI87_CLEANUP_TAC VI87_ALLOWED_OLD 17;
    ARM_STEPS_TAC VI87_EXEC [18] THEN
    VI87_CLEANUP_TAC VI87_ALLOWED_OLD 18] THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(*** If some hints do not unpack: the result -6 and the cleanup ***)

let VI87_POST_HF_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC VI87_EXEC [1] THEN
  VI87_CLEANUP_TAC VI87_ALLOWED_OLD 1 THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0; VI87_OK_THM] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

let VI87_POST_TAC b =
  VERIF_GEN_TAIL_TAC true "old" THEN
  ASM_CASES_TAC VI87_HINTSOK_TM THENL
   [REWRITE_TAC[EQT_INTRO(ASSUME VI87_HINTSOK_TM); ARITH_RULE `0 < 8`] THEN
    VI87_POST_OK_TAC b;
    REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg VI87_HINTSOK_TM))] THEN
    VI87_POST_HF_TAC];;

(* ------------------------------------------------------------------------- *)
(* Each case of the alignment of the stack, with the buffers at              *)
(* stackpointer + b, and of the norm check.                                  *)
(* ------------------------------------------------------------------------- *)

let VI87_CASE_TAC b =
  ASM_CASES_TAC VI87_NORMOK_TM THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term VI87_K)
     `pc + mldsa87_verify_internal_loop1` VI87_PC2 (VI87_INV b) THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                  CONJUNCT1 LT; LT_REFL] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa87_verify_internal_join1`
       (VI87_JOIN1 b) THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC VI87_EXT0 THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th])
        THENL
         [VI87_PROLOGUE_TAC ALL_TAC THEN VI87_HASH_TAC b;
          VI87_PROLOGUE_TAC VI87_M_CHUNKS_TAC THEN VI87_COPY_TAC b];
        VI87_MID_TAC b];
      VI87_BODY_TAC;
      VI87_POST_TAC b];
    VI87_NF_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    MAP_EVERY (fun (fth,name) ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC
        (MATCH_MP fth (MATCH_MP MEMSET_RET_FULL_CONTRACT th)) name)
     [VI87_MEXP_FULL,"H_MEXP";
      MLDSA_NATIVE_POLY_CHALLENGE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_CHAL";
      MLDSA_NATIVE_H_87_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_H87";
      MLDSA_NATIVE_ZEROIZE_6_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_ZERO"]) THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_FULL
               th) "H_HINTS") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_UNPACK_Z_87_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_UNPACKZ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_CHKNORM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_87_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_VNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI87_ROW_FULL "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_UNPACK_PK_T1_87_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_SHIFTL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_PWM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_SUB_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CADDQ_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_USEHINT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_W1PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_CT_MEMCMP_3_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_CMP" THEN
  CONCRETIZE_F_EVENTS_TAC VI87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst VI87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 74064):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28) THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    VI87_CASE_TAC 5248;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    VI87_CASE_TAC 5232]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
