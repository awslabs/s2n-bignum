(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the proof (see verify_internal_44_spec.ml).  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/verify_internal_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

let VI44_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_EXEC;;

let VI44_MEXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL;;

let VI44_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The template of the events. The f_events arguments are ARGS below. The    *)
(* events split on the alignment of the stack (the buffers are at            *)
(* stackpointer + 5248 or + 5264), on the norm check of z (nf: the whole run *)
(* when it fails), on ext (hash or copy: from the start to join1, where mu   *)
(* is ready), mid (from join1 to the loop over the rows), the rows (row: one *)
(* whose hints unpack, rowf: the first one whose hints do not, after which   *)
(* the loop stops), and the end after the loop: hf when some hints do not    *)
(* unpack, and acc or rej after the hash and the compare of c~ otherwise.    *)
(* The number of rows done is K: 4, or the first failing row plus 1.         *)
(* ------------------------------------------------------------------------- *)

let VI44_ARGS =
  "sig m mlen pre prelen pk ext sigb pkb M PRE guard mf pc stackpointer " ^
  "returnaddress";;

let VI44_LAMBDA =
  "\\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (pk:int64) " ^
  "(ext:int64) (sigb:num->byte) (pkb:num->byte) (M:num) PRE " ^
  "(guard:int64) (mf:int64) (pc:num) (stackpointer:int64) " ^
  "(returnaddress:int64).";;

let VI44_HOK = "mld_unpack_hints_ret 80 4 (\\t. sigb(2336 + t)) i = word 0";;

let VI44_HINTSOK = "(!i. i < 4 ==> " ^ VI44_HOK ^ ")";;

let VI44_K =
  "(if " ^ VI44_HINTSOK ^ " then 4 else (minimal i. ~(" ^ VI44_HOK ^
  ")) + 1)";;

let VI44_NORMOK =
  "mld_polyvec_chknorm 4 (mld_polyvec_unpack 576 mld_polyz_unpack_17 " ^
  "(\\j. sigb(32 + j))) (word 130994) = word 0";;

let VI44_OK =
  "mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994 " ^
  "mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 sigb pkb " ^
  "(if word_zx ext = (word 0:int32) " ^
  "then mld_verify_mu 1312 pkb prelen PRE mlen M else M MOD 2 EXP 512)";;

let VI44_TEMPLATE_CASE x =
  let f n = "(f_ev_" ^ n ^ "_" ^ x ^ " " ^ VI44_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ "_" ^ x ^ " " ^ VI44_ARGS ^ " i)" in
  "(if " ^ VI44_NORMOK ^ " then " ^
  "APPEND (if " ^ VI44_HINTSOK ^ " then (if " ^ VI44_OK ^ " then " ^
  f "acc" ^ " else " ^ f "rej" ^ ") else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ VI44_K ^ " (\\i. if " ^ VI44_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if word_zx ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ")";;

let VI44_TEMPLATE =
  parse_term(VI44_LAMBDA ^ " if aligned 32 stackpointer then " ^
             VI44_TEMPLATE_CASE "a" ^ " else " ^ VI44_TEMPLATE_CASE "u" ^
             " :(uarch_event)list");;

(* ------------------------------------------------------------------------- *)
(* The same conditions in the proof, where the variable for PRE is PRE' (PRE *)
(* is also the predecessor function), and the values the code computes: mu,  *)
(* the vectors z and zhat, c, rho, and row i of w1' (the use of the hints on *)
(* caddq(invntt(reduce(A z - c t1 2^d)))) and its packing W1B.               *)
(* ------------------------------------------------------------------------- *)

let VI44_HOK_TM = parse_term VI44_HOK;;
let VI44_HINTSOK_TM = parse_term VI44_HINTSOK;;
let VI44_NORMOK_TM = parse_term VI44_NORMOK;;
let VI44_EXT0 = `word_zx (ext:int64) = (word 0:int32)`;;

let VI44_MU =
  `if word_zx (ext:int64) = (word 0:int32)
   then mld_verify_mu 1312 pkb prelen PRE' mlen M else M MOD 2 EXP 512`;;

let VI44_OK_TM =
  subst [VI44_MU,`mu:num`]
   `mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994
     mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 (sigb:num->byte)
     (pkb:num->byte) mu`;;

let VI44_RHO = `num_of_bytelist (list_of_seq (pkb:num->byte) 32)`;;

let VI44_Z =
  `mld_polyvec_unpack 576 mld_polyz_unpack_17 (\j. (sigb:num->byte)(32 + j))`;;

let VI44_ZHAT = mk_comb(`mld_polyvec_map mld_poly_ntt`,VI44_Z);;

let VI44_C = `num_of_bytelist (list_of_seq (sigb:num->byte) 32)`;;

let VI44_CP = mk_comb(`mld_poly_challenge 39 32`,VI44_C);;

let VI44_CPHAT = mk_comb(`mld_poly_ntt`,VI44_CP);;

let VI44_ACC =
  subst [VI44_RHO,`rho:num`; VI44_ZHAT,`zhat:num->int32`]
   `mld_polyvec_pointwise_acc_montgomery 4
     (\j. mld_polyvec_matrix_expand 4 rho (1024 * i + j)) zhat`;;

let VI44_T1 = `mld_polyt1_unpack (\j. (pkb:num->byte) (32 + 320 * i + j))`;;
let VI44_SHL = mk_comb(`mld_poly_shiftl`,VI44_T1);;
let VI44_NTT1 = mk_comb(`mld_poly_ntt`,VI44_SHL);;
let VI44_PWM =
  list_mk_comb(`mld_poly_pointwise_montgomery`,[VI44_NTT1;VI44_CPHAT]);;
let VI44_SUB = list_mk_comb(`mld_poly_sub`,[VI44_ACC;VI44_PWM]);;
let VI44_RED = mk_comb(`mld_poly_reduce`,VI44_SUB);;
let VI44_INVT = mk_comb(`mld_poly_invntt_tomont`,VI44_RED);;
let VI44_CADDQ = mk_comb(`mld_poly_caddq`,VI44_INVT);;
let VI44_HINTS = `mld_unpack_hints 80 (\t. (sigb:num->byte) (2336 + t)) i`;;
let VI44_UH = list_mk_comb(`mld_poly_use_hint_88`,[VI44_CADDQ;VI44_HINTS]);;

let VI44_W1B =
  subst [VI44_RHO,`rho:num`; VI44_ZHAT,`zhat:num->int32`;
         VI44_CPHAT,`cphat:num->int32`]
   `mld_polyvec_pack 192 mld_polyw1_pack_88
     (mld_polyvec
       (mld_verify_w1 4 mld_poly_use_hint_88 rho zhat cphat pkb 80
         (\t. (sigb:num->byte) (2336 + t))))`;;

let VI44_W1NUM =
  mk_comb(`num_of_bytelist`,
          mk_comb(mk_comb(`list_of_seq:(num->byte)->num->byte list`,VI44_W1B),
                  `768`));;

(*** mld_verify_internal_ok for the parameters of ML-DSA-44 ***)

let VI44_OK_THM = GEN_ALL(prove
 (subst [VI44_W1B,`w1b:num->byte`]
  `mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994
       mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 (sigb:num->byte)
       (pkb:num->byte) mu <=>
     mld_polyvec_chknorm 4
       (mld_polyvec_unpack 576 mld_polyz_unpack_17 (\j. sigb(32 + j)))
       (word 130994) = word 0 /\
     (!i. i < 4
          ==> mld_unpack_hints_ret 80 4 (\t. sigb(2336 + t)) i = word 0) /\
     (!j. j < 32
          ==> sigb j =
              mld_shake256_byte 832
               (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b 768)) j)`,
  REWRITE_TAC[mld_verify_internal_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `32 + 4 * 576 + t = 2336 + t`;
              ARITH_RULE `64 + 4 * 192 = 832`; ARITH_RULE `4 * 192 = 768`]));;

(*** Equal byte arrays, and the outputs of mld_H44 with empty inputs ***)

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

let VI44_H1 = prove
 (`!x. mld_shake256_byte (1312 + 0 + 0)
         (x + 2 EXP (8 * 1312) * (0 + 2 EXP (8 * 0) * 0)) =
       mld_shake256_byte 1312 x`,
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let VI44_H3 = prove
 (`!mu w. mld_shake256_byte (64 + 768 + 0)
            (mu + 2 EXP (8 * 64) * (w + 2 EXP (8 * 768) * 0)) =
          mld_shake256_byte 832 (mu + 2 EXP 512 * w)`,
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ARITH_RULE `8 * 64 = 512`]);;

(* ------------------------------------------------------------------------- *)
(* Calls and the cleanup. The allowed variables of the events are the        *)
(* arguments of f_events, and in the loop body and after the loop the row    *)
(* index i and the generalized events so far (front, old). VI44_CLEANUP_TAC  *)
(* allowed n simulates the code from join3 (+0x22c) to the return from state *)
(* n: the nine calls of mld_zeroize_2 for the buffers, the check of the      *)
(* canary and the restoring of the registers.                                *)
(* ------------------------------------------------------------------------- *)

let VI44_ALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `pk:int64`; `ext:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
   `PRE':num`; `guard:int64`; `mf:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let VI44_ALLOWED_LOOP =
  `front:(uarch_event)list`::`i:num`::VI44_ALLOWED;;

let VI44_ALLOWED_OLD = `old:(uarch_event)list`::VI44_ALLOWED;;

let VI44_CALL_GEN_TAC allowed name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc VI44_EXEC name ilist
   allowed n;;

let VI44_CALL_TAC = VI44_CALL_GEN_TAC VI44_ALLOWED;;
let VI44_LOOP_CALL_TAC = VI44_CALL_GEN_TAC VI44_ALLOWED_LOOP;;
let VI44_POST_CALL_TAC = VI44_CALL_GEN_TAC VI44_ALLOWED_OLD;;

let VI44_ZERO_TAC allowed n len =
  VI44_CALL_GEN_TAC allowed "H_ZERO"
   [`read X0 s`; mk_small_numeral len; `pc:num`; `read SP s`; `read X30 s`] n;;

(*** The cleanup from join3 (+0x22c): the nine zeroizations of the buffers   ***)
(*** (the polynomials at 20480 and 21504, the matrix, c-hat, z, c2, c~, mu   ***)
(*** and the buffer of w1'), the check of the canary and the return.        ***)

let VI44_CLEANUP_TAC allowed n =
  let z = VI44_ZERO_TAC allowed in
  VERIF_DROP_MEM_TAC (VERIF_KEEP_FRAME 5104 5208 29720) THEN
  ARM_STEPS_TAC VI44_EXEC ((n+1)--(n+3)) THEN z (n+4) 1024 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+5)--(n+7)) THEN z (n+8) 1024 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+9)--(n+11)) THEN z (n+12) 16384 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+13)--(n+15)) THEN z (n+16) 1024 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+17)--(n+19)) THEN z (n+20) 4096 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+21)--(n+24)) THEN z (n+25) 32 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+26)--(n+28)) THEN z (n+29) 32 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+30)--(n+33)) THEN z (n+34) 64 THEN
  ARM_STEPS_TAC VI44_EXEC ((n+35)--(n+37)) THEN z (n+38) 768 THEN
  ARM_STEPS_TAC VI44_EXEC [n+39] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI44_EXEC ((n+40)--(n+55));;

(*** Words of the stack frame ***)

let VI44_SP k =
  mk_comb(`word_add (stackpointer:int64)`,
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(* ------------------------------------------------------------------------- *)
(* The prologue, to the norm check: the chunks of c~ that the code copies,   *)
(* the bytes of z for mldsa44_polyvecl_unpack_z, and the bound of the norm   *)
(* check as the code passes it.                                              *)
(* ------------------------------------------------------------------------- *)

let VI44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5279 5248 5264;;

let VI44_SIG_CHUNKS_TAC =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `2420`; `sigb:num->byte`; `s0:armstate`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1];;

let VI44_BYTES_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let VI44_BND_TAC =
  let tm = `word_zx (word 130994:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let VI44_CHUNK_NORM_RULE th =
  REWRITE_RULE[WORD_ADD_0; EXP; DIV_1]
   (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) th);;

let VI44_M_CHUNKS_TAC =
  SUBGOAL_THEN `64 <= mlen` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral i;
                  `s0:armstate`] VERIF_BYTES128_OF_BYTES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o VI44_CHUNK_NORM_RULE)) [0;1;2;3];;

let VI44_PROLOGUE_TAC pretac =
  FULL_INIT_TAC THEN pretac THEN VI44_SIG_CHUNKS_TAC THEN
  ARM_STEPS_TAC VI44_EXEC (1--10) THEN MEXP_BUFFER_TAC VI44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC VI44_EXEC (11--21) THEN
  ARM_STEPS_TAC VI44_EXEC [22] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI44_EXEC (23--35) THEN
  VI44_BYTES_SLICE_TAC
   `!j. j < 2304
        ==> read(memory :> bytes8(word_add sig (word(32 + j)))) s35 =
            (sigb:num->byte)(32 + j)` THEN
  VI44_CALL_TAC "H_UNPACKZ"
   [`read X0 s`; `read X1 s`; `\j. (sigb:num->byte)(32 + j)`; `pc:num`;
    `read SP s`; `read X30 s`] 36 THEN
  ARM_STEPS_TAC VI44_EXEC (37--40) THEN
  VI44_CALL_TAC "H_CHKNORM"
   [`read X0 s`; VI44_Z; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 41 THEN
  VI44_BND_TAC THEN
  ARM_STEPS_TAC VI44_EXEC (42--46) THEN VERIF_PC_TAC [VI44_NORMOK_TM];;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: the setup of the result -6 and the cleanup.         *)
(* ------------------------------------------------------------------------- *)

let VI44_NF_TAC =
  VI44_PROLOGUE_TAC ALL_TAC THEN ARM_STEPS_TAC VI44_EXEC [47] THEN
  VI44_CLEANUP_TAC VI44_ALLOWED 47 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VI44_OK_THM] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join1 (+0x10c), where mu is ready, with the buffers at       *)
(* stackpointer + b: the matrix, z, t1 (the polynomial of t1 and the hints), *)
(* tmp, cp, buf (w1' packed, first tr), mu, c2 and c at offsets 0, 16384,    *)
(* 20480, 21504, 22528, 23552, 24320, 24384 and 24416. The frame of the      *)
(* function is at stackpointer + 5104, with the saved registers, then the    *)
(* pointer pk, that of c, mlen, pre, prelen and ext (32 bits) at 5200 to     *)
(* 5244, and the canary at 29720.                                            *)
(* ------------------------------------------------------------------------- *)

let VI44_FRAME_FACTS b =
  let sp n = "word_add stackpointer (word " ^ string_of_int n ^ ")" in
  let q n v = "read (memory :> bytes64 (" ^ sp n ^ ")) s = " ^ v ^ " /\\\n    " in
  "read SP s = " ^ sp 5104 ^ " /\\\n    " ^
  q 5104 "x19_init" ^ q 5112 "x20_init" ^ q 5120 "x21_init" ^
  q 5128 "x22_init" ^ q 5136 "x23_init" ^ q 5144 "x24_init" ^
  q 5152 "x25_init" ^ q 5160 "x26_init" ^ q 5168 "x27_init" ^
  q 5176 "x28_init" ^ q 5184 "returnaddress" ^ q 5200 "pk" ^
  q 5208 (sp (b + 24416)) ^ q 5216 "word mlen" ^ q 5224 "pre" ^
  q 5232 "word prelen" ^
  "read (memory :> bytes32 (" ^ sp 5244 ^ ")) s = word_zx (ext:int64) /\\\n    " ^
  q 29720 "canary" ^
  "read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
      s = guard /\\
    read (memory :> bytes64 guard) s = canary /\\
    read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
    read (memory :> bytes (ea,el)) s = ev /\\
    (!j. j < 2420
         ==> read (memory :> bytes8 (word_add sig (word j))) s = sigb j) /\\
    (!j. j < 1312
         ==> read (memory :> bytes8 (word_add pk (word j))) s = pkb j)";;

let VI44_JOIN1 b =
  let n k = string_of_int(b + k) in
  let s = "\\s. " ^ VI44_FRAME_FACTS b ^ " /\\
    read X19 s = word_add stackpointer (word " ^ n 0 ^ ") /\\
    read X20 s = word 0 /\\
    read X21 s = word_add stackpointer (word " ^ n 21504 ^ ") /\\
    read X22 s = word_add stackpointer (word " ^ n 20480 ^ ") /\\
    read X23 s = word_add stackpointer (word " ^ n 23552 ^ ") /\\
    read X24 s = sig /\\
    read X25 s = word_add stackpointer (word " ^ n 24576 ^ ") /\\
    read X26 s = word_add stackpointer (word " ^ n 16384 ^ ") /\\
    read X27 s = word_add stackpointer (word " ^ n 22528 ^ ") /\\
    read X28 s = m /\\
    (!j. j < 1024
         ==> read (memory :> bytes32
                    (word_add stackpointer
                      (word (" ^ n 16384 ^ " + 4 * j)))) s =
             VI44Z j) /\\
    read (memory :> bytes (word_add stackpointer (word " ^ n 24320 ^ "),64)) s =
      VI44MU /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 24416 ^ "))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 24432 ^ "))) s =
      mld_chunk128 sigb 1" in
  subst [VI44_MU,`VI44MU:num`; VI44_Z,`VI44Z:num->int32`] (parse_term s);;

(*** The loop invariant at loop1 for row i (the facts that need the rows  ***)
(*** before i to have succeeded are under that hypothesis)                ***)

let VI44_INV b =
  let n k = string_of_int(b + k) in
  let s = "\\i s. " ^ VI44_FRAME_FACTS b ^ " /\\
    read X19 s = word_add stackpointer (word " ^ n 0 ^ ") /\\
    read X21 s = word_add stackpointer (word " ^ n 21504 ^ ") /\\
    read X22 s = word_add stackpointer (word " ^ n 20480 ^ ") /\\
    read X23 s = word_add stackpointer (word " ^ n 23552 ^ ") /\\
    read X24 s = sig /\\
    read X26 s = word_add stackpointer (word " ^ n 16384 ^ ") /\\
    read X27 s = word_add stackpointer (word " ^ n 22528 ^ ") /\\
    (!j. j < 4096
         ==> read (memory :> bytes32
                    (word_add stackpointer (word (" ^ n 0 ^ " + 4 * j)))) s =
             mld_polyvec_matrix_expand 4 VI44RHO j) /\\
    (!j. j < 1024
         ==> read (memory :> bytes32
                    (word_add stackpointer
                      (word (" ^ n 16384 ^ " + 4 * j)))) s =
             VI44ZHAT j) /\\
    (!j. j < 256
         ==> read (memory :> bytes32
                    (word_add stackpointer
                      (word (" ^ n 22528 ^ " + 4 * j)))) s =
             VI44CPHAT j) /\\
    read (memory :> bytes (word_add stackpointer (word " ^ n 24320 ^ "),64)) s =
      VI44MU /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 24416 ^ "))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 24432 ^ "))) s =
      mld_chunk128 sigb 1 /\\
    ((!j. j < i ==> mld_unpack_hints_ret 80 4 (\\t. sigb(2336 + t)) j = word 0)
     ==> read X20 s = word i /\\
         read X28 s =
           word_add stackpointer (word (" ^ n 23552 ^ " + 192 * i)) /\\
         (0 < i ==> read X25 s = word 0) /\\
         (!j. j < 192 * i
              ==> read (memory :> bytes8
                         (word_add stackpointer
                           (word (" ^ n 23552 ^ " + j)))) s =
                  VI44W1B j))" in
  subst [VI44_MU,`VI44MU:num`; VI44_W1B,`VI44W1B:num->byte`;
         VI44_RHO,`VI44RHO:num`; VI44_ZHAT,`VI44ZHAT:num->int32`;
         VI44_CPHAT,`VI44CPHAT:num->int32`]
        (parse_term s);;

let VI44_PC2 =
  parse_term("if " ^ VI44_HINTSOK ^
             " then pc + mldsa44_verify_internal_loop1_exit1" ^
             " else pc + mldsa44_verify_internal_loop1_exit2");;

(* ------------------------------------------------------------------------- *)
(* From the start to join1: the norm check passes, then mu is copied from m  *)
(* (ext nonzero, the 4 chunks of the 64 bytes at m) or computed (ext zero):  *)
(* tr, the first 64 bytes of SHAKE256(pk), by mld_H44, then mu by mld_H44 of *)
(* tr, pre and m, and the zeroing of tr.                                     *)
(* ------------------------------------------------------------------------- *)

let VI44_MU_OF_CHUNKS_TAC a s =
  MP_TAC(SPECL [a; `M:num`; `4`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC];;

let VI44_COPY_TAC b =
  ARM_STEPS_TAC VI44_EXEC [47;48] THEN
  VERIF_PC_TAC [VI44_EXT0] THEN ARM_STEPS_TAC VI44_EXEC (49--54) THEN
  VI44_MU_OF_CHUNKS_TAC (VI44_SP(b + 24320)) `s54:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

let VI44_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 1312)`;;

(*** The empty input of mld_H44 (NULL, length 0): its bytes are 0, and it    ***)
(*** does not overlap the stack of the call                                 ***)

let VI44_NULL_TAC s =
  SUBGOAL_THEN
   (subst [s,`s:armstate`] `read (memory :> bytes(word 0,0)) s = 0`)
   ASSUME_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64)
      (val(word_add stackpointer (word 4496):int64),608) (0,0)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[]; ALL_TAC];;

(*** tr, the first 64 bytes of SHAKE256 of the public key ***)

let VI44_TRNUM =
  subst [VI44_PKNUM,`p:num`]
   `num_of_bytelist (list_of_seq (mld_shake256_byte 1312 p) 64)`;;

let VI44_HASH_TAC b =
  ARM_STEPS_TAC VI44_EXEC [47;48] THEN VERIF_PC_TAC [VI44_EXT0] THEN
  ARM_STEPS_TAC VI44_EXEC (49--57) THEN
  MP_TAC(SPECL [`pk:int64`; `1312`; `pkb:num->byte`; `s57:armstate`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  VI44_NULL_TAC `s57:armstate` THEN
  VI44_CALL_TAC "H_H44"
   [`read X0 s`; `64`; `read X2 s`; `1312`; `read X4 s`; `0`; `read X6 s`;
    `0`; VI44_PKNUM; `0`; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 58 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VI44_H1]) THEN
  ARM_STEPS_TAC VI44_EXEC (59--67) THEN
  VI44_CALL_TAC "H_H44"
   [`read X0 s`; `64`; `read X2 s`; `64`; `read X4 s`; `prelen:num`;
    `read X6 s`; `mlen:num`; VI44_TRNUM; `PRE':num`; `M:num`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 68 THEN
  ARM_STEPS_TAC VI44_EXEC (69--71) THEN
  VI44_CALL_TAC "H_ZERO"
   [`read X0 s`; `64`; `pc:num`; `read SP s`; `read X30 s`] 72 THEN
  REWRITE_TAC[mld_verify_mu] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2 EXP (8 * 64)` (concl th)
    then REWRITE_RULE[ARITH_RULE `8 * 64 = 512`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* From join1 to the loop: the NTT of z, the expansion of the matrix from    *)
(* rho (32 bytes of pk), the challenge from c~ (its 2 chunks) and its NTT.   *)
(* ------------------------------------------------------------------------- *)

let VI44_MID_TAC b =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC VI44_EXEC (1--2) THEN
  VI44_CALL_TAC "H_VNTT"
   [`read X0 s`; VI44_Z; `pc:num`; `read SP s`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC VI44_EXEC (4--7) THEN
  MP_TAC(SPECL [`pk:int64`; `32`; `pkb:num->byte`; `s7:armstate`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  VI44_CALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; VI44_RHO; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 8 THEN
  ARM_STEPS_TAC VI44_EXEC (9--12) THEN
  MP_TAC(SPECL [VI44_SP(b + 24416); `sigb:num->byte`; `2`; `s12:armstate`]
               VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  VI44_CALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; VI44_C; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 13 THEN
  ARM_STEPS_TAC VI44_EXEC (14--15) THEN
  VI44_CALL_TAC "H_NTT" [`read X0 s`; VI44_CP; `pc:num`; `read X30 s`] 16 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_H_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body for row i: the rows before i succeeded and i < 4            *)
(* (VERIF_ROWS), the calls for row i up to the unpacking of its hints, and   *)
(* then either the use of the hints and the packing of the row, or the exit  *)
(* to loop1_exit2 if the hints do not unpack. The events before the row are  *)
(* kept opaque as front after the rows already done.                         *)
(* ------------------------------------------------------------------------- *)

let VI44_ROWS_TAC =
  MP_TAC(BETA_RULE(SPECL [mk_abs(`i:num`,VI44_HOK_TM); `4`; `i:num`]
                         VERIF_ROWS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(lhand(concl th)) &&
    fst(dest_forall(lhand(concl th))) = `j:num`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

let VI44_I_ZX = `word_zx(word_zx(word i:int64):int32):int64 = word i`;;

let VI44_I1_ZX =
  `word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
   word(i + 1)`;;

let VI44_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  VERIF_GEN_TAIL_TAC false "front" THEN
  FULL_INIT_TAC THEN VI44_ROWS_TAC THEN
  SUBGOAL_THEN (mk_conj(VI44_I_ZX,VI44_I1_ZX)) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC VI44_EXEC (1--5) THEN VERIF_REG_RULE_TAC[ASSUME VI44_I_ZX] THEN
  VI44_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`;
    mk_comb(`mld_polyvec_matrix_expand 4`,VI44_RHO); VI44_ZHAT; `i:num`;
    `pc:num`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC VI44_EXEC (7--10) THEN VERIF_REG_RULE_TAC[ASSUME VI44_I_ZX] THEN
  VI44_BYTES_SLICE_TAC
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word(32 + 320 * i + j)))) s10 =
            (pkb:num->byte)(32 + 320 * i + j)` THEN
  VI44_LOOP_CALL_TAC "H_T1"
   [`read X0 s`; `read X1 s`; `\j. (pkb:num->byte)(32 + 320 * i + j)`;
    `i:num`; `pc:num`; `read X30 s`] 11 THEN
  ARM_STEPS_TAC VI44_EXEC (12--13) THEN
  VI44_LOOP_CALL_TAC "H_SHIFTL"
   [`read X0 s`; VI44_T1; `pc:num`; `read X30 s`] 14 THEN
  ARM_STEPS_TAC VI44_EXEC (15--16) THEN
  VI44_LOOP_CALL_TAC "H_NTT"
   [`read X0 s`; VI44_SHL; `pc:num`; `read X30 s`] 17 THEN
  ARM_STEPS_TAC VI44_EXEC (18--20) THEN
  VI44_LOOP_CALL_TAC "H_PWM"
   [`read X0 s`; `read X1 s`; VI44_NTT1; VI44_CPHAT; `pc:num`;
    `read X30 s`] 21 THEN
  ARM_STEPS_TAC VI44_EXEC (22--24) THEN
  VI44_LOOP_CALL_TAC "H_SUB"
   [`read X0 s`; `read X1 s`; VI44_ACC; VI44_PWM; `pc:num`;
    `read X30 s`] 25 THEN
  ARM_STEPS_TAC VI44_EXEC (26--27) THEN
  VI44_LOOP_CALL_TAC "H_RED"
   [`read X0 s`; VI44_SUB; `pc:num`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC VI44_EXEC (29--30) THEN
  VI44_LOOP_CALL_TAC "H_INV"
   [`read X0 s`; VI44_RED; `pc:num`; `read X30 s`] 31 THEN
  ARM_STEPS_TAC VI44_EXEC (32--33) THEN
  VI44_LOOP_CALL_TAC "H_CADDQ"
   [`read X0 s`; VI44_INVT; `pc:num`; `read X30 s`] 34 THEN
  ARM_STEPS_TAC VI44_EXEC (35--38) THEN
  VERIF_REG_RULE_TAC[ASSUME VI44_I_ZX] THEN
  VI44_BYTES_SLICE_TAC
   `!j. j < 84
        ==> read(memory :> bytes8(word_add sig (word(2336 + j)))) s38 =
            (sigb:num->byte)(2336 + j)` THEN
  VI44_LOOP_CALL_TAC "H_HINTS"
   [`read X0 s`; `read X1 s`; `\t. (sigb:num->byte)(2336 + t)`; `i:num`;
    `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC VI44_EXEC (40--41);;

let VI44_PC_OK_TAC =
  ASM_CASES_TAC `i + 1 < 4` THENL
   [SUBGOAL_THEN `~(i + 1 = 4)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i + 1 < 4`; ASSUME `~(i + 1 = 4)`];
    SUBGOAL_THEN `i + 1 = 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN VI44_HINTSOK_TM ASSUME_TAC THENL
     [VERIF_IMP_CASE_TAC `~(i + 1 < 4)`; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~(i + 1 < 4)`; ASSUME `i + 1 = 4`;
                ASSUME VI44_HINTSOK_TM]];;

let VI44_JOIN_W1_TAC =
  DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[MATCH_MP (SPEC_ALL VERIF_W1B_ROW_88) (ASSUME `k < 192`)] THEN
      REWRITE_TAC[mld_verify_w1] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      FIRST_ASSUM(fun th ->
        MATCH_MP_TAC(REWRITE_RULE[GSYM ADD_ASSOC] th)) THEN
      FIRST_ASSUM ACCEPT_TAC]];;

let VI44_BODY_OK_TAC =
  VERIF_MP_CASE_TAC VI44_HOK_TM THEN
  ARM_STEPS_TAC VI44_EXEC (42--44) THEN
  VI44_LOOP_CALL_TAC "H_USEHINT"
   [`read X0 s`; `read X1 s`; VI44_CADDQ; VI44_HINTS; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC VI44_EXEC (46--49) THEN
  VERIF_REG_RULE_TAC[ASSUME VI44_I1_ZX] THEN
  VI44_LOOP_CALL_TAC "H_W1PACK"
   [`read X0 s`; `read X1 s`; VI44_UH; `pc:num`; `read X30 s`] 50 THEN
  ARM_STEPS_TAC VI44_EXEC (51--53) THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN W32_LOOP_TEST_TAC THEN
  CONJ_TAC THENL [VI44_PC_OK_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [VI44_JOIN_W1_TAC; ALL_TAC] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI44_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg VI44_HOK_TM) THEN VERIF_FINAL_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg VI44_HOK_TM)];
    ALL_TAC] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI44_BODY_TAC =
  VI44_BODY1_TAC THEN
  ASM_CASES_TAC VI44_HOK_TM THEN VERIF_PC_TAC [VI44_HOK_TM] THENL
   [VI44_BODY_OK_TAC; VI44_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop, if all hints unpack: c2 = the first 32 bytes of           *)
(* SHAKE256(mu || w1') by mld_H44, then the comparison of c~ and c2 by       *)
(* mld_ct_memcmp_1, which returns 0 iff they are equal, iff the signature is *)
(* accepted.                                                                 *)
(* ------------------------------------------------------------------------- *)

let VI44_C2NUM =
  subst [VI44_MU,`mu:num`; VI44_W1NUM,`w:num`]
   `num_of_bytelist (list_of_seq (mld_shake256_byte 832 (mu + 2 EXP 512 * w))
                      32)`;;

let VI44_OK_EQ_TAC =
  SUBGOAL_THEN (mk_eq(mk_eq(VI44_C,VI44_C2NUM),VI44_OK_TM)) ASSUME_TAC THENL
   [REWRITE_TAC[VI44_OK_THM; ASSUME VI44_NORMOK_TM;
                EQT_INTRO(ASSUME VI44_HINTSOK_TM); MLD_NUM_BYTELIST_EQ];
    ALL_TAC];;

(*** The simulation evaluates 2 EXP 512 in the conditional PC, so the     ***)
(*** equivalence and the case are rewritten in that form                 ***)

let VI44_NRM = CONV_RULE(DEPTH_CONV NUM_EXP_CONV);;

let VI44_CMP_PC_TAC =
  W(fun (asl,w) ->
    let eqv = VI44_NRM(snd(find (fun (_,th) ->
      concl th = mk_eq(mk_eq(VI44_C,VI44_C2NUM),VI44_OK_TM)) asl)) in
    let case =
      try EQT_INTRO(VI44_NRM(snd(find (fun (_,th) ->
            concl th = VI44_OK_TM) asl)))
      with Failure _ ->
        EQF_INTRO(VI44_NRM(snd(find (fun (_,th) ->
            concl th = mk_neg VI44_OK_TM) asl))) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`)
             (concl th)
      then REWRITE_RULE[]
            (CONV_RULE(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)
              (REWRITE_RULE[eqv; case] th))
      else th));;

let VI44_W1_BYTES_TAC b s =
  MP_TAC(SPECL [VI44_SP(b + 23552); `768`; VI44_W1B; s]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_88`)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC];;

let VI44_POST_OK_TAC b =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC VI44_EXEC (1--12) THEN
  VI44_W1_BYTES_TAC b `s12:armstate` THEN
  VI44_NULL_TAC `s12:armstate` THEN
  VI44_POST_CALL_TAC "H_H44"
   [`read X0 s`; `32`; `read X2 s`; `64`; `read X4 s`; `768`; `read X6 s`;
    `0`; VI44_MU; VI44_W1NUM; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 13 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VI44_H3]) THEN
  ARM_STEPS_TAC VI44_EXEC (14--17) THEN
  MP_TAC(SPECL [VI44_SP(b + 24416); `sigb:num->byte`; `2`; `s17:armstate`]
               VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  VI44_POST_CALL_TAC "H_CMP"
   [`read X0 s`; `read X1 s`; `32`; VI44_C; VI44_C2NUM; `pc:num`;
    `read X30 s`] 18 THEN
  ARM_STEPS_TAC VI44_EXEC (19--20) THEN
  VI44_OK_EQ_TAC THEN
  ASM_CASES_TAC VI44_OK_TM THEN VI44_CMP_PC_TAC THENL
   [VI44_CLEANUP_TAC VI44_ALLOWED_OLD 20;
    ARM_STEPS_TAC VI44_EXEC [21] THEN
    VI44_CLEANUP_TAC VI44_ALLOWED_OLD 21] THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(*** If some hints do not unpack: the result -6 and the cleanup ***)

let VI44_POST_HF_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC VI44_EXEC [1] THEN
  VI44_CLEANUP_TAC VI44_ALLOWED_OLD 1 THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0; VI44_OK_THM] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

let VI44_POST_TAC b =
  VERIF_GEN_TAIL_TAC true "old" THEN
  ASM_CASES_TAC VI44_HINTSOK_TM THENL
   [REWRITE_TAC[EQT_INTRO(ASSUME VI44_HINTSOK_TM); ARITH_RULE `0 < 4`] THEN
    VI44_POST_OK_TAC b;
    REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg VI44_HINTSOK_TM))] THEN
    VI44_POST_HF_TAC];;

(* ------------------------------------------------------------------------- *)
(* Each case of the alignment of the stack, with the buffers at              *)
(* stackpointer + b, and of the norm check.                                  *)
(* ------------------------------------------------------------------------- *)

let VI44_CASE_TAC b =
  ASM_CASES_TAC VI44_NORMOK_TM THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term VI44_K)
     `pc + mldsa44_verify_internal_loop1` VI44_PC2 (VI44_INV b) THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                  CONJUNCT1 LT; LT_REFL] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa44_verify_internal_join1`
       (VI44_JOIN1 b) THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC VI44_EXT0 THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th])
        THENL
         [VI44_PROLOGUE_TAC ALL_TAC THEN VI44_HASH_TAC b;
          VI44_PROLOGUE_TAC VI44_M_CHUNKS_TAC THEN VI44_COPY_TAC b];
        VI44_MID_TAC b];
      VI44_BODY_TAC;
      VI44_POST_TAC b];
    VI44_NF_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    MAP_EVERY (fun (fth,name) ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC
        (MATCH_MP fth (MATCH_MP MEMSET_RET_FULL_CONTRACT th)) name)
     [VI44_MEXP_FULL,"H_MEXP";
      MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_CHAL";
      MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_H44";
      MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_FULL,"H_ZERO"]) THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_FULL
               th) "H_HINTS") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_UNPACK_Z_44_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_UNPACKZ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_CHKNORM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_VNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI44_ROW_FULL "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_T1" THEN
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
   MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_USEHINT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYW1_PACK_88_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_W1PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_CMP" THEN
  CONCRETIZE_F_EVENTS_TAC VI44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst VI44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 29728):int64)` THEN
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
    VI44_CASE_TAC 5248;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    VI44_CASE_TAC 5264]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
