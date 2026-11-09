(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the proof (see verify_internal_44_spec.ml).  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/verify_internal_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

let VI44_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_EXEC;;

let VI44_MEXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL;;

let VI44_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The template of the events. The f_events arguments are ARGS below. The    *)
(* events split on the alignment of the stack (the buffers are at            *)
(* stackpointer + 5216 or + 5200), on the norm check of z (nf: the whole run *)
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

(*** The two SHAKE256 hashes, as the incremental calls give them ***)

let VI44_SQ_EQ = prove
 (`!x. mld_shake256_byte 832 x =
       mld_keccak_squeeze_byte 136
        (mld_keccak_finalize 136 31
          (FST(mld_keccak_absorb 136 (word 0) 0 832 x)) 16) 136`,
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; MLD_KECCAK_ABSORB_SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VI44_TR_EQ = prove
 (`!x. mld_shake256_byte 1312 x =
       mld_keccak_squeeze_byte 136
        (mld_keccak_finalize 136 31
          (FST(mld_keccak_absorb 136 (word 0) 0 1312 x)) 88) 136`,
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; MLD_KECCAK_ABSORB_SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Calls and the cleanup. The allowed variables of the events are the        *)
(* arguments of f_events, and in the loop body and after the loop the row    *)
(* index i and the generalized events so far (front, old). VI44_CLEANUP_TAC  *)
(* allowed n simulates the code from join2 (+0x29c) to the return from state *)
(* n: memset of the buffers through the PLT, the inline zeroing, the check   *)
(* of the canary and the restoring of the registers.                         *)
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
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc VI44_EXEC name ilist
   allowed n;;

let VI44_CALL_TAC = VI44_CALL_GEN_TAC VI44_ALLOWED;;
let VI44_LOOP_CALL_TAC = VI44_CALL_GEN_TAC VI44_ALLOWED_LOOP;;
let VI44_POST_CALL_TAC = VI44_CALL_GEN_TAC VI44_ALLOWED_OLD;;

let VI44_MEMSET_TAC allowed n =
  LIBC_PLT_TAC VI44_EXEC n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" VI44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref allowed) (n + 5);;

let VI44_CLEANUP_TAC allowed n =
  let ms = VI44_MEMSET_TAC allowed in
  VERIF_DROP_MEM_TAC (VERIF_KEEP_FRAME 5072 5192 29880) THEN
  ARM_STEPS_TAC VI44_EXEC ((n+1)--(n+4)) THEN ms (n+4) THEN
  ARM_STEPS_TAC VI44_EXEC ((n+10)--(n+13)) THEN ms (n+13) THEN
  ARM_STEPS_TAC VI44_EXEC ((n+19)--(n+22)) THEN ms (n+22) THEN
  ARM_STEPS_TAC VI44_EXEC ((n+28)--(n+31)) THEN ms (n+31) THEN
  ARM_STEPS_TAC VI44_EXEC ((n+37)--(n+40)) THEN ms (n+40) THEN
  ARM_STEPS_TAC VI44_EXEC ((n+46)--(n+57)) THEN ms (n+57) THEN
  ARM_STEPS_TAC VI44_EXEC [n+63] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI44_EXEC ((n+64)--(n+79));;

(*** Words of the stack frame ***)

let VI44_SP k =
  mk_comb(`word_add (stackpointer:int64)`,
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(* ------------------------------------------------------------------------- *)
(* The prologue, to the norm check: the chunks of c~ that the code copies,   *)
(* the bytes of z for mldsa44_polyvecl_unpack_z, and the bound of the norm   *)
(* check as the code passes it.                                              *)
(* ------------------------------------------------------------------------- *)

let VI44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5231 5216 5200;;

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
  ARM_STEPS_TAC VI44_EXEC (1--9) THEN MEXP_BUFFER_TAC VI44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC VI44_EXEC (10--20) THEN
  ARM_STEPS_TAC VI44_EXEC [21] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI44_EXEC (22--29) THEN
  VI44_BYTES_SLICE_TAC
   `!j. j < 2304
        ==> read(memory :> bytes8(word_add sig (word(32 + j)))) s29 =
            (sigb:num->byte)(32 + j)` THEN
  VI44_CALL_TAC "H_UNPACKZ"
   [`read X0 s`; `read X1 s`; `\j. (sigb:num->byte)(32 + j)`; `pc:num`;
    `read SP s`; `read X30 s`] 30 THEN
  ARM_STEPS_TAC VI44_EXEC (31--34) THEN
  VI44_CALL_TAC "H_CHKNORM"
   [`read X0 s`; VI44_Z; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 35 THEN
  VI44_BND_TAC THEN
  ARM_STEPS_TAC VI44_EXEC [36] THEN VERIF_PC_TAC [VI44_NORMOK_TM];;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: the setup of the result -6 and the cleanup.         *)
(* ------------------------------------------------------------------------- *)

let VI44_NF_TAC =
  VI44_PROLOGUE_TAC ALL_TAC THEN ARM_STEPS_TAC VI44_EXEC (37--52) THEN
  VI44_CLEANUP_TAC VI44_ALLOWED 52 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VI44_OK_THM] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join1 (+0xb4), where mu is ready, with the buffers at        *)
(* stackpointer + b: the matrix, z, tmp, w1, cp, buf (w1' packed), mu, c2    *)
(* and c at offsets 0, 16384, 20480, 21504, 22528, 23552, 24320, 24384 and   *)
(* 24416. The frame of the function is at stackpointer + 5072, with the      *)
(* saved registers, then the pointers pk, sig and pre (later c) at           *)
(* 5176..5192, the SHAKE256 context at 29672 and the canary at 29880.        *)
(* ------------------------------------------------------------------------- *)

let VI44_FRAME_FACTS =
  "read SP s = word_add stackpointer (word 5072) /\\
    read (memory :> bytes64 (word_add stackpointer (word 5072))) s =
      x19_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5080))) s =
      x20_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5088))) s =
      x21_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5096))) s =
      x22_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5104))) s =
      x23_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5112))) s =
      x24_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5120))) s =
      x25_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5128))) s =
      x26_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5136))) s =
      x27_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5144))) s =
      x28_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 5152))) s =
      returnaddress /\\
    read (memory :> bytes64 (word_add stackpointer (word 5176))) s = pk /\\
    read (memory :> bytes64 (word_add stackpointer (word 5184))) s = sig /\\
    read (memory :> bytes64 (word_add stackpointer (word 29880))) s =
      canary /\\
    read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
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
  let s = "\\s. " ^ VI44_FRAME_FACTS ^ " /\\
    read X21 s = word_add stackpointer (word " ^ n 0 ^ ") /\\
    read X22 s = word 0 /\\
    read X25 s = word_add stackpointer (word " ^ n 16384 ^ ") /\\
    read X27 s = word_add stackpointer (word " ^ n 24320 ^ ") /\\
    read X28 s = word_add stackpointer (word " ^ n 23552 ^ ") /\\
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
  let s = "\\i s. " ^ VI44_FRAME_FACTS ^ " /\\
    read X19 s = word_add stackpointer (word " ^ n 20480 ^ ") /\\
    read X20 s = word_add stackpointer (word " ^ n 21504 ^ ") /\\
    read X21 s = word_add stackpointer (word " ^ n 0 ^ ") /\\
    read X25 s = word_add stackpointer (word " ^ n 16384 ^ ") /\\
    read X26 s = word_add stackpointer (word " ^ n 22528 ^ ") /\\
    read X27 s = word_add stackpointer (word " ^ n 24320 ^ ") /\\
    read X28 s = word_add stackpointer (word " ^ n 23552 ^ ") /\\
    read (memory :> bytes64 (word_add stackpointer (word 5192))) s =
      word_add stackpointer (word " ^ n 24416 ^ ") /\\
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
     ==> read X22 s = word i /\\
         read X24 s =
           word_add stackpointer (word (" ^ n 23552 ^ " + 192 * i)) /\\
         (0 < i ==> read X23 s = word 0) /\\
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
(* tr = SHAKE256(pk) by the incremental functions, then mld_H44 of tr, pre   *)
(* and m.                                                                    *)
(* ------------------------------------------------------------------------- *)

let VI44_MU_OF_CHUNKS_TAC a s =
  MP_TAC(SPECL [a; `M:num`; `4`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC];;

let VI44_COPY_TAC b =
  ARM_STEPS_TAC VI44_EXEC [37;38] THEN
  VERIF_PC_TAC [VI44_EXT0] THEN ARM_STEPS_TAC VI44_EXEC (39--47) THEN
  VI44_MU_OF_CHUNKS_TAC (VI44_SP(b + 24320)) `s47:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

let VI44_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 1312)`;;

let VI44_S0 =
  subst [VI44_PKNUM,`p:num`]
   `FST(mld_keccak_absorb 136 (word 0) 0 1312 p)`;;

let VI44_HASH_TAC b =
  ARM_STEPS_TAC VI44_EXEC [37;38] THEN VERIF_PC_TAC [VI44_EXT0] THEN
  ARM_STEPS_TAC VI44_EXEC (39--44) THEN
  VI44_CALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 45 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC VI44_EXEC (46--49) THEN
  MP_TAC(SPECL [`pk:int64`; `1312`; `pkb:num->byte`; `s49:armstate`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  KECCAK_STATE_AT_TAC (VI44_SP 29672) THEN
  VI44_CALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `1312`; `word 0:1600 word`; `0`; VI44_PKNUM;
    `pc:num`; `read SP s`; `read X30 s`] 50 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `1312 MOD 136` (concl th)
    then REWRITE_RULE[ARITH_RULE `1312 MOD 136 = 88`] th else th) THEN
  ARM_STEPS_TAC VI44_EXEC (51--52) THEN
  KECCAK_STATE_AT_TAC (VI44_SP 29672) THEN MLD_H_GUARD_ADDR_TAC THEN
  VI44_CALL_TAC "H_FINALIZE"
   [`read X0 s`; VI44_S0; `88`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 53 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC VI44_EXEC (54--57) THEN
  KECCAK_STATE_AT_TAC (VI44_SP 29672) THEN
  VI44_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `64`; `read X2 s`;
    mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI44_S0),`88`);
    `136`; `pc:num`; `read SP s`; `read X30 s`] 58 THEN
  ARM_STEPS_TAC VI44_EXEC (59--60) THEN
  VI44_CALL_TAC "H_RELEASE" [`read X0 s`; `pc:num`; `read X30 s`] 61 THEN
  ARM_STEPS_TAC VI44_EXEC (62--80) THEN
  VI44_CALL_TAC "H_H44"
   [`read X0 s`; `64`; `read X2 s`; `64`; `read X4 s`; `prelen:num`;
    `read X6 s`; `mlen:num`;
    subst [mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI44_S0),`88`),
           `sf:1600 word`]
     `num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 sf 136) 64)`;
    `PRE':num`; `M:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 81 THEN
  ARM_STEPS_TAC VI44_EXEC (82--85) THEN
  REWRITE_TAC[mld_verify_mu; VI44_TR_EQ] THEN
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
  ARM_STEPS_TAC VI44_EXEC (1--10) THEN
  VI44_CALL_TAC "H_VNTT"
   [`read X0 s`; VI44_Z; `pc:num`; `read SP s`; `read X30 s`] 11 THEN
  ARM_STEPS_TAC VI44_EXEC (12--15) THEN
  MP_TAC(SPECL [`pk:int64`; `32`; `pkb:num->byte`; `s15:armstate`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  VI44_CALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; VI44_RHO; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC VI44_EXEC (17--19) THEN
  MP_TAC(SPECL [VI44_SP(b + 24416); `sigb:num->byte`; `2`; `s19:armstate`]
               VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  VI44_CALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; VI44_C; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 20 THEN
  ARM_STEPS_TAC VI44_EXEC (21--23) THEN
  VI44_CALL_TAC "H_NTT" [`read X0 s`; VI44_CP; `pc:num`; `read X30 s`] 24 THEN
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
   [`read X0 s`; `read X1 s`; VI44_CADDQ; VI44_HINTS; `pc:num`;
    `read X30 s`] 45 THEN
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
(* After the loop, if all hints unpack: c2 = SHAKE256(mu || w1', 32) by the  *)
(* incremental functions, whose two absorbs are one of the concatenation,    *)
(* then the vectorized compare of the 2 chunks of c~ and c2, whose branch is *)
(* taken iff the OR of the differences is nonzero (proved by bit-blasting    *)
(* over the OR and XOR folds, once), iff the signature is not accepted.      *)
(* ------------------------------------------------------------------------- *)

let VI44_S1 =
  subst [VI44_MU,`mu:num`; VI44_W1NUM,`w:num`]
   `FST(mld_keccak_absorb 136 (word 0) 0 832 (mu + 2 EXP 512 * w))`;;

let VI44_SQ =
  subst [VI44_S1,`s1:1600 word`]
   `mld_keccak_squeeze_byte 136 (mld_keccak_finalize 136 31 s1 16) 136`;;

let VI44_ABSORB_APPEND_TAC b =
  MLD_H_BOUND_TAC (VI44_SP(b + 24320)) THEN
  FIRST_ASSUM(fun bth ->
    if concl bth <> subst [VI44_MU,`mu:num`] `mu < 2 EXP (8 * 64)`
    then NO_TAC else
    let th = MP (SPECL [`64`; `768`; VI44_MU; VI44_W1NUM]
                       MLD_SHAKE256_ABSORB_APPEND) bth in
    let th' = REWRITE_RULE[ARITH_RULE `64 MOD 136 = 64`;
                           ARITH_RULE `8 * 64 = 512`;
                           ARITH_RULE `64 + 768 = 832`] th in
    RULE_ASSUM_TAC(fun ath ->
      if can (find_term ((=) `mld_keccak_absorb`)) (concl ath) ||
         free_in `(64 + 768) MOD 136` (concl ath)
      then REWRITE_RULE[th'; ARITH_RULE `(64 + 768) MOD 136 = 16`] ath
      else ath));;

let VI44_C2_CHUNKS_TAC a s =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> bytes(x,32)) s = n`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [a; `32`; VI44_SQ; s; mk_small_numeral i]
                 BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    DISCH_TAC) [0;1];;

(*** Name the chunks compared, so that the simulation keeps them opaque ***)

let VI44_CHUNK_VARS = ["cc0";"cc1";"dd0";"dd1"];;

let VI44_CHUNK_ABBREV_TAC =
  let mk n i f = (mk_var(n ^ string_of_int i,`:int128`),
                  mk_comb(mk_comb(`mld_chunk128`,f),mk_small_numeral i)) in
  let abbs = map (fun i -> mk "cc" i `sigb:num->byte`) [0;1] @
             map (fun i -> mk "dd" i VI44_SQ) [0;1] in
  MAP_EVERY (fun (v,t) ->
    ABBREV_TAC (mk_eq(v,t)) THEN
    FIRST_ASSUM(fun eth ->
      if concl eth <> mk_eq(t,v) then NO_TAC else
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if is_eq c && rhs c = t &&
           can (term_match [] `read (memory :> bytes128 a) s = x:int128`) c
        then TRANS th eth else th))) abbs;;

let VI44_OR_FOLD = `(dd1 ^^ cc1) || (dd0 ^^ cc0):int128`;;

let VI44_XOR_FOLD =
  `(dd1 ^^ cc1) ^^ (dd0 ^^ cc0):int128`;;

let VI44_CMP_MEMO = ref ([]:(term * thm) list);;

let VI44_CMP_REDUCE_TAC s =
  W(fun (asl,w) ->
    let pcth = snd(find (fun (_,th) ->
      can (term_match [] (subst [s,`s:armstate`] `read PC s = x:int64`))
          (concl th)) asl) in
    let c = rand(rator(rator(rhs(concl pcth)))) in
    let c' = subst [`vv:int128`,VI44_OR_FOLD; `ww:int128`,VI44_XOR_FOLD] c in
    let tm = mk_forall(`vv:int128`,mk_forall(`ww:int128`,
               mk_eq(c',`~(vv = word 0:int128)`))) in
    let lem = try assoc tm (!VI44_CMP_MEMO) with Failure _ ->
      let th = BITBLAST_RULE tm in
      (VI44_CMP_MEMO := (tm,th)::(!VI44_CMP_MEMO); th) in
    ASSUME_TAC(SPECL [VI44_OR_FOLD; VI44_XOR_FOLD] lem));;

let VI44_OK_EQ_TAC =
  SUBGOAL_THEN (mk_eq(mk_eq(VI44_OR_FOLD,`word 0:int128`),VI44_OK_TM))
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
    W(fun (asl,w) -> REWRITE_TAC(mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_var(rhs c) && mem (fst(dest_var(rhs c))) VI44_CHUNK_VARS
      then SYM th else fail()) asl)) THEN
    REWRITE_TAC[VI44_OK_THM; ASSUME VI44_NORMOK_TM;
                EQT_INTRO(ASSUME VI44_HINTSOK_TM)] THEN
    REWRITE_TAC[VI44_SQ_EQ] THEN
    MP_TAC(ISPECL [`sigb:num->byte`; VI44_SQ; `2`] MLD_CHUNK128_EQ) THEN
    CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
    REWRITE_TAC[ARITH_RULE `16 * 2 = 32`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[];
    ALL_TAC];;

let VI44_CMP_PC_TAC =
  W(fun (asl,w) ->
    let z = mk_eq(VI44_OR_FOLD,`word 0:int128`) in
    let red = snd(find (fun (_,th) -> let c = concl th in
      is_eq c && type_of(lhs c) = bool_ty && rhs c = mk_neg z) asl) in
    let eqv = snd(find (fun (_,th) -> concl th = mk_eq(z,VI44_OK_TM)) asl) in
    let case =
      try EQT_INTRO(snd(find (fun (_,th) -> concl th = VI44_OK_TM) asl))
      with Failure _ ->
        EQF_INTRO(snd(find (fun (_,th) -> concl th = mk_neg VI44_OK_TM) asl)) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`)
             (concl th)
      then REWRITE_RULE[red; eqv; case] th else th));;

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
  ARM_STEPS_TAC VI44_EXEC (1--6) THEN
  VI44_POST_CALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC VI44_EXEC (8--11) THEN
  KECCAK_STATE_AT_TAC (VI44_SP 29672) THEN
  VI44_POST_CALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `64`; `word 0:1600 word`; `0`; VI44_MU;
    `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `64 MOD 136` (concl th)
    then REWRITE_RULE[ARITH_RULE `64 MOD 136 = 64`] th else th) THEN
  ARM_STEPS_TAC VI44_EXEC (13--16) THEN
  VI44_W1_BYTES_TAC b `s16:armstate` THEN
  KECCAK_STATE_AT_TAC (VI44_SP 29672) THEN
  VI44_POST_CALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `768`;
    mk_comb(`FST:1600 word#num->1600 word`,
     list_mk_comb(`mld_keccak_absorb`,
      [`136`; `word 0:1600 word`; `0`; `64`; VI44_MU]));
    `64`; VI44_W1NUM; `pc:num`; `read SP s`; `read X30 s`] 17 THEN
  VI44_ABSORB_APPEND_TAC b THEN
  ARM_STEPS_TAC VI44_EXEC (18--19) THEN
  KECCAK_STATE_AT_TAC (VI44_SP 29672) THEN MLD_H_GUARD_ADDR_TAC THEN
  VI44_POST_CALL_TAC "H_FINALIZE"
   [`read X0 s`; VI44_S1; `16`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 20 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC VI44_EXEC (21--24) THEN
  KECCAK_STATE_AT_TAC (VI44_SP 29672) THEN
  VI44_POST_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `32`; `read X2 s`;
    mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI44_S1),`16`);
    `136`; `pc:num`; `read SP s`; `read X30 s`] 25 THEN
  ARM_STEPS_TAC VI44_EXEC (26--27) THEN
  VI44_POST_CALL_TAC "H_RELEASE" [`read X0 s`; `pc:num`; `read X30 s`] 28 THEN
  VI44_C2_CHUNKS_TAC (VI44_SP(b + 24384)) `s28:armstate` THEN
  VI44_CHUNK_ABBREV_TAC THEN
  ARM_STEPS_TAC VI44_EXEC (29--67) THEN
  VI44_CMP_REDUCE_TAC `s67:armstate` THEN VI44_OK_EQ_TAC THEN
  ASM_CASES_TAC VI44_OK_TM THEN VI44_CMP_PC_TAC THENL
   [VI44_CLEANUP_TAC VI44_ALLOWED_OLD 67;
    ARM_STEPS_TAC VI44_EXEC (68--69) THEN
    VI44_CLEANUP_TAC VI44_ALLOWED_OLD 69] THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(*** If some hints do not unpack: the result -6 and the cleanup ***)

let VI44_POST_HF_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC VI44_EXEC (1--4) THEN
  VI44_CLEANUP_TAC VI44_ALLOWED_OLD 4 THEN
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

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP VI44_MEXP_FULL (MATCH_MP MEMSET_RET_FULL_CONTRACT th))
     "H_MEXP") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
               (MATCH_MP MEMSET_RET_FULL_CONTRACT th)) "H_CHAL") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
               th) "H_HINTS") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_ret_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_UNPACK_Z_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_UNPACKZ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_CHKNORM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_VNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI44_ROW_FULL "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_SHIFTL_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHIFTL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_PWM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_USEHINT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_W1PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_H44" THEN
  CONCRETIZE_F_EVENTS_TAC VI44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst VI44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 29888):int64)` THEN
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
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    VI44_CASE_TAC 5216;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    VI44_CASE_TAC 5200]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
