(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the proof (see verify_internal_65_spec.ml).  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_eq_spec.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

let VI65_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_EXEC;;

let VI65_MEXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let VI65_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The template of the events. The f_events arguments are ARGS below. The    *)
(* events split on the norm check of z (nf: the whole run when it fails), on *)
(* ext (hash or copy: from the start to join1, where mu is ready), mid (from *)
(* join1 to the loop over the rows), the rows (row: one whose hints unpack,  *)
(* rowf: the first one whose hints do not, after which the loop stops), and  *)
(* the end after the loop: hf when some hints do not unpack, and acc or rej  *)
(* after the hash and the compare of c~ otherwise. The number of rows done   *)
(* is K: 6, or the first failing row plus 1. The code aligns its frame to 32 *)
(* bytes, so that the addresses in it are at fixed offsets from bot          *)
(* (utils/mldsa_native_realign.ml), a function of stackpointer, as the       *)
(* events are once bot is expanded.                                          *)
(* ------------------------------------------------------------------------- *)

let VI65_ARGS =
  "sig m mlen pre prelen pk ext sigb pkb M PRE pc stackpointer " ^
  "returnaddress";;

let VI65_LAMBDA =
  "\\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (pk:int64) " ^
  "(ext:int64) (sigb:num->byte) (pkb:num->byte) (M:num) PRE " ^
  "(pc:num) (stackpointer:int64) (returnaddress:int64).";;

let VI65_HOK = "mld_unpack_hints_ret 55 6 (\\t. sigb(3248 + t)) i = word 0";;

let VI65_HINTSOK = "(!i. i < 6 ==> " ^ VI65_HOK ^ ")";;

let VI65_K =
  "(if " ^ VI65_HINTSOK ^ " then 6 else (minimal i. ~(" ^ VI65_HOK ^
  ")) + 1)";;

let VI65_NORMOK =
  "mld_polyvec_chknorm 5 (mld_polyvec_unpack 640 mld_polyz_unpack_19 " ^
  "(\\j. sigb(48 + j))) (word 524092) = word 0";;

let VI65_OK =
  "mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092 " ^
  "mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 sigb pkb " ^
  "(if word_zx ext = (word 0:int32) " ^
  "then mld_verify_mu 1952 pkb prelen PRE mlen M else M MOD 2 EXP 512)";;

let VI65_TEMPLATE_CASE =
  let f n = "(f_ev_" ^ n ^ " " ^ VI65_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ " " ^ VI65_ARGS ^ " i)" in
  "(if " ^ VI65_NORMOK ^ " then " ^
  "APPEND (if " ^ VI65_HINTSOK ^ " then (if " ^ VI65_OK ^ " then " ^
  f "acc" ^ " else " ^ f "rej" ^ ") else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ VI65_K ^ " (\\i. if " ^ VI65_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if word_zx ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ")";;

let VI65_TEMPLATE =
  parse_term(VI65_LAMBDA ^ " " ^ VI65_TEMPLATE_CASE ^ " :(uarch_event)list");;

(* ------------------------------------------------------------------------- *)
(* The same conditions in the proof, where the variable for PRE is PRE' (PRE *)
(* is also the predecessor function), and the values the code computes: mu,  *)
(* the vectors z and zhat, c, rho, and row i of w1' (the use of the hints on *)
(* caddq(invntt(reduce(A z - c t1 2^d))), with row i of A z as the default   *)
(* configuration computes it), and its packing W1B.                          *)
(* ------------------------------------------------------------------------- *)

let VI65_HOK_TM = parse_term VI65_HOK;;
let VI65_HINTSOK_TM = parse_term VI65_HINTSOK;;
let VI65_NORMOK_TM = parse_term VI65_NORMOK;;
let VI65_EXT0 = `word_zx (ext:int64) = (word 0:int32)`;;

let VI65_MU =
  `if word_zx (ext:int64) = (word 0:int32)
   then mld_verify_mu 1952 pkb prelen PRE' mlen M else M MOD 2 EXP 512`;;

let VI65_OK_TM =
  subst [VI65_MU,`mu:num`]
   `mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
     mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 (sigb:num->byte)
     (pkb:num->byte) mu`;;

let VI65_RHO = `num_of_bytelist (list_of_seq (pkb:num->byte) 32)`;;

let VI65_Z =
  `mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. (sigb:num->byte)(48 + j))`;;

let VI65_ZHAT = mk_comb(`mld_polyvec_map mld_poly_ntt`,VI65_Z);;

let VI65_C = `num_of_bytelist (list_of_seq (sigb:num->byte) 48)`;;

let VI65_CP = mk_comb(`mld_poly_challenge 49 48`,VI65_C);;

let VI65_CPHAT = mk_comb(`mld_poly_ntt`,VI65_CP);;

let VI65_ACC =
  subst [VI65_RHO,`rho:num`; VI65_ZHAT,`zhat:num->int32`]
   `mld_polyvec_pointwise_acc_montgomery 5
     (\j. mld_polyvec_matrix_expand 5 rho (1280 * i + j)) zhat`;;

let VI65_T1 = `mld_polyt1_unpack (\j. (pkb:num->byte) (32 + 320 * i + j))`;;
let VI65_SHL = mk_comb(`mld_poly_shiftl`,VI65_T1);;
let VI65_NTT1 = mk_comb(`mld_poly_ntt`,VI65_SHL);;
let VI65_PWM =
  list_mk_comb(`mld_poly_pointwise_montgomery`,[VI65_NTT1;VI65_CPHAT]);;
let VI65_SUB = list_mk_comb(`mld_poly_sub`,[VI65_ACC;VI65_PWM]);;
let VI65_RED = mk_comb(`mld_poly_reduce`,VI65_SUB);;
let VI65_INVT = mk_comb(`mld_poly_invntt_tomont`,VI65_RED);;
let VI65_CADDQ = mk_comb(`mld_poly_caddq`,VI65_INVT);;
let VI65_HINTS = `mld_unpack_hints 55 (\t. (sigb:num->byte) (3248 + t)) i`;;
let VI65_UH = list_mk_comb(`mld_poly_use_hint_32`,[VI65_CADDQ;VI65_HINTS]);;

(*** Row i as the code computes it, with the lazy product of the row       ***)
(*** (mld_polyvec_matrix_row_lazy), whose result made nonnegative is that  ***)
(*** of the specification (MLD_LAZY_VERIFY)                                ***)

let VI65_ROWL =
  subst [VI65_RHO,`rho:num`; VI65_ZHAT,`zhat:num->int32`]
   `mld_polyvec_matrix_row_lazy 5 rho zhat i`;;
let VI65_SUBL = list_mk_comb(`mld_poly_sub`,[VI65_ROWL;VI65_PWM]);;
let VI65_REDL = mk_comb(`mld_poly_reduce`,VI65_SUBL);;
let VI65_INVTL = mk_comb(`mld_poly_invntt_tomont`,VI65_REDL);;
let VI65_CADDQL = mk_comb(`mld_poly_caddq`,VI65_INVTL);;

let VI65_ZHAT_BOUND =
  subst [VI65_ZHAT,`zhat:num->int32`]
   `!j. j < 1280 ==> abs(ival((zhat:num->int32) j)) < &94279689`;;

let VI65_ZHAT_BOUND_TAC =
  SUBGOAL_THEN VI65_ZHAT_BOUND ASSUME_TAC THENL
   [MP_TAC(SPECL [`5`; VI65_Z] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_Z_UNPACK_BOUND];
    ALL_TAC];;

let VI65_CADDQ_TAC =
  FIRST_ASSUM(fun th ->
    if not(is_forall(concl th)) ||
       not(can (find_term ((=) VI65_CADDQL)) (concl th))
    then failwith "VI65_CADDQ_TAC" else
    SUBGOAL_THEN (subst [VI65_CADDQ,VI65_CADDQL] (concl th)) ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun nth -> REWRITE_TAC[MP (SPEC `n:num` th) nth] THEN
                            ASSUME_TAC nth) THEN
      MP_TAC(SPECL [`6`; `5`; VI65_RHO; VI65_ZHAT; VI65_PWM; `i:num`; `n:num`]
                   MLD_LAZY_VERIFY) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MLD_LAZY_POINTWISE_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[]];
      ALL_TAC]);;

let VI65_W1B =
  subst [VI65_RHO,`rho:num`; VI65_ZHAT,`zhat:num->int32`;
         VI65_CPHAT,`cphat:num->int32`]
   `mld_polyvec_pack 128 mld_polyw1_pack_32
     (mld_polyvec
       (mld_verify_w1 5 mld_poly_use_hint_32 rho zhat cphat pkb 55
         (\t. (sigb:num->byte) (3248 + t))))`;;

let VI65_W1NUM =
  mk_comb(`num_of_bytelist`,
          mk_comb(mk_comb(`list_of_seq:(num->byte)->num->byte list`,VI65_W1B),
                  `768`));;

(*** mld_verify_internal_ok for the parameters of ML-DSA-65 ***)

let VI65_OK_THM = GEN_ALL(prove
 (subst [VI65_W1B,`w1b:num->byte`]
  `mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
       mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 (sigb:num->byte)
       (pkb:num->byte) mu <=>
     mld_polyvec_chknorm 5
       (mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(48 + j)))
       (word 524092) = word 0 /\
     (!i. i < 6
          ==> mld_unpack_hints_ret 55 6 (\t. sigb(3248 + t)) i = word 0) /\
     (!j. j < 48
          ==> sigb j =
              mld_shake256_byte 832
               (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b 768)) j)`,
  REWRITE_TAC[mld_verify_internal_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `48 + 5 * 640 + t = 3248 + t`;
              ARITH_RULE `64 + 6 * 128 = 832`; ARITH_RULE `6 * 128 = 768`]));;

(*** The two SHAKE256 hashes, as the incremental calls give them ***)

let VI65_SQ_EQ = prove
 (`!x. mld_shake256_byte 832 x =
       mld_keccak_squeeze_byte 136
        (mld_keccak_finalize 136 31
          (FST(mld_keccak_absorb 136 (word 0) 0 832 x)) 16) 136`,
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state;
              MLD_KECCAK_ABSORB_SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VI65_TR_EQ = prove
 (`!x. mld_shake256_byte 1952 x =
       mld_keccak_squeeze_byte 136
        (mld_keccak_finalize 136 31
          (FST(mld_keccak_absorb 136 (word 0) 0 1952 x)) 48) 136`,
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state;
              MLD_KECCAK_ABSORB_SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Calls and the cleanup. The allowed variables of the events are the        *)
(* arguments of f_events and bot, which REALIGN_UNBOT_TAC expands at the end *)
(* of each part, and in the loop body and after the loop the row index i and *)
(* the generalized events so far (front, old). VI65_CLEANUP_TAC allowed n    *)
(* simulates the code from join2 to the return from state n: the inline      *)
(* zeroing of the buffers (REP STOSQ, including the structure of the matrix, *)
(* and 128-bit stores), the restoring of the registers and of RSP from R10.  *)
(* ------------------------------------------------------------------------- *)

let VI65_ALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `pk:int64`; `ext:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
   `PRE':num`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let VI65_ALLOWED_LOOP =
  `front:(uarch_event)list`::`i:num`::VI65_ALLOWED;;

let VI65_ALLOWED_OLD = `old:(uarch_event)list`::VI65_ALLOWED;;

let VI65_CALL_GEN_TAC allowed name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc VI65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   allowed n;;

let VI65_CALL_TAC = VI65_CALL_GEN_TAC VI65_ALLOWED;;
let VI65_LOOP_CALL_TAC = VI65_CALL_GEN_TAC VI65_ALLOWED_LOOP;;
let VI65_POST_CALL_TAC = VI65_CALL_GEN_TAC VI65_ALLOWED_OLD;;

let VI65_CLEANUP_TAC (allowed:term list) n =
  VERIF_DROP_MEM_TAC (VERIF_KEEP_FRAME 1678 12230) THEN
  X86_STEPS_TAC VI65_EXEC ((n+1)--(n+46));;

(* ------------------------------------------------------------------------- *)
(* The prologue, to the norm check: the realigned frame (with RBP at bot +   *)
(* 12222), the chunks of c~ that the code copies, the 32-bit argument ext    *)
(* from its slot on the stack, the bytes of z for mldsa65_polyvecl_unpack_z, *)
(* and the bound of the norm check as the code passes it.                    *)
(* ------------------------------------------------------------------------- *)

let VI65_SIG_CHUNKS_TAC =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `3309`; `sigb:num->byte`; `s0:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1;2];;

let VI65_EXT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add stackpointer (word 12277))) s =
          (ext:int64)`) (concl th)
    then ASSUME_TAC(MATCH_MP VERIF_BYTES32_OF_BYTES64 th) else NO_TAC);;

let VI65_BND_TAC =
  let tm = `word_zx (word 524092:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let VI65_PROLOGUE_TAC pretac =
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
  FULL_INIT_TAC THEN pretac THEN VI65_SIG_CHUNKS_TAC THEN
  X86_STEPS_TAC VI65_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC VI65_EXEC (3--25) THEN VI65_EXT_TAC THEN
  X86_STEPS_TAC VI65_EXEC (26--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VERIF_SLICE_TAC
   `!j. j < 3200
        ==> read(memory :> bytes8(word_add sig (word(48 + j)))) s31 =
            (sigb:num->byte)(48 + j)` THEN
  VI65_CALL_TAC "H_UNPACKZ"
   [`read RDI s`; `read RSI s`; `\j. (sigb:num->byte)(48 + j)`] 32 THEN
  X86_STEPS_TAC VI65_EXEC (33--35) THEN
  VI65_CALL_TAC "H_CHKNORM" [`read RDI s`; VI65_Z; `read RSI s`] 36 THEN
  VI65_BND_TAC THEN
  X86_STEPS_TAC VI65_EXEC (37--39) THEN VERIF_PC_TAC [VI65_NORMOK_TM];;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: the setup of the pointers and of the result -6, and *)
(* the cleanup.                                                              *)
(* ------------------------------------------------------------------------- *)

let VI65_NF_TAC =
  VI65_PROLOGUE_TAC ALL_TAC THEN X86_STEPS_TAC VI65_EXEC (40--54) THEN
  VI65_CLEANUP_TAC VI65_ALLOWED 54 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VI65_OK_THM] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join1, where mu is ready, and at the head of the loop for    *)
(* row i, with the frame at fixed offsets from bot: RBP at bot + 12222, the  *)
(* copy of the return address and the saved registers (with R10, the entry   *)
(* RSP + 8) above it, and below it z, the structure of the matrix (rho at    *)
(* offset 1024 in it), the rows of w1 (and tr), tmp, cp, w1' packed, the     *)
(* context of the hash of c2, mu, c2 and c~ at offsets 7054, 5998, 4974,     *)
(* 3950, 2926, 2158, 1950, 1870, 1806 and 1742, and the pointers spilled at  *)
(* 1678..1734, with RSP at bot + 1678. The facts that need the rows before i *)
(* to have succeeded are under that hypothesis.                              *)
(* ------------------------------------------------------------------------- *)

let VI65_FRAME_FACTS =
  "read RSP s = word_add bot (word 1678) /\\
    read RBP s = word_add bot (word 12222) /\\
    read (memory :> bytes64 (word_add bot (word 12230))) s = returnaddress /\\
    read (memory :> bytes64 (word_add bot (word 12222))) s = rbp_init /\\
    read (memory :> bytes64 (word_add bot (word 12214))) s = r15_init /\\
    read (memory :> bytes64 (word_add bot (word 12206))) s = r14_init /\\
    read (memory :> bytes64 (word_add bot (word 12198))) s = r13_init /\\
    read (memory :> bytes64 (word_add bot (word 12190))) s = r12_init /\\
    read (memory :> bytes64 (word_add bot (word 12182))) s =
      word_add stackpointer (word 12277) /\\
    read (memory :> bytes64 (word_add bot (word 12174))) s = rbx_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 12269))) s =
      returnaddress /\\
    read (memory :> bytes64 (word_add bot (word 1710))) s = pk /\\
    read (memory :> bytes64 (word_add bot (word 1726))) s =
      word_add bot (word 7054) /\\
    read (memory :> bytes64 (word_add bot (word 1734))) s =
      word_add bot (word 5998) /\\
    read (memory :> bytes64 (word_add bot (word 1686))) s =
      word_add bot (word 1870) /\\
    ~read DF s /\\
    (!j. j < 3309
         ==> read (memory :> bytes8 (word_add sig (word j))) s = sigb j) /\\
    (!j. j < 1952
         ==> read (memory :> bytes8 (word_add pk (word j))) s = pkb j)";;

let VI65_JOIN1 =
  let s = "\\s. " ^ VI65_FRAME_FACTS ^ " /\\
    read RBX s = word_add bot (word 4974) /\\
    read R13 s = word 0 /\\
    read R11 s = sig /\\
    (!j. j < 1280
         ==> read (memory :> bytes32 (word_add bot (word (7054 + 4 * j)))) s =
             VI65Z j) /\\
    read (memory :> bytes (word_add bot (word 1870),64)) s = VI65MU /\\
    read (memory :> bytes128 (word_add bot (word 1742))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add bot (word 1758))) s =
      mld_chunk128 sigb 1 /\\
    read (memory :> bytes128 (word_add bot (word 1774))) s =
      mld_chunk128 sigb 2" in
  subst [VI65_MU,`VI65MU:num`; VI65_Z,`VI65Z:num->int32`] (parse_term s);;

let VI65_INV =
  let s = "\\i s. " ^ VI65_FRAME_FACTS ^ " /\\
    read R12 s = word_add bot (word 3950) /\\
    read RBX s = word_add bot (word 4974) /\\
    read (memory :> bytes64 (word_add bot (word 1718))) s =
      word_add bot (word 2926) /\\
    read (memory :> bytes64 (word_add bot (word 1702))) s = sig /\\
    read (memory :> bytes64 (word_add bot (word 1694))) s =
      word_add bot (word 2158) /\\
    read (memory :> bytes64 (word_add bot (word 1678))) s =
      word_add bot (word 1742) /\\
    read (memory :> bytes (word_add bot (word 7022),32)) s = VI65RHO /\\
    (!j. j < 1280
         ==> read (memory :> bytes32 (word_add bot (word (7054 + 4 * j)))) s =
             VI65ZHAT j) /\\
    (!j. j < 256
         ==> read (memory :> bytes32 (word_add bot (word (2926 + 4 * j)))) s =
             VI65CPHAT j) /\\
    read (memory :> bytes (word_add bot (word 1870),64)) s = VI65MU /\\
    read (memory :> bytes128 (word_add bot (word 1742))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add bot (word 1758))) s =
      mld_chunk128 sigb 1 /\\
    read (memory :> bytes128 (word_add bot (word 1774))) s =
      mld_chunk128 sigb 2 /\\
    ((!j. j < i ==> mld_unpack_hints_ret 55 6 (\\t. sigb(3248 + t)) j = word 0)
     ==> read R13 s = word i /\\
         read R15 s = word_add bot (word (2158 + 128 * i)) /\\
         (0 < i ==> read R14 s = word 0) /\\
         (!j. j < 128 * i
              ==> read (memory :> bytes8 (word_add bot (word (2158 + j)))) s =
                  VI65W1B j))" in
  subst [VI65_MU,`VI65MU:num`; VI65_W1B,`VI65W1B:num->byte`;
         VI65_RHO,`VI65RHO:num`; VI65_ZHAT,`VI65ZHAT:num->int32`;
         VI65_CPHAT,`VI65CPHAT:num->int32`]
        (parse_term s);;

let VI65_PC2 =
  parse_term("if " ^ VI65_HINTSOK ^
             " then pc + mldsa65_verify_internal_loop1_exit1" ^
             " else pc + mldsa65_verify_internal_loop1_exit2");;

(* ------------------------------------------------------------------------- *)
(* From the start to join1: the norm check passes, then mu is copied from m  *)
(* (ext nonzero, the 4 chunks of the 64 bytes at m) or computed (ext zero):  *)
(* tr = SHAKE256(pk) by the incremental functions, then mld_H65 of tr, pre   *)
(* and m. The calls change the 256-bit registers, which YMM_GHOST_TAC names  *)
(* before the SSE code of the copy.                                          *)
(* ------------------------------------------------------------------------- *)

let VI65_CHUNK_NORM_RULE th =
  REWRITE_RULE[WORD_ADD_0; EXP; DIV_1]
   (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) th);;

let VI65_M_CHUNKS_TAC =
  SUBGOAL_THEN `64 <= mlen` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral i;
                  `s0:x86state`] VERIF_BYTES128_OF_BYTES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o VI65_CHUNK_NORM_RULE)) [0;1;2;3];;

let VI65_MU_OF_CHUNKS_TAC a s =
  MP_TAC(SPECL [a; `M:num`; `4`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC];;

let VI65_COPY_TAC =
  X86_STEPS_TAC VI65_EXEC (40--42) THEN VERIF_PC_TAC [VI65_EXT0] THEN
  YMM_GHOST_TAC `s42:x86state` ["YMM6","ymm6_42"; "YMM7","ymm7_42"] THEN
  X86_STEPS_TAC VI65_EXEC (43--55) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VI65_MU_OF_CHUNKS_TAC `word_add bot (word 1870):int64` `s55:x86state` THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

let VI65_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 1952)`;;

let VI65_S0 =
  subst [VI65_PKNUM,`p:num`]
   `FST(mld_keccak_absorb 136 (word 0) 0 1952 p)`;;

let VI65_CTX1 = `word_add bot (word 5998):int64`;;

let VI65_HASH_TAC =
  X86_STEPS_TAC VI65_EXEC (40--42) THEN VERIF_PC_TAC [VI65_EXT0] THEN
  X86_STEPS_TAC VI65_EXEC (43--47) THEN
  VI65_CALL_TAC "H_INIT" [`read RDI s`] 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI65_EXEC (49--52) THEN
  MP_TAC(SPECL [`pk:int64`; `1952`; `pkb:num->byte`; `s52:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  KECCAK_STATE_AT_TAC VI65_CTX1 THEN
  VI65_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `1952`; `word 0:1600 word`; `0`;
    VI65_PKNUM] 53 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `1952 MOD 136` (concl th)
    then REWRITE_RULE[ARITH_RULE `1952 MOD 136 = 48`] th else th) THEN
  X86_STEPS_TAC VI65_EXEC (54--57) THEN
  KECCAK_STATE_AT_TAC VI65_CTX1 THEN
  VI65_CALL_TAC "H_FINALIZE" [`read RDI s`; VI65_S0; `48`] 58 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI65_EXEC (59--62) THEN
  KECCAK_STATE_AT_TAC VI65_CTX1 THEN
  VI65_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `64`; `read RDX s`;
    mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI65_S0),`48`);
    `136`] 63 THEN
  X86_STEPS_TAC VI65_EXEC (64--65) THEN
  VI65_CALL_TAC "H_RELEASE" [`read RDI s`] 66 THEN
  X86_STEPS_TAC VI65_EXEC (67--82) THEN
  VI65_CALL_TAC "H_H65"
   [`read RDI s`; `64`; `read RDX s`; `64`; `read R8 s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    subst [mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI65_S0),`48`),
           `sf:1600 word`]
     `num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 sf 136) 64)`;
    `PRE':num`; `M:num`] 83 THEN
  X86_STEPS_TAC VI65_EXEC (84--92) THEN
  REWRITE_TAC[mld_verify_mu; VI65_TR_EQ] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2 EXP (8 * 64)` (concl th)
    then REWRITE_RULE[ARITH_RULE `8 * 64 = 512`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* From join1 to the loop: the NTT of z, the lazy expansion of the matrix,   *)
(* which copies rho (32 bytes of pk) into its structure, the challenge from  *)
(* c~ (its 2 chunks) and its NTT.                                            *)
(* ------------------------------------------------------------------------- *)

let VI65_MID_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC VI65_EXEC (1--4) THEN
  VI65_CALL_TAC "H_VNTT" [`read RDI s`; VI65_Z] 5 THEN
  X86_STEPS_TAC VI65_EXEC (6--8) THEN
  MP_TAC(SPECL [`pk:int64`; `32`; `pkb:num->byte`; `s8:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  VI65_CALL_TAC "H_MEXP" [`read RDI s`; `read RSI s`; VI65_RHO] 9 THEN
  X86_STEPS_TAC VI65_EXEC (10--17) THEN
  MP_TAC(SPECL [`word_add bot (word 1742):int64`; `sigb:num->byte`; `3`;
                `s17:x86state`] VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  VI65_CALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; VI65_C] 18 THEN
  X86_STEPS_TAC VI65_EXEC (19--20) THEN
  VI65_CALL_TAC "H_NTT" [`read RDI s`; VI65_CP] 21 THEN
  X86_STEPS_TAC VI65_EXEC (22--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_H_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body for row i: the rows before i succeeded and i < 6            *)
(* (VERIF_ROWS), the calls for row i up to the unpacking of its hints, and   *)
(* then either the use of the hints and the packing of the row, or the exit  *)
(* to join4 if the hints do not unpack. Row i of A z is computed by          *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy, which samples the   *)
(* entries of row i of the matrix from rho in the structure, and the row     *)
(* made nonnegative is that of the default configuration (VI65_CADDQ_TAC),   *)
(* so that the packed rows are those of the statement. The events before the *)
(* row are kept opaque as front after the rows already done.                 *)
(* ------------------------------------------------------------------------- *)

let VI65_ROWS_TAC =
  MP_TAC(BETA_RULE(SPECL [mk_abs(`i:num`,VI65_HOK_TM); `6`; `i:num`]
                         VERIF_ROWS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(lhand(concl th)) &&
    fst(dest_forall(lhand(concl th))) = `j:num`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

let VI65_I_ZX = `word_zx(word_zx(word i:int64):int32):int64 = word i`;;

let VI65_I1_ZX =
  `word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
   word(i + 1)`;;

let VI65_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  VERIF_GEN_TAIL_TAC false "front" THEN
  FULL_INIT_TAC THEN VI65_ROWS_TAC THEN
  SUBGOAL_THEN (mk_conj(VI65_I_ZX,VI65_I1_ZX)) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC VI65_EXEC (1--5) THEN VERIF_REG_RULE_TAC[ASSUME VI65_I_ZX] THEN
  VI65_LOOP_CALL_TAC "H_ROW"
   [`read RDI s`; `read RSI s`; `read RDX s`; VI65_RHO; VI65_ZHAT; `i:num`]
   6 THEN
  X86_STEPS_TAC VI65_EXEC (7--10) THEN
  VERIF_REG_RULE_TAC[ASSUME VI65_I_ZX] THEN
  VERIF_SLICE_TAC
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word(32 + 320 * i + j)))) s10 =
            (pkb:num->byte)(32 + 320 * i + j)` THEN
  VI65_LOOP_CALL_TAC "H_T1"
   [`read RDI s`; `read RSI s`; `\j. (pkb:num->byte)(32 + 320 * i + j)`;
    `i:num`] 11 THEN
  X86_STEPS_TAC VI65_EXEC (12--13) THEN
  VI65_LOOP_CALL_TAC "H_SHIFTL" [`read RDI s`; VI65_T1] 14 THEN
  X86_STEPS_TAC VI65_EXEC (15--16) THEN
  VI65_LOOP_CALL_TAC "H_NTT" [`read RDI s`; VI65_SHL] 17 THEN
  X86_STEPS_TAC VI65_EXEC (18--20) THEN
  VI65_LOOP_CALL_TAC "H_PWM"
   [`read RDI s`; `read RSI s`; VI65_NTT1; VI65_CPHAT] 21 THEN
  X86_STEPS_TAC VI65_EXEC (22--24) THEN
  VI65_LOOP_CALL_TAC "H_SUB"
   [`read RDI s`; `read RSI s`; VI65_ROWL; VI65_PWM] 25 THEN
  X86_STEPS_TAC VI65_EXEC (26--27) THEN
  VI65_LOOP_CALL_TAC "H_RED" [`read RDI s`; VI65_SUBL] 28 THEN
  X86_STEPS_TAC VI65_EXEC (29--30) THEN
  VI65_LOOP_CALL_TAC "H_INV" [`read RDI s`; VI65_REDL] 31 THEN
  X86_STEPS_TAC VI65_EXEC (32--33) THEN
  VI65_LOOP_CALL_TAC "H_CADDQ" [`read RDI s`; VI65_INVTL] 34 THEN
  VI65_CADDQ_TAC THEN
  X86_STEPS_TAC VI65_EXEC (35--38) THEN
  VERIF_REG_RULE_TAC[ASSUME VI65_I_ZX] THEN
  VERIF_SLICE_TAC
   `!j. j < 61
        ==> read(memory :> bytes8(word_add sig (word(3248 + j)))) s38 =
            (sigb:num->byte)(3248 + j)` THEN
  VI65_LOOP_CALL_TAC "H_HINTS"
   [`read RDI s`; `read RSI s`; `\t. (sigb:num->byte)(3248 + t)`;
    `i:num`] 39 THEN
  X86_STEPS_TAC VI65_EXEC (40--42);;

let VI65_PC_OK_TAC =
  ASM_CASES_TAC `i + 1 < 6` THENL
   [SUBGOAL_THEN `~(i + 1 = 6)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i + 1 < 6`; ASSUME `~(i + 1 = 6)`];
    SUBGOAL_THEN `i + 1 = 6` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN VI65_HINTSOK_TM ASSUME_TAC THENL
     [VERIF_IMP_CASE_TAC `~(i + 1 < 6)`; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~(i + 1 < 6)`; ASSUME `i + 1 = 6`;
                ASSUME VI65_HINTSOK_TM]];;

let VI65_JOIN_W1_TAC =
  DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[WORD_SUB_M128; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
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

let VI65_BODY_OK_TAC =
  VERIF_MP_CASE_TAC VI65_HOK_TM THEN
  X86_STEPS_TAC VI65_EXEC (43--46) THEN
  VERIF_REG_RULE_TAC[ASSUME VI65_I1_ZX] THEN
  VI65_LOOP_CALL_TAC "H_USEHINT"
   [`read RDI s`; `read RSI s`; VI65_CADDQ; VI65_HINTS] 47 THEN
  X86_STEPS_TAC VI65_EXEC (48--51) THEN
  VI65_LOOP_CALL_TAC "H_W1PACK"
   [`read RDI s`; `read RSI s`; VI65_UH] 52 THEN
  X86_STEPS_TAC VI65_EXEC (53--54) THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN W32_LOOP_TEST_TAC THEN
  CONJ_TAC THENL [VI65_PC_OK_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [VI65_JOIN_W1_TAC; ALL_TAC] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI65_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg VI65_HOK_TM) THEN VERIF_FINAL_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg VI65_HOK_TM)];
    ALL_TAC] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI65_BODY_TAC =
  VI65_BODY1_TAC THEN
  ASM_CASES_TAC VI65_HOK_TM THEN VERIF_PC_TAC [VI65_HOK_TM] THENL
   [VI65_BODY_OK_TAC; VI65_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop, if all hints unpack: c2 = SHAKE256(mu || w1', 48) by the  *)
(* incremental functions, whose two absorbs are one of the concatenation,    *)
(* then the vectorized compare of the 3 chunks of c~ and c2 (a loop that the *)
(* simulation unrolls), whose branch is taken iff the OR of the differences  *)
(* is nonzero (proved by bit-blasting over the OR and XOR folds, once), iff  *)
(* the signature is not accepted.                                            *)
(* ------------------------------------------------------------------------- *)

let VI65_S1 =
  subst [VI65_MU,`mu:num`; VI65_W1NUM,`w:num`]
   `FST(mld_keccak_absorb 136 (word 0) 0 832 (mu + 2 EXP 512 * w))`;;

let VI65_SQ =
  subst [VI65_S1,`s1:1600 word`]
   `mld_keccak_squeeze_byte 136 (mld_keccak_finalize 136 31 s1 16) 136`;;

let VI65_CTX2 = `word_add bot (word 1950):int64`;;

let VI65_ABSORB_APPEND_TAC =
  MLD_H_BOUND_TAC `word_add bot (word 1870):int64` THEN
  FIRST_ASSUM(fun bth ->
    if concl bth <> subst [VI65_MU,`mu:num`] `mu < 2 EXP (8 * 64)`
    then NO_TAC else
    let th = MP (SPECL [`64`; `768`; VI65_MU; VI65_W1NUM]
                       MLD_SHAKE256_ABSORB_APPEND) bth in
    let th' = REWRITE_RULE[ARITH_RULE `64 MOD 136 = 64`;
                           ARITH_RULE `8 * 64 = 512`;
                           ARITH_RULE `64 + 768 = 832`] th in
    RULE_ASSUM_TAC(fun ath ->
      if can (find_term ((=) `mld_keccak_absorb`)) (concl ath) ||
         free_in `(64 + 768) MOD 136` (concl ath)
      then REWRITE_RULE[th'; ARITH_RULE `(64 + 768) MOD 136 = 16`] ath
      else ath));;

let VI65_W1_BYTES_TAC s =
  MP_TAC(SPECL [`word_add bot (word 2158):int64`; `768`; VI65_W1B; s]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_32`)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC];;

let VI65_POST1_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC VI65_EXEC (1--6) THEN
  VI65_POST_CALL_TAC "H_INIT" [`read RDI s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI65_EXEC (8--11) THEN
  KECCAK_STATE_AT_TAC VI65_CTX2 THEN
  VI65_POST_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `64`; `word 0:1600 word`; `0`; VI65_MU]
   12 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `64 MOD 136` (concl th)
    then REWRITE_RULE[ARITH_RULE `64 MOD 136 = 64`] th else th) THEN
  X86_STEPS_TAC VI65_EXEC (13--16) THEN
  VI65_W1_BYTES_TAC `s16:x86state` THEN
  KECCAK_STATE_AT_TAC VI65_CTX2 THEN
  VI65_POST_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `768`;
    mk_comb(`FST:1600 word#num->1600 word`,
     list_mk_comb(`mld_keccak_absorb`,
      [`136`; `word 0:1600 word`; `0`; `64`; VI65_MU]));
    `64`; VI65_W1NUM] 17 THEN
  VI65_ABSORB_APPEND_TAC THEN
  X86_STEPS_TAC VI65_EXEC (18--19) THEN
  KECCAK_STATE_AT_TAC VI65_CTX2 THEN
  VI65_POST_CALL_TAC "H_FINALIZE" [`read RDI s`; VI65_S1; `16`] 20 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI65_EXEC (21--24) THEN
  KECCAK_STATE_AT_TAC VI65_CTX2 THEN
  VI65_POST_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `48`; `read RDX s`;
    mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI65_S1),`16`);
    `136`] 25 THEN
  X86_STEPS_TAC VI65_EXEC (26--27) THEN
  VI65_POST_CALL_TAC "H_RELEASE" [`read RDI s`] 28 THEN
  X86_STEPS_TAC VI65_EXEC (29--32);;

let VI65_C2_CHUNKS_TAC a s =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (term_match [] `read (memory :> bytes(x,48)) (s:x86state) = n`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [a; `48`; VI65_SQ; s; mk_small_numeral i]
                 BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    DISCH_TAC) [0;1;2];;

(*** Name the chunks compared, so that the simulation keeps them opaque ***)

let VI65_CHUNK_VARS = ["cc0";"cc1";"cc2";"dd0";"dd1";"dd2"];;

let VI65_CHUNK_ABBREV_TAC =
  let mk n i f = (mk_var(n ^ string_of_int i,`:int128`),
                  mk_comb(mk_comb(`mld_chunk128`,f),mk_small_numeral i)) in
  let abbs = map (fun i -> mk "cc" i `sigb:num->byte`) [0;1;2] @
             map (fun i -> mk "dd" i VI65_SQ) [0;1;2] in
  MAP_EVERY (fun (v,t) ->
    ABBREV_TAC (mk_eq(v,t)) THEN
    FIRST_ASSUM(fun eth ->
      if concl eth <> mk_eq(t,v) then NO_TAC else
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if is_eq c && rhs c = t &&
           can (term_match []
                 `read (memory :> bytes128 a) (s:x86state) = x:int128`) c
        then TRANS th eth else th))) abbs;;

let VI65_OR_FOLD =
  `word_or (word_or (word_xor cc0 dd0) (word_xor cc1 dd1))
           (word_xor cc2 dd2):int128`;;

let VI65_XOR_FOLD =
  `word_xor (word_xor (word_xor (word 0) (word_xor cc0 dd0))
                      (word_xor cc1 dd1))
            (word_xor cc2 dd2):int128`;;

let VI65_CMP_MEMO = ref ([]:(term * thm) list);;

let VI65_CMP_REDUCE_TAC s =
  W(fun (asl,w) ->
    let pcth = snd(find (fun (_,th) ->
      can (term_match [] (subst [s,`s:x86state`]
                            `read RIP s = (if b then x else y):int64`))
          (concl th)) asl) in
    let c = rand(rator(rator(rhs(concl pcth)))) in
    let c' = subst [`vv:int128`,VI65_OR_FOLD; `ww:int128`,VI65_XOR_FOLD] c in
    let nth = REWRITE_CONV[WORD_VAL_MOD_256; VAL_EQ_0; WORD_SUB_EQ_0] c' in
    let c'' = rhs(concl nth) in
    let tm = mk_forall(`vv:int128`,mk_forall(`ww:int128`,
               mk_eq(c'',`~(vv = word 0:int128)`))) in
    let lem = try assoc tm (!VI65_CMP_MEMO) with Failure _ ->
      let th = BITBLAST_RULE tm in
      (VI65_CMP_MEMO := (tm,th)::(!VI65_CMP_MEMO); th) in
    let th1 = TRANS nth (SPECL [`vv:int128`; `ww:int128`] lem) in
    ASSUME_TAC(INST [VI65_OR_FOLD,`vv:int128`; VI65_XOR_FOLD,`ww:int128`]
                    th1));;

let VI65_OK_EQ_TAC =
  SUBGOAL_THEN (mk_eq(mk_eq(VI65_OR_FOLD,`word 0:int128`),VI65_OK_TM))
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
    W(fun (asl,w) -> REWRITE_TAC(mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_var(rhs c) && mem (fst(dest_var(rhs c))) VI65_CHUNK_VARS
      then SYM th else fail()) asl)) THEN
    REWRITE_TAC[VI65_OK_THM; ASSUME VI65_NORMOK_TM;
                EQT_INTRO(ASSUME VI65_HINTSOK_TM)] THEN
    REWRITE_TAC[VI65_SQ_EQ] THEN
    MP_TAC(ISPECL [`sigb:num->byte`; VI65_SQ; `3`] MLD_CHUNK128_EQ) THEN
    CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
    REWRITE_TAC[ARITH_RULE `16 * 3 = 48`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[];
    ALL_TAC];;

let VI65_CMP_PC_TAC =
  W(fun (asl,w) ->
    let z = mk_eq(VI65_OR_FOLD,`word 0:int128`) in
    let red = snd(find (fun (_,th) -> let c = concl th in
      is_eq c && type_of(lhs c) = bool_ty && rhs c = mk_neg z) asl) in
    let eqv = snd(find (fun (_,th) -> concl th = mk_eq(z,VI65_OK_TM)) asl) in
    let case =
      try EQT_INTRO(snd(find (fun (_,th) -> concl th = VI65_OK_TM) asl))
      with Failure _ ->
        EQF_INTRO(snd(find (fun (_,th) -> concl th = mk_neg VI65_OK_TM)
                           asl)) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read RIP s = (if b then x else y):int64`)
             (concl th)
      then REWRITE_RULE[red; eqv; case] th else th));;

let VI65_POST_OK_TAC =
  VI65_POST1_TAC THEN
  VI65_C2_CHUNKS_TAC `word_add bot (word 1806):int64` `s32:x86state` THEN
  VI65_CHUNK_ABBREV_TAC THEN
  YMM_GHOST_TAC `s32:x86state`
   ["YMM0","ymm0_32"; "YMM1","ymm1_32"; "YMM2","ymm2_32"] THEN
  VERIF_SSE_STEPS_TAC VI65_EXEC (33--88) THEN
  VI65_CMP_REDUCE_TAC `s88:x86state` THEN VI65_OK_EQ_TAC THEN
  ASM_CASES_TAC VI65_OK_TM THEN VI65_CMP_PC_TAC THENL
   [VI65_CLEANUP_TAC VI65_ALLOWED_OLD 88;
    X86_STEPS_TAC VI65_EXEC (89--90) THEN
    VI65_CLEANUP_TAC VI65_ALLOWED_OLD 90] THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(*** If some hints do not unpack: the result -6 and the cleanup ***)

let VI65_POST_HF_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC VI65_EXEC (1--4) THEN
  VI65_CLEANUP_TAC VI65_ALLOWED_OLD 4 THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0; VI65_OK_THM] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

let VI65_POST_TAC =
  VERIF_GEN_TAIL_TAC true "old" THEN
  ASM_CASES_TAC VI65_HINTSOK_TM THENL
   [REWRITE_TAC[EQT_INTRO(ASSUME VI65_HINTSOK_TM); ARITH_RULE `0 < 6`] THEN
    VI65_POST_OK_TAC;
    REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg VI65_HINTSOK_TM))] THEN
    VI65_POST_HF_TAC];;

(* ------------------------------------------------------------------------- *)
(* The callees and the setup: the frame realigned below the entry RSP        *)
(* (REALIGN_TAC with k = N, as the AND comes first), the alignment of RBP    *)
(* and of the polynomials and the structure that the callees need aligned,   *)
(* and the callee-saved registers.                                           *)
(* ------------------------------------------------------------------------- *)

let VI65_CALLEES_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_MEXP_FULL "H_MEXP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_CHAL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_HINTS" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_UNPACKZ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_CHKNORM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_VNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_ROW_FULL "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_UNPACK_PK_T1_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_SHIFTL_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_SHIFTL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_PWM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_SUB_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_USEHINT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYW1_PACK_32_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_W1PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_H_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_H65";;

let VI65_SETUP_TAC =
  VI65_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC VI65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst VI65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 12269 THEN REALIGN_FRAME_TAC 12269 12269 THEN
  REALIGN_NONOV_TAC 12238
   [`sig:int64,3309`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `pk:int64,1952`; `word pc:int64,51232`;
    `word_add stackpointer (word 12269):int64,8`;
    `word_add stackpointer (word 12277):int64,8`] THEN
  REALIGN_ALIGNED_TAC
   [12222; 5998; 4974; 3950; 1742; 1758; 1774; 1806; 1822; 1838] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  VI65_SETUP_TAC THEN VI65_ZHAT_BOUND_TAC THEN
  ASM_CASES_TAC VI65_NORMOK_TM THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term VI65_K)
     `pc + mldsa65_verify_internal_loop1` VI65_PC2 VI65_INV THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                  CONJUNCT1 LT; LT_REFL] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_verify_internal_join1`
       VI65_JOIN1 THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC VI65_EXT0 THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th])
        THENL
         [VI65_PROLOGUE_TAC ALL_TAC THEN VI65_HASH_TAC;
          VI65_PROLOGUE_TAC VI65_M_CHUNKS_TAC THEN VI65_COPY_TAC];
        VI65_MID_TAC];
      VI65_BODY_TAC;
      VI65_POST_TAC];
    VI65_NF_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
