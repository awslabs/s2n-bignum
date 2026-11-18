(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the proof (see verify_internal_87_spec.ml).  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/verify_internal_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

let VI87_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_EXEC;;

let VI87_MEXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL;;

let VI87_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The template of the events. The f_events arguments are ARGS below. The    *)
(* events split on the norm check of z (nf: the whole run when it fails), on *)
(* ext (hash or copy: from the start to join1, where mu is ready), mid (from *)
(* join1 to the loop over the rows), the rows (row: one whose hints unpack,  *)
(* rowf: the first one whose hints do not, after which the loop stops), and  *)
(* the end after the loop: hf when some hints do not unpack, and acc or rej  *)
(* after the hash and the compare of c~ otherwise. The number of rows done   *)
(* is K: 8, or the first failing row plus 1. The code aligns its frame to 32 *)
(* bytes, so that the addresses in it are at fixed offsets from bot          *)
(* (utils/mldsa_native_realign.ml), a function of stackpointer, as the       *)
(* events are once bot is expanded.                                          *)
(* ------------------------------------------------------------------------- *)

let VI87_ARGS =
  "sig m mlen pre prelen pk ext sigb pkb M PRE mf pc stackpointer " ^
  "returnaddress";;

let VI87_LAMBDA =
  "\\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (pk:int64) " ^
  "(ext:int64) (sigb:num->byte) (pkb:num->byte) (M:num) PRE " ^
  "(mf:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).";;

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

let VI87_TEMPLATE_CASE =
  let f n = "(f_ev_" ^ n ^ " " ^ VI87_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ " " ^ VI87_ARGS ^ " i)" in
  "(if " ^ VI87_NORMOK ^ " then " ^
  "APPEND (if " ^ VI87_HINTSOK ^ " then (if " ^ VI87_OK ^ " then " ^
  f "acc" ^ " else " ^ f "rej" ^ ") else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ VI87_K ^ " (\\i. if " ^ VI87_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if word_zx ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ")";;

let VI87_TEMPLATE =
  parse_term(VI87_LAMBDA ^ " " ^ VI87_TEMPLATE_CASE ^ " :(uarch_event)list");;

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

(*** The two SHAKE256 hashes, as the incremental calls give them ***)

let VI87_SQ_EQ = prove
 (`!x. mld_shake256_byte 1088 x =
       mld_keccak_squeeze_byte 136
        (mld_keccak_finalize 136 31
          (FST(mld_keccak_absorb 136 (word 0) 0 1088 x)) 0) 136`,
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; MLD_KECCAK_ABSORB_SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VI87_TR_EQ = prove
 (`!x. mld_shake256_byte 2592 x =
       mld_keccak_squeeze_byte 136
        (mld_keccak_finalize 136 31
          (FST(mld_keccak_absorb 136 (word 0) 0 2592 x)) 8) 136`,
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; MLD_KECCAK_ABSORB_SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Calls and the cleanup. The allowed variables of the events are the        *)
(* arguments of f_events and bot, which REALIGN_UNBOT_TAC expands at the end *)
(* of each part, and in the loop body and after the loop the row index i and *)
(* the generalized events so far (front, old). VI87_CLEANUP_TAC allowed n    *)
(* simulates the code from join2 to the return from state n: the inline      *)
(* zeroing of the buffers (REP STOSQ and 128-bit stores), the memset of the  *)
(* matrix through the PLT, the restoring of the registers and of RSP from    *)
(* R10.                                                                      *)
(* ------------------------------------------------------------------------- *)

let VI87_ALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `pk:int64`; `ext:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
   `PRE':num`; `mf:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let VI87_ALLOWED_LOOP =
  `front:(uarch_event)list`::`i:num`::VI87_ALLOWED;;

let VI87_ALLOWED_OLD = `old:(uarch_event)list`::VI87_ALLOWED;;

let VI87_CALL_GEN_TAC allowed name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc VI87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   allowed n;;

let VI87_CALL_TAC = VI87_CALL_GEN_TAC VI87_ALLOWED;;
let VI87_LOOP_CALL_TAC = VI87_CALL_GEN_TAC VI87_ALLOWED_LOOP;;
let VI87_POST_CALL_TAC = VI87_CALL_GEN_TAC VI87_ALLOWED_OLD;;

(*** The memset of the matrix through the PLT, after its CALL at step n ***)

let VI87_MEMSET_TAC allowed n =
  LIBC_PLT_TAC VI87_EXEC (layout "plt_memset") (layout "got_memset") n THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" VI87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref allowed) (n + 2);;

let VI87_CLEANUP_TAC allowed n =
  VERIF_DROP_MEM_TAC (VERIF_KEEP_FRAME 5166 74310) THEN
  X86_STEPS_TAC VI87_EXEC ((n+1)--(n+14)) THEN
  VI87_MEMSET_TAC allowed (n+14) THEN
  X86_STEPS_TAC VI87_EXEC ((n+17)--(n+56));;

(* ------------------------------------------------------------------------- *)
(* The prologue, to the norm check: the realigned frame (with RBP at bot +   *)
(* 74302), the chunks of c~ that the code copies, the 32-bit argument ext    *)
(* from its slot on the stack, the bytes of z for mldsa87_polyvecl_unpack_z, *)
(* and the bound of the norm check as the code passes it.                    *)
(* ------------------------------------------------------------------------- *)

let VI87_SIG_CHUNKS_TAC =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `4627`; `sigb:num->byte`; `s0:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1;2;3];;

let VI87_EXT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add stackpointer (word 74357))) s =
          (ext:int64)`) (concl th)
    then ASSUME_TAC(MATCH_MP VERIF_BYTES32_OF_BYTES64 th) else NO_TAC);;

let VI87_BND_TAC =
  let tm = `word_zx (word 524168:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let VI87_PROLOGUE_TAC pretac =
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
  FULL_INIT_TAC THEN pretac THEN VI87_SIG_CHUNKS_TAC THEN
  X86_STEPS_TAC VI87_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC VI87_EXEC (3--19) THEN VI87_EXT_TAC THEN
  X86_STEPS_TAC VI87_EXEC (20--33) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VERIF_SLICE_TAC
   `!j. j < 4480
        ==> read(memory :> bytes8(word_add sig (word(64 + j)))) s33 =
            (sigb:num->byte)(64 + j)` THEN
  VI87_CALL_TAC "H_UNPACKZ"
   [`read RDI s`; `read RSI s`; `\j. (sigb:num->byte)(64 + j)`] 34 THEN
  X86_STEPS_TAC VI87_EXEC (35--37) THEN
  VI87_CALL_TAC "H_CHKNORM" [`read RDI s`; VI87_Z; `read RSI s`] 38 THEN
  VI87_BND_TAC THEN
  X86_STEPS_TAC VI87_EXEC (39--41) THEN VERIF_PC_TAC [VI87_NORMOK_TM];;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: the setup of the pointers and of the result -6, and *)
(* the cleanup.                                                              *)
(* ------------------------------------------------------------------------- *)

let VI87_NF_TAC =
  VI87_PROLOGUE_TAC ALL_TAC THEN X86_STEPS_TAC VI87_EXEC (42--56) THEN
  VI87_CLEANUP_TAC VI87_ALLOWED 56 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VI87_OK_THM] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join1, where mu is ready, and at the head of the loop for    *)
(* row i, with the frame at fixed offsets from bot: RBP at bot + 74302, the  *)
(* copy of the return address and the saved registers (with R10, the entry   *)
(* RSP + 8) above it, and below it the matrix, z, the rows of w1 (and tr),   *)
(* tmp, cp, w1' packed, the context of the hash of c2, c2, c~ and mu at      *)
(* offsets 16910, 9742, 8718, 7694, 6670, 5646, 5438, 5358, 5294 and 5230,   *)
(* and the pointers spilled at 5166..5222, with RSP at bot + 5166. The code  *)
(* keeps sig in R11 to join1. The facts that need the rows before i to have  *)
(* succeeded are under that hypothesis.                                      *)
(* ------------------------------------------------------------------------- *)

let VI87_FRAME_FACTS =
  "read RSP s = word_add bot (word 5166) /\\
    read RBP s = word_add bot (word 74302) /\\
    read (memory :> bytes64 (word_add bot (word 74310))) s = returnaddress /\\
    read (memory :> bytes64 (word_add bot (word 74302))) s = rbp_init /\\
    read (memory :> bytes64 (word_add bot (word 74294))) s = r15_init /\\
    read (memory :> bytes64 (word_add bot (word 74286))) s = r14_init /\\
    read (memory :> bytes64 (word_add bot (word 74278))) s = r13_init /\\
    read (memory :> bytes64 (word_add bot (word 74270))) s = r12_init /\\
    read (memory :> bytes64 (word_add bot (word 74262))) s =
      word_add stackpointer (word 74357) /\\
    read (memory :> bytes64 (word_add bot (word 74254))) s = rbx_init /\\
    read (memory :> bytes64 (word_add stackpointer (word 74349))) s =
      returnaddress /\\
    read (memory :> bytes64 (word_add bot (word 5198))) s = pk /\\
    read (memory :> bytes64 (word_add bot (word 5214))) s =
      word_add bot (word 9742) /\\
    read (memory :> bytes64 (word_add bot (word 5222))) s =
      word_add bot (word 16910) /\\
    read (memory :> bytes64 (word_add bot (word 5174))) s =
      word_add bot (word 5230) /\\
    read (memory :> bytes64 (word (pc + got_memset))) s = mf /\\
    read (memory :> bytes (ea,el)) s = ev /\\
    ~read DF s /\\
    (!j. j < 4627
         ==> read (memory :> bytes8 (word_add sig (word j))) s = sigb j) /\\
    (!j. j < 2592
         ==> read (memory :> bytes8 (word_add pk (word j))) s = pkb j)";;

let VI87_JOIN1 =
  let s = "\\s. " ^ VI87_FRAME_FACTS ^ " /\\
    read RBX s = word_add bot (word 8718) /\\
    read R13 s = word 0 /\\
    read R11 s = sig /\\
    (!j. j < 1792
         ==> read (memory :> bytes32 (word_add bot (word (9742 + 4 * j)))) s =
             VI87Z j) /\\
    read (memory :> bytes (word_add bot (word 5230),64)) s = VI87MU /\\
    read (memory :> bytes128 (word_add bot (word 5294))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add bot (word 5310))) s =
      mld_chunk128 sigb 1 /\\
    read (memory :> bytes128 (word_add bot (word 5326))) s =
      mld_chunk128 sigb 2 /\\
    read (memory :> bytes128 (word_add bot (word 5342))) s =
      mld_chunk128 sigb 3" in
  subst [VI87_MU,`VI87MU:num`; VI87_Z,`VI87Z:num->int32`] (parse_term s);;

let VI87_INV =
  let s = "\\i s. " ^ VI87_FRAME_FACTS ^ " /\\
    read R12 s = word_add bot (word 7694) /\\
    read RBX s = word_add bot (word 8718) /\\
    read (memory :> bytes64 (word_add bot (word 5206))) s =
      word_add bot (word 6670) /\\
    read (memory :> bytes64 (word_add bot (word 5190))) s = sig /\\
    read (memory :> bytes64 (word_add bot (word 5182))) s =
      word_add bot (word 5646) /\\
    read (memory :> bytes64 (word_add bot (word 5166))) s =
      word_add bot (word 5294) /\\
    (!j. j < 14336
         ==> read (memory :> bytes32 (word_add bot (word (16910 + 4 * j)))) s =
             mld_polyvec_matrix_expand 7 VI87RHO j) /\\
    (!j. j < 1792
         ==> read (memory :> bytes32 (word_add bot (word (9742 + 4 * j)))) s =
             VI87ZHAT j) /\\
    (!j. j < 256
         ==> read (memory :> bytes32 (word_add bot (word (6670 + 4 * j)))) s =
             VI87CPHAT j) /\\
    read (memory :> bytes (word_add bot (word 5230),64)) s = VI87MU /\\
    read (memory :> bytes128 (word_add bot (word 5294))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add bot (word 5310))) s =
      mld_chunk128 sigb 1 /\\
    read (memory :> bytes128 (word_add bot (word 5326))) s =
      mld_chunk128 sigb 2 /\\
    read (memory :> bytes128 (word_add bot (word 5342))) s =
      mld_chunk128 sigb 3 /\\
    ((!j. j < i ==> mld_unpack_hints_ret 75 8 (\\t. sigb(4544 + t)) j = word 0)
     ==> read R13 s = word i /\\
         read R15 s = word_add bot (word (5646 + 128 * i)) /\\
         (0 < i ==> read R14 s = word 0) /\\
         (!j. j < 128 * i
              ==> read (memory :> bytes8 (word_add bot (word (5646 + j)))) s =
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
(* tr = SHAKE256(pk) by the incremental functions, then mld_H87 of tr, pre   *)
(* and m. The calls change the 256-bit registers, which YMM_GHOST_TAC names  *)
(* before the SSE code of the copy.                                          *)
(* ------------------------------------------------------------------------- *)

let VI87_CHUNK_NORM_RULE th =
  REWRITE_RULE[WORD_ADD_0; EXP; DIV_1]
   (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) th);;

let VI87_M_CHUNKS_TAC =
  SUBGOAL_THEN `64 <= mlen` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral i;
                  `s0:x86state`] VERIF_BYTES128_OF_BYTES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o VI87_CHUNK_NORM_RULE)) [0;1;2;3];;

let VI87_MU_OF_CHUNKS_TAC a s =
  MP_TAC(SPECL [a; `M:num`; `4`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC];;

let VI87_COPY_TAC =
  X86_STEPS_TAC VI87_EXEC (42--44) THEN VERIF_PC_TAC [VI87_EXT0] THEN
  YMM_GHOST_TAC `s44:x86state`
   ["YMM3","ymm3_44"; "YMM4","ymm4_44"; "YMM7","ymm7_44"] THEN
  X86_STEPS_TAC VI87_EXEC (45--57) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VI87_MU_OF_CHUNKS_TAC `word_add bot (word 5230):int64` `s57:x86state` THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

let VI87_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 2592)`;;

let VI87_S0 =
  subst [VI87_PKNUM,`p:num`]
   `FST(mld_keccak_absorb 136 (word 0) 0 2592 p)`;;

let VI87_CTX1 = `word_add bot (word 16910):int64`;;

let VI87_HASH_TAC =
  X86_STEPS_TAC VI87_EXEC (42--44) THEN VERIF_PC_TAC [VI87_EXT0] THEN
  X86_STEPS_TAC VI87_EXEC (45--49) THEN
  VI87_CALL_TAC "H_INIT" [`read RDI s`] 50 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI87_EXEC (51--54) THEN
  MP_TAC(SPECL [`pk:int64`; `2592`; `pkb:num->byte`; `s54:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  KECCAK_STATE_AT_TAC VI87_CTX1 THEN
  VI87_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `2592`; `word 0:1600 word`; `0`;
    VI87_PKNUM] 55 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2592 MOD 136` (concl th)
    then REWRITE_RULE[ARITH_RULE `2592 MOD 136 = 8`] th else th) THEN
  X86_STEPS_TAC VI87_EXEC (56--59) THEN
  KECCAK_STATE_AT_TAC VI87_CTX1 THEN
  VI87_CALL_TAC "H_FINALIZE" [`read RDI s`; VI87_S0; `8`] 60 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI87_EXEC (61--64) THEN
  KECCAK_STATE_AT_TAC VI87_CTX1 THEN
  VI87_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `64`; `read RDX s`;
    mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI87_S0),`8`);
    `136`] 65 THEN
  X86_STEPS_TAC VI87_EXEC (66--67) THEN
  VI87_CALL_TAC "H_RELEASE" [`read RDI s`] 68 THEN
  X86_STEPS_TAC VI87_EXEC (69--84) THEN
  VI87_CALL_TAC "H_H87"
   [`read RDI s`; `read RSI s`; `64`; `read RCX s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    subst [mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI87_S0),`8`),
           `sf:1600 word`]
     `num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 sf 136) 64)`;
    `PRE':num`; `M:num`] 85 THEN
  X86_STEPS_TAC VI87_EXEC (86--94) THEN
  REWRITE_TAC[mld_verify_mu; VI87_TR_EQ] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2 EXP (8 * 64)` (concl th)
    then REWRITE_RULE[ARITH_RULE `8 * 64 = 512`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* From join1 to the loop: the NTT of z, the expansion of the matrix from    *)
(* rho (32 bytes of pk), the challenge from c~ (its 4 chunks) and its NTT.   *)
(* ------------------------------------------------------------------------- *)

let VI87_MID_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC VI87_EXEC (1--4) THEN
  VI87_CALL_TAC "H_VNTT" [`read RDI s`; VI87_Z] 5 THEN
  X86_STEPS_TAC VI87_EXEC (6--8) THEN
  MP_TAC(SPECL [`pk:int64`; `32`; `pkb:num->byte`; `s8:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  VI87_CALL_TAC "H_MEXP" [`read RDI s`; `read RSI s`; VI87_RHO] 9 THEN
  X86_STEPS_TAC VI87_EXEC (10--17) THEN
  MP_TAC(SPECL [`word_add bot (word 5294):int64`; `sigb:num->byte`; `4`;
                `s17:x86state`] VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  VI87_CALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; VI87_C] 18 THEN
  X86_STEPS_TAC VI87_EXEC (19--20) THEN
  VI87_CALL_TAC "H_NTT" [`read RDI s`; VI87_CP] 21 THEN
  X86_STEPS_TAC VI87_EXEC (22--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_H_DISCHARGE_TAC;;

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
  X86_STEPS_TAC VI87_EXEC (1--5) THEN VERIF_REG_RULE_TAC[ASSUME VI87_I_ZX] THEN
  VI87_LOOP_CALL_TAC "H_ROW"
   [`read RDI s`; `read RSI s`; `read RDX s`;
    mk_comb(`mld_polyvec_matrix_expand 7`,VI87_RHO); VI87_ZHAT; `i:num`] 6 THEN
  X86_STEPS_TAC VI87_EXEC (7--10) THEN VERIF_REG_RULE_TAC[ASSUME VI87_I_ZX] THEN
  VERIF_SLICE_TAC
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word(32 + 320 * i + j)))) s10 =
            (pkb:num->byte)(32 + 320 * i + j)` THEN
  VI87_LOOP_CALL_TAC "H_T1"
   [`read RDI s`; `read RSI s`; `\j. (pkb:num->byte)(32 + 320 * i + j)`;
    `i:num`] 11 THEN
  X86_STEPS_TAC VI87_EXEC (12--13) THEN
  VI87_LOOP_CALL_TAC "H_SHIFTL" [`read RDI s`; VI87_T1] 14 THEN
  X86_STEPS_TAC VI87_EXEC (15--16) THEN
  VI87_LOOP_CALL_TAC "H_NTT" [`read RDI s`; VI87_SHL] 17 THEN
  X86_STEPS_TAC VI87_EXEC (18--20) THEN
  VI87_LOOP_CALL_TAC "H_PWM"
   [`read RDI s`; `read RSI s`; VI87_NTT1; VI87_CPHAT] 21 THEN
  X86_STEPS_TAC VI87_EXEC (22--24) THEN
  VI87_LOOP_CALL_TAC "H_SUB"
   [`read RDI s`; `read RSI s`; VI87_ACC; VI87_PWM] 25 THEN
  X86_STEPS_TAC VI87_EXEC (26--27) THEN
  VI87_LOOP_CALL_TAC "H_RED" [`read RDI s`; VI87_SUB] 28 THEN
  X86_STEPS_TAC VI87_EXEC (29--30) THEN
  VI87_LOOP_CALL_TAC "H_INV" [`read RDI s`; VI87_RED] 31 THEN
  X86_STEPS_TAC VI87_EXEC (32--33) THEN
  VI87_LOOP_CALL_TAC "H_CADDQ" [`read RDI s`; VI87_INVT] 34 THEN
  X86_STEPS_TAC VI87_EXEC (35--38) THEN
  VERIF_REG_RULE_TAC[ASSUME VI87_I_ZX] THEN
  VERIF_SLICE_TAC
   `!j. j < 83
        ==> read(memory :> bytes8(word_add sig (word(4544 + j)))) s38 =
            (sigb:num->byte)(4544 + j)` THEN
  VI87_LOOP_CALL_TAC "H_HINTS"
   [`read RDI s`; `read RSI s`; `\t. (sigb:num->byte)(4544 + t)`;
    `i:num`] 39 THEN
  X86_STEPS_TAC VI87_EXEC (40--42);;

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

let VI87_BODY_OK_TAC =
  VERIF_MP_CASE_TAC VI87_HOK_TM THEN
  X86_STEPS_TAC VI87_EXEC (43--46) THEN
  VERIF_REG_RULE_TAC[ASSUME VI87_I1_ZX] THEN
  VI87_LOOP_CALL_TAC "H_USEHINT"
   [`read RDI s`; `read RSI s`; VI87_CADDQ; VI87_HINTS] 47 THEN
  X86_STEPS_TAC VI87_EXEC (48--51) THEN
  VI87_LOOP_CALL_TAC "H_W1PACK" [`read RDI s`; `read RSI s`; VI87_UH] 52 THEN
  X86_STEPS_TAC VI87_EXEC (53--54) THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN W32_LOOP_TEST_TAC THEN
  CONJ_TAC THENL [VI87_PC_OK_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [VI87_JOIN_W1_TAC; ALL_TAC] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI87_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg VI87_HOK_TM) THEN VERIF_FINAL_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg VI87_HOK_TM)];
    ALL_TAC] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

let VI87_BODY_TAC =
  VI87_BODY1_TAC THEN
  ASM_CASES_TAC VI87_HOK_TM THEN VERIF_PC_TAC [VI87_HOK_TM] THENL
   [VI87_BODY_OK_TAC; VI87_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop, if all hints unpack: c2 = SHAKE256(mu || w1', 64) by the  *)
(* incremental functions, whose two absorbs are one of the concatenation,    *)
(* then the vectorized compare of the 4 chunks of c~ and c2 (a loop that the *)
(* simulation unrolls), whose branch is taken iff the OR of the differences  *)
(* is nonzero (proved by bit-blasting over the OR and XOR folds, once), iff  *)
(* the signature is not accepted.                                            *)
(* ------------------------------------------------------------------------- *)

let VI87_S1 =
  subst [VI87_MU,`mu:num`; VI87_W1NUM,`w:num`]
   `FST(mld_keccak_absorb 136 (word 0) 0 1088 (mu + 2 EXP 512 * w))`;;

let VI87_SQ =
  subst [VI87_S1,`s1:1600 word`]
   `mld_keccak_squeeze_byte 136 (mld_keccak_finalize 136 31 s1 0) 136`;;

let VI87_CTX2 = `word_add bot (word 5438):int64`;;

let VI87_ABSORB_APPEND_TAC =
  MLD_H_BOUND_TAC `word_add bot (word 5230):int64` THEN
  FIRST_ASSUM(fun bth ->
    if concl bth <> subst [VI87_MU,`mu:num`] `mu < 2 EXP (8 * 64)`
    then NO_TAC else
    let th = MP (SPECL [`64`; `1024`; VI87_MU; VI87_W1NUM]
                       MLD_SHAKE256_ABSORB_APPEND) bth in
    let th' = REWRITE_RULE[ARITH_RULE `64 MOD 136 = 64`;
                           ARITH_RULE `8 * 64 = 512`;
                           ARITH_RULE `64 + 1024 = 1088`] th in
    RULE_ASSUM_TAC(fun ath ->
      if can (find_term ((=) `mld_keccak_absorb`)) (concl ath) ||
         free_in `(64 + 1024) MOD 136` (concl ath)
      then REWRITE_RULE[th'; ARITH_RULE `(64 + 1024) MOD 136 = 0`] ath
      else ath));;

let VI87_W1_BYTES_TAC s =
  MP_TAC(SPECL [`word_add bot (word 5646):int64`; `1024`; VI87_W1B; s]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_32`)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC];;

let VI87_POST1_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC VI87_EXEC (1--6) THEN
  VI87_POST_CALL_TAC "H_INIT" [`read RDI s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI87_EXEC (8--11) THEN
  KECCAK_STATE_AT_TAC VI87_CTX2 THEN
  VI87_POST_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `64`; `word 0:1600 word`; `0`; VI87_MU]
   12 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `64 MOD 136` (concl th)
    then REWRITE_RULE[ARITH_RULE `64 MOD 136 = 64`] th else th) THEN
  X86_STEPS_TAC VI87_EXEC (13--16) THEN
  VI87_W1_BYTES_TAC `s16:x86state` THEN
  KECCAK_STATE_AT_TAC VI87_CTX2 THEN
  VI87_POST_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `1024`;
    mk_comb(`FST:1600 word#num->1600 word`,
     list_mk_comb(`mld_keccak_absorb`,
      [`136`; `word 0:1600 word`; `0`; `64`; VI87_MU]));
    `64`; VI87_W1NUM] 17 THEN
  VI87_ABSORB_APPEND_TAC THEN
  X86_STEPS_TAC VI87_EXEC (18--19) THEN
  KECCAK_STATE_AT_TAC VI87_CTX2 THEN
  VI87_POST_CALL_TAC "H_FINALIZE" [`read RDI s`; VI87_S1; `0`] 20 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC VI87_EXEC (21--24) THEN
  KECCAK_STATE_AT_TAC VI87_CTX2 THEN
  VI87_POST_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `64`; `read RDX s`;
    mk_comb(mk_comb(`mld_keccak_finalize 136 31`,VI87_S1),`0`);
    `136`] 25 THEN
  X86_STEPS_TAC VI87_EXEC (26--27) THEN
  VI87_POST_CALL_TAC "H_RELEASE" [`read RDI s`] 28 THEN
  X86_STEPS_TAC VI87_EXEC (29--32);;

let VI87_C2_CHUNKS_TAC a s =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (term_match [] `read (memory :> bytes(x,64)) (s:x86state) = n`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [a; `64`; VI87_SQ; s; mk_small_numeral i]
                 BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    DISCH_TAC) [0;1;2;3];;

(*** Name the chunks compared, so that the simulation keeps them opaque ***)

let VI87_CHUNK_VARS =
  ["cc0";"cc1";"cc2";"cc3";"dd0";"dd1";"dd2";"dd3"];;

let VI87_CHUNK_ABBREV_TAC =
  let mk n i f = (mk_var(n ^ string_of_int i,`:int128`),
                  mk_comb(mk_comb(`mld_chunk128`,f),mk_small_numeral i)) in
  let abbs = map (fun i -> mk "cc" i `sigb:num->byte`) [0;1;2;3] @
             map (fun i -> mk "dd" i VI87_SQ) [0;1;2;3] in
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

let VI87_OR_FOLD =
  `word_or (word_or (word_or (word_xor cc0 dd0) (word_xor cc1 dd1))
                    (word_xor cc2 dd2))
           (word_xor cc3 dd3):int128`;;

let VI87_XOR_FOLD =
  `word_xor (word_xor (word_xor (word_xor (word 0) (word_xor cc0 dd0))
                                (word_xor cc1 dd1))
                      (word_xor cc2 dd2))
            (word_xor cc3 dd3):int128`;;

let VI87_CMP_MEMO = ref ([]:(term * thm) list);;

let VI87_CMP_REDUCE_TAC s =
  W(fun (asl,w) ->
    let pcth = snd(find (fun (_,th) ->
      can (term_match [] (subst [s,`s:x86state`]
                            `read RIP s = (if b then x else y):int64`))
          (concl th)) asl) in
    let c = rand(rator(rator(rhs(concl pcth)))) in
    let c' = subst [`vv:int128`,VI87_OR_FOLD; `ww:int128`,VI87_XOR_FOLD] c in
    let nth = REWRITE_CONV[WORD_VAL_MOD_256; VAL_EQ_0; WORD_SUB_EQ_0] c' in
    let c'' = rhs(concl nth) in
    let tm = mk_forall(`vv:int128`,mk_forall(`ww:int128`,
               mk_eq(c'',`~(vv = word 0:int128)`))) in
    let lem = try assoc tm (!VI87_CMP_MEMO) with Failure _ ->
      let th = BITBLAST_RULE tm in
      (VI87_CMP_MEMO := (tm,th)::(!VI87_CMP_MEMO); th) in
    let th1 = TRANS nth (SPECL [`vv:int128`; `ww:int128`] lem) in
    ASSUME_TAC(INST [VI87_OR_FOLD,`vv:int128`; VI87_XOR_FOLD,`ww:int128`]
                    th1));;

let VI87_OK_EQ_TAC =
  SUBGOAL_THEN (mk_eq(mk_eq(VI87_OR_FOLD,`word 0:int128`),VI87_OK_TM))
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
    W(fun (asl,w) -> REWRITE_TAC(mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_var(rhs c) && mem (fst(dest_var(rhs c))) VI87_CHUNK_VARS
      then SYM th else fail()) asl)) THEN
    REWRITE_TAC[VI87_OK_THM; ASSUME VI87_NORMOK_TM;
                EQT_INTRO(ASSUME VI87_HINTSOK_TM)] THEN
    REWRITE_TAC[VI87_SQ_EQ] THEN
    MP_TAC(ISPECL [`sigb:num->byte`; VI87_SQ; `4`] MLD_CHUNK128_EQ) THEN
    CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
    REWRITE_TAC[ARITH_RULE `16 * 4 = 64`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[];
    ALL_TAC];;

let VI87_CMP_PC_TAC =
  W(fun (asl,w) ->
    let z = mk_eq(VI87_OR_FOLD,`word 0:int128`) in
    let red = snd(find (fun (_,th) -> let c = concl th in
      is_eq c && type_of(lhs c) = bool_ty && rhs c = mk_neg z) asl) in
    let eqv = snd(find (fun (_,th) -> concl th = mk_eq(z,VI87_OK_TM)) asl) in
    let case =
      try EQT_INTRO(snd(find (fun (_,th) -> concl th = VI87_OK_TM) asl))
      with Failure _ ->
        EQF_INTRO(snd(find (fun (_,th) -> concl th = mk_neg VI87_OK_TM) asl)) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read RIP s = (if b then x else y):int64`)
             (concl th)
      then REWRITE_RULE[red; eqv; case] th else th));;

let VI87_POST_OK_TAC =
  VI87_POST1_TAC THEN
  VI87_C2_CHUNKS_TAC `word_add bot (word 5358):int64` `s32:x86state` THEN
  VI87_CHUNK_ABBREV_TAC THEN
  YMM_GHOST_TAC `s32:x86state`
   ["YMM0","ymm0_32"; "YMM1","ymm1_32"; "YMM2","ymm2_32"] THEN
  VERIF_SSE_STEPS_TAC VI87_EXEC (33--95) THEN
  VI87_CMP_REDUCE_TAC `s95:x86state` THEN VI87_OK_EQ_TAC THEN
  ASM_CASES_TAC VI87_OK_TM THEN VI87_CMP_PC_TAC THENL
   [VI87_CLEANUP_TAC VI87_ALLOWED_OLD 95;
    X86_STEPS_TAC VI87_EXEC (96--97) THEN
    VI87_CLEANUP_TAC VI87_ALLOWED_OLD 97] THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(*** If some hints do not unpack: the result -6 and the cleanup ***)

let VI87_POST_HF_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC VI87_EXEC (1--4) THEN
  VI87_CLEANUP_TAC VI87_ALLOWED_OLD 4 THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0; VI87_OK_THM] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_ONLY_TAC THEN
  VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

let VI87_POST_TAC =
  VERIF_GEN_TAIL_TAC true "old" THEN
  ASM_CASES_TAC VI87_HINTSOK_TM THENL
   [REWRITE_TAC[EQT_INTRO(ASSUME VI87_HINTSOK_TM); ARITH_RULE `0 < 8`] THEN
    VI87_POST_OK_TAC;
    REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg VI87_HINTSOK_TM))] THEN
    VI87_POST_HF_TAC];;

(* ------------------------------------------------------------------------- *)
(* The callees, with the contract of memset, and the setup: the frame        *)
(* realigned below the entry RSP (REALIGN_TAC with k = N, as the AND comes   *)
(* first), the alignment of RBP, of the polynomials that the callees need    *)
(* aligned and of the chunks of c~ and c2 that the compare loop reads, and   *)
(* the callee-saved registers.                                               *)
(* ------------------------------------------------------------------------- *)

let VI87_CALLEES_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI87_MEXP_FULL "H_MEXP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CHALLENGE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CHAL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_HINTS" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_UNPACK_Z_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_UNPACKZ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_CHKNORM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_VNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI87_ROW_FULL "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_UNPACK_PK_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_T1" THEN
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
   MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_USEHINT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYW1_PACK_32_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_W1PACK" THEN
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
   MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_H87";;

let VI87_SETUP_TAC =
  VI87_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC VI87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst VI87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 74349 THEN REALIGN_FRAME_TAC 74349 74349 THEN
  REALIGN_NONOV_TAC 74318
   [`sig:int64,4627`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `pk:int64,2592`; `word pc:int64,51232`;
    `word(pc + got_memset):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 74349):int64,8`;
    `word_add stackpointer (word 74357):int64,8`] THEN
  REALIGN_ALIGNED_TAC
   [74302; 8718; 7694; 5294; 5310; 5326; 5342; 5358; 5374; 5390; 5406] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  VI87_SETUP_TAC THEN
  ASM_CASES_TAC VI87_NORMOK_TM THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term VI87_K)
     `pc + mldsa87_verify_internal_loop1` VI87_PC2 VI87_INV THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                  CONJUNCT1 LT; LT_REFL] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa87_verify_internal_join1`
       VI87_JOIN1 THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC VI87_EXT0 THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th])
        THENL
         [VI87_PROLOGUE_TAC ALL_TAC THEN VI87_HASH_TAC;
          VI87_PROLOGUE_TAC VI87_M_CHUNKS_TAC THEN VI87_COPY_TAC];
        VI87_MID_TAC];
      VI87_BODY_TAC;
      VI87_POST_TAC];
    VI87_NF_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
