(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the proof (see verify_internal_44_spec.ml). *)
(*                                                                           *)
(* clang has inlined most callees of mldsa44_verify_internal, so the proof   *)
(* composes three kinds of pieces with FULL_CALL_TAC: the theorems of the    *)
(* functions that are still called (polyvecl_chknorm, poly_ntt,              *)
(* poly_invntt_tomont, poly_challenge, the row of the matrix product, mld_H, *)
(* the permutation through the absorption of pk), the region lemmas of the   *)
(* inlined loops and straight-line code (verify_internal_44_inline.ml), and  *)
(* the contracts of memset and memcpy.                                       *)
(*                                                                           *)
(* VI44_MAIN is the body as a region lemma, from loop1 (after the prologue,  *)
(* with RSP = rsp0 aligned to 32) to join2 (the start of the zeroing), with  *)
(* the result in R14. It follows the gcc proof: the norm check of z (the     *)
(* rejection path nf), mu (the hash path for ext = 0, the copy otherwise),   *)
(* the NTTs of z and of the challenge (mid), then a loop over the K rows,    *)
(* with K = 4 or the first row whose hints do not unpack, plus 1             *)
(* (ENSURES_EVENTS_WHILE_UP2_TAC), and after it c2 = H(mu, w1') and the      *)
(* comparison (post), or -6 (hf). The callees use the stack below rsp0,      *)
(* down to rsp0 - 1654 (the row of the matrix product).                      *)
(*                                                                           *)
(* The whole function then is the prologue, which realigns the frame to 32   *)
(* bytes below the six registers that it pushes (REALIGN_TAC with k = 10949  *)
(* - 48, and RSP = rsp0 = bot + 1654 after it), VI44_MAIN, and the zeroing   *)
(* of the buffers and the return (VI44_CLEANUP).                             *)
(*                                                                           *)
(* The aligned SSE loads of constants from the read-only data are            *)
(* RIP-relative: IMAGE_RIPREL_TAC (utils/mldsa_native_scalar.ml) gives the   *)
(* value and the alignment of the address in the form that the simulation   *)
(* uses, before each of them.                                                *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_pack.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "common/mldsa_native_packing.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "common/fips204/properties/mldsa_native_lazy.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_44_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_tools.ml";;

(* ------------------------------------------------------------------------- *)
(* The body, from loop1 to join2.                                            *)
(* ------------------------------------------------------------------------- *)


let VM_HOK = "mld_unpack_hints_ok 80 4 (\\t. sigb(2336 + t)) i";;

let VM_HINTSOK = "(!i. i < 4 ==> " ^ VM_HOK ^ ")";;

let VM_K =
  "(if " ^ VM_HINTSOK ^ " then 4 else (minimal i. ~(" ^ VM_HOK ^
  ")) + 1)";;

let VM_NORMOK =
  "mld_polyvec_chknorm 4 (mld_polyvec_unpack 576 mld_polyz_unpack_17 " ^
  "(\\j. sigb(32 + j))) (word 130994) = word 0";;

let VM_OK =
  "mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994 " ^
  "mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 sigb pkb " ^
  "(if ext = (word 0:int32) " ^
  "then mld_verify_mu 1312 pkb prelen PRE' mlen M else M MOD 2 EXP 512)";;

let VM_TEMPLATE_CASE =
  let f n = "(f_ev_" ^ n ^ " " ^ VM_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ " " ^ VM_ARGS ^ " i)" in
  "(if " ^ VM_NORMOK ^ " then " ^
  "APPEND (if " ^ VM_HINTSOK ^ " then " ^ f "post" ^ " else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ VM_K ^ " (\\i. if " ^ VM_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ")";;

let VM_TEMPLATE =
  parse_term(VM_LAMBDA ^ " " ^ VM_TEMPLATE_CASE ^ " :(uarch_event)list");;

let VM_READS =
  "[sig,2420; m,mlen; pre,prelen; pk,1312;
    word_sub rsp0 (word 1654),10870;
    word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
    word(pc + rodata_mld_KeccakF_RoundConstants),192;
    word(pc + rodata_mld_zetas),1024;
    word(pc + mldsa44_poly_challenge_consts),64;
    word(pc + mldsa44_verify_internal_const1),16;
    word(pc + mldsa44_verify_internal_const2),16;
    word(pc + mldsa44_verify_internal_const3),8;
    word(pc + mldsa44_verify_internal_const4),8;
    word(pc + mld_compute_pack_t0_t144_const1),16;
    word(pc + mld_compute_pack_t0_t144_const2),16;
    word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
    word(pc + mldsa_poly_ntt_consts),256;
    word(pc + mldsa_poly_invntt_tomont_consts),448]";;

let VM_STMT =
  parse_term(subst_tokens ["@MC@",image_mc; "@READS@",VM_READS]
  "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc rsp0.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          mlen < 2 EXP 64 /\\ prelen < 2 EXP 64 /\\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\\
          mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(list_of_seq sigb 32)) /\\
          aligned 32 rsp0 /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1654),10870))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + mldsa44_verify_internal_loop1) /\\
                    read RSP s = rsp0 /\\
                    read RAX s = word_add sig (word 40) /\\ read RCX s = word 12 /\\
                    read R10 s = sig /\\ read R12 s = m /\\ read R13 s = word mlen /\\
                    read RBX s = pk /\\ read R15 s = word_zx ext /\\
                    read (memory :> bytes64 (word_add rsp0 (word 40))) s = word prelen /\\
                    read (memory :> bytes64 (word_add rsp0 (word 48))) s = pre /\\
                    read (memory :> bytes128 (word_add rsp0 (word 64))) s =
                      mld_chunk128 sigb 0 /\\
                    read (memory :> bytes128 (word_add rsp0 (word 80))) s =
                      mld_chunk128 sigb 1 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s = sigb j) /\\
                    read (memory :> bytes(m,mlen)) s = M /\\
                    read (memory :> bytes(pre,prelen)) s = PRE /\\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s = pkb j) /\\
                    read events s = e)
               (\\s. read RIP s = word (pc + mldsa44_verify_internal_join2) /\\
                    read RSP s = rsp0 /\\
                    read R14 s =
                    (if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 1312 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (exists e2.
                       read events s = APPEND e2 e /\\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              mf mc pc rsp0 /\\
                       memaccess_inbounds e2 @READS@
                        [word_sub rsp0 (word 1654),10870]))
               (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1654),10870)])");;

(* ------------------------------------------------------------------------- *)
(* The z vector as the code unpacks it, polynomial by polynomial, at         *)
(* rsp0 + 4320.                                                               *)
(* ------------------------------------------------------------------------- *)

let VM_VEC4 = prove
 (`!(r:int64) (sigb:num->byte) (s:x86state).
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(4320 + 4 * i)))) s =
                      mld_polyz_unpack_17 (\j. sigb(32 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(5344 + 4 * i)))) s =
                      mld_polyz_unpack_17 (\j. sigb(608 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(6368 + 4 * i)))) s =
                      mld_polyz_unpack_17 (\j. sigb(1184 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(7392 + 4 * i)))) s =
                      mld_polyz_unpack_17 (\j. sigb(1760 + j)) i)
     ==> !i. i < 1024
             ==> read(memory :> bytes32(word_add r (word(4320 + 4 * i)))) s =
                 mld_polyvec_unpack 576 mld_polyz_unpack_17 (\j. sigb(32 + j)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  SUBGOAL_THEN `i = 256 * (i DIV 256) + i MOD 256 /\ i MOD 256 < 256 /\ i DIV 256 < 4`
   MP_TAC THENL
   [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = i DIV 256` THEN ABBREV_TAC `t = i MOD 256` THEN
  REWRITE_TAC[ARITH_RULE `q < 4 <=> q = 0 \/ q = 1 \/ q = 2 \/ q = 3`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `i:num`
                          then SUBST1_TAC th else NO_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Polynomial k of a vector of 4 at base, and back *)

let VM_SPLIT = prove
 (`!(r:int64) base (x:num->int32) (s:x86state) k.
     (!i. i < 1024 ==> read(memory :> bytes32(word_add r (word(base + 4 * i)))) s = x i) /\
     k < 4
     ==> !i. i < 256
             ==> read(memory :> bytes32(word_add r (word((base + 1024 * k) + 4 * i)))) s =
                 mld_poly_of x k i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * k + i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `base + 4 * (256 * k + i) = (base + 1024 * k) + 4 * i`]);;

let VM_JOIN = prove
 (`!(r:int64) base (f:num->num->int32) (s:x86state).
     (!k i. k < 4 /\ i < 256
            ==> read(memory :> bytes32(word_add r (word((base + 1024 * k) + 4 * i)))) s =
                f k i)
     ==> !i. i < 1024
             ==> read(memory :> bytes32(word_add r (word(base + 4 * i)))) s =
                 mld_polyvec f i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(base + 1024 * i DIV 256) + 4 * i MOD 256 = base + 4 * i`
   (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC);;

(* the facts for the 4 polynomials at base + 1024 k, each with the value f k *)
let VM_JOIN_TAC (base:int) (f:term) (st:term) =
  MP_TAC(SPECL [`rsp0:int64`; mk_small_numeral base; f; st] VM_JOIN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC];;

(* the fact for polynomial k of the vector at base, from that for the vector *)
let VM_SPLIT_TAC (base:int) (x:term) (k:int) (st:term) =
  MP_TAC(SPECL [`rsp0:int64`; mk_small_numeral base; x; st; mk_small_numeral k] VM_SPLIT) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC;;



(* ------------------------------------------------------------------------- *)
(* The callees and the region lemmas, assumed before the template.           *)
(* ------------------------------------------------------------------------- *)

let VM_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* The loop test at the end of a row (loop11_exit): the index in RCX, the
   pointers to t1 (RBX) and to the packed w1 (R13) advanced, RSI the matrix
   structure again, and the branch back to join4, or past the end of the
   loop for the last row. Simulated as a region of its own, in a small
   context. *)
let VM_LT_STMT = parse_term(subst_tokens ["@MC@",image_mc]
 "exists f_events. forall e rsp0 pc i (tb:int64) (wp:int64).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\ i < 4
    ==> ensures x86
      (\\s. bytes_loaded s (word pc) @MC@ /\\
           read RIP s = word (pc + mldsa44_verify_internal_loop11_exit) /\\
           read RSP s = rsp0 /\\ read RCX s = word i /\\
           read RBX s = tb /\\ read R13 s = wp /\\
           read events s = e)
      (\\s. read RIP s = word (if i + 1 = 4 then pc + 30021
                              else pc + mldsa44_verify_internal_join4) /\\
           read RSP s = rsp0 /\\ read RCX s = word (i + 1) /\\
           read RBX s = word_add tb (word 320) /\\
           read R13 s = word_add wp (word 192) /\\
           read RSI s = word_add rsp0 (word 128) /\\
           (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc i /\\
              memaccess_inbounds e2 [] []))
      (MAYCHANGE [RIP; RCX; RBX; R13; RSI] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])");;

let VM_LT_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num) (i:num). f_ev_lt rsp0 pc i :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `i:num`;
                       `tb:int64`; `wp:int64`] THEN
  REWRITE_TAC[fst VM_EXEC; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC VM_EXEC (1--6) THEN
  SUBGOAL_THEN `val (word_add (word i) (word 18446744073709551613):int64) = 0 <=>
                i + 1 = 4`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `i < 4` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_CASES_TAC `i + 1 = 4` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let VM_LT = prove(VM_LT_STMT, VM_LT_TAC);;




(* a region lemma or callee at step n, with the arguments ilist after e *)
let VM_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,VM_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [VM_PRE_TAC VM_ALLOWED; LABEL_TAC name th]);;

(* The precondition aligned 16 (stackpointer + 8) of mld_H, with the stack
   pointer word_sub rsp0 (word 8) after the call, from aligned 32 rsp0 *)
let VM_H_ALIGN_TAC =
  VM_ALIGNED_TAC [] THEN
  SUBGOAL_THEN `aligned 16 (word_add (word_sub rsp0 (word 8)) (word 8):int64)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`];
    ALL_TAC];;

(* a callee called at step n - 1 *)
let VM_FCALL_TAC name ilist n =
  VM_CALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC;;


let VM_CALLEES_TAC =
  let [uz0;uz1;uz2;uz3] = VI44_UNPACKZ_LOOPS in
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    VM_ASSUME_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
      "H_CHKNORM" THEN
    VM_ASSUME_TAC MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
    VM_ASSUME_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
      "H_INV" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)
      "H_CHAL" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)
      "H_ROW" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) mcs)
      "H_H44" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL VI44_HINTS) ms) "H_HINTS" THEN
    VM_ASSUME_TAC uz0 "H_UZ0" THEN VM_ASSUME_TAC uz1 "H_UZ1" THEN
    VM_ASSUME_TAC uz2 "H_UZ2" THEN VM_ASSUME_TAC uz3 "H_UZ3" THEN
    VM_ASSUME_TAC VI44_UNPACKT1_LOOP "H_T1" THEN
    VM_ASSUME_TAC VI44_SHIFTL "H_SHL" THEN
    VM_ASSUME_TAC VI44_PWM_LOOP "H_PWM" THEN
    VM_ASSUME_TAC VI44_SUB_LOOP "H_SUB" THEN
    VM_ASSUME_TAC VI44_REDUCE_LOOP "H_RED" THEN
    VM_ASSUME_TAC VI44_CADDQ_LOOP "H_CADDQ" THEN
    VM_ASSUME_TAC VI44_USEHINT_LOOP "H_USEHINT" THEN
    VM_ASSUME_TAC VI44_PACKW1_LOOP "H_W1PACK" THEN
    VM_ASSUME_TAC VI44_CMP "H_CMP" THEN
    VM_ASSUME_TAC VI44_TR "H_TR" THEN
    VM_ASSUME_TAC VM_LT "H_LT");;

let VM_SETUP_TAC =
  REPEAT GEN_TAC THEN VM_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC VM_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `pre:int64`;
    `prelen:num`; `pk:int64`; `ext:int32`; `sigb:num->byte`; `pkb:num->byte`;
    `M:num`; `PRE':num`; `pc:num`; `rsp0:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              NONOVERLAPPING_CLAUSES; fst VM_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

(* ------------------------------------------------------------------------- *)
(* From loop1 to the return of the norm check, from state 0 to state 19: the *)
(* four polynomials of z (z at rsp0 + 4320), and the norm check of z.        *)
(* ------------------------------------------------------------------------- *)

let VM_Z = parse_term
  "mld_polyvec_unpack 576 mld_polyz_unpack_17 (\\j. (sigb:num->byte)(32 + j))";;

let VM_UZ_TAC k n =
  let off = 32 + 576 * k in
  let offt = mk_small_numeral off in
  VERIF_SLICE_TAC (subst [offt,`off:num`;
     mk_var("s"^string_of_int(n-1),`:x86state`),`s:x86state`]
    `!j. j < 576 ==> read(memory :> bytes8(word_add sig (word(off + j)))) s =
                     (sigb:num->byte)(off + j)`) THEN
  VM_CALL_TAC ("H_UZ"^string_of_int k)
   [subst [offt,`off:num`] `word_add sig (word off):int64`; `rsp0:int64`; `pc:num`;
    subst [offt,`off:num`] `\j. (sigb:num->byte)(off + j)`] n;;

let VM_UNPACK_TAC =
  VM_UZ_TAC 0 1 THEN
  X86_STEPS_TAC VM_EXEC (2--5) THEN VM_UZ_TAC 1 6 THEN
  X86_STEPS_TAC VM_EXEC (7--9) THEN VM_UZ_TAC 2 10 THEN
  X86_STEPS_TAC VM_EXEC (11--14) THEN VM_UZ_TAC 3 15 THEN
  X86_STEPS_TAC VM_EXEC (16--18) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `4320`)) (concl th) &&
       can (find_term ((=) `mld_polyz_unpack_17`)) (concl th)
    then ALL_TAC else NO_TAC) THEN
  W(fun (asl,w) ->
    let fs = filter (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `mld_polyz_unpack_17`)) (concl th))
                    (map snd asl) in
    let st = rand(lhs(snd(dest_imp(snd(dest_forall(concl(hd fs))))))) in
    MP_TAC(SPECL [`rsp0:int64`; `sigb:num->byte`; st] VM_VEC4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  VM_FCALL_TAC "H_CHKNORM" [`read RDI s`; VM_Z; `read RSI s`] 19;;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: join1 sets the result -6.                           *)
(* ------------------------------------------------------------------------- *)

let VM_NORMOK_TM = parse_term VM_NORMOK;;
let VM_OK_TM = parse_term VM_OK;;

let VM_OK_NORM = prove
 (`!sigb pkb mu.
     mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994
       mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 sigb pkb mu
     ==> mld_polyvec_chknorm 4
          (mld_polyvec_unpack 576 mld_polyz_unpack_17 (\j. sigb(32 + j)))
          (word 130994) = word 0`,
  REWRITE_TAC[mld_verify_internal_ok] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[]);;

let VM_BND_TAC =
  let tm = `word_zx (word 130994:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let VM_NOT_OK_TAC =
  SUBGOAL_THEN (mk_neg VM_OK_TM) (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN(MP_TAC o MATCH_MP VM_OK_NORM) THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let VM_NF_TAC =
  FULL_INIT_TAC THEN VM_UNPACK_TAC THEN VM_BND_TAC THEN
  X86_STEPS_TAC VM_EXEC (20--21) THEN VERIF_PC_TAC [VM_NORMOK_TM] THEN
  X86_STEPS_TAC VM_EXEC (22--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN VM_NOT_OK_TAC THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join3, where mu is ready at rsp0 + 1184.                     *)
(* ------------------------------------------------------------------------- *)

let VM_MU =
  `if ext = (word 0:int32)
   then mld_verify_mu 1312 pkb prelen PRE' mlen M else M MOD 2 EXP 512`;;

let VM_FRAME =
  "read RSP s = rsp0 /\\
   read (memory :> bytes64 (word_add rsp0 (word 56))) s = sig /\\
   read (memory :> bytes128 (word_add rsp0 (word 64))) s = mld_chunk128 sigb 0 /\\
   read (memory :> bytes128 (word_add rsp0 (word 80))) s = mld_chunk128 sigb 1 /\\
   (read DF s <=> false) /\\
   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
   read (memory :> bytes(ea,el)) s = ev /\\
   (!j. j < 2420 ==> read(memory :> bytes8(word_add sig (word j))) s = sigb j) /\\
   (!j. j < 1312 ==> read(memory :> bytes8(word_add pk (word j))) s = pkb j)";;

let VM_J3 =
  subst [VM_Z,`VMZ:num->int32`; VM_MU,`VMMU:num`]
  (parse_term ("\\s. " ^ VM_FRAME ^ " /\\
     read RBX s = pk /\\ read R14 s = word_add rsp0 (word 5344) /\\
     (!i. i < 1024 ==> read (memory :> bytes32 (word_add rsp0 (word (4320 + 4 * i)))) s =
                       VMZ i) /\\
     read (memory :> bytes (word_add rsp0 (word 1184),64)) s = VMMU"));;


let VM_COPY_TAC =
  FULL_INIT_TAC THEN VM_M_CHUNKS_TAC THEN VM_ALIGNED_TAC [1184; 1200; 1216; 1232] THEN
  VM_UNPACK_TAC THEN VM_BND_TAC THEN
  X86_STEPS_TAC VM_EXEC (20--21) THEN VERIF_PC_TAC [VM_NORMOK_TM] THEN
  X86_STEPS_TAC VM_EXEC (22--23) THEN VM_EXT_PC_TAC THEN
  YMM_GHOST_TAC `s23:x86state`
   ["YMM0","ymm0_23"; "YMM1","ymm1_23"; "YMM2","ymm2_23"; "YMM3","ymm3_23"] THEN
  X86_STEPS_TAC VM_EXEC (24--32) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_MU_OF_CHUNKS_TAC `word_add rsp0 (word 1184):int64` `s32:x86state` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;


(* ------------------------------------------------------------------------- *)
(* ext = 0: tr = SHAKE256(pk) (the region TR, then the 64 bytes of the state *)
(* copied to rsp0 + 3296 and the state zeroed), and mu = H(tr, pre, m) by a  *)
(* call of mld_H44 (steps 24 to 75).                                         *)
(* ------------------------------------------------------------------------- *)

let VM_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 1312)`;;

let VM_TRNUM = subst [VM_PKNUM,`p:num`]
  `num_of_bytelist (list_of_seq (mld_shake256_byte 1312 p) 64)`;;

(* the chunks of the state loaded from rsp0 + 128 + 16 k, k < 4, in state st *)
let VM_TR_CHUNKS_TAC st =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> wbytes (word_add rsp0 (word 128))) s = x`)
           (concl th)
    then MAP_EVERY (fun k ->
           MP_TAC(SPECL [`word_add rsp0 (word 128):int64`; rhs(concl th);
                         mk_small_numeral k; st] READ_MEMORY_BYTES128_OF_WBYTES) THEN
           ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC th; ARITH_TAC]; ALL_TAC] THEN
           MP_TAC(SPECL [`1312`; VM_PKNUM; mk_small_numeral k] VM_TR_CHUNK) THEN
           ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
           CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
           REWRITE_TAC[WORD_ADD_0; EXP; DIV_1] THEN DISCH_TAC) [0;1;2;3]
    else NO_TAC);;

let VM_TR_OF_CHUNKS_TAC s =
  MP_TAC(SPECL [`word_add rsp0 (word 3296):int64`; VM_TRNUM; `4`; s]
               VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VM_SHAKE_BYTES; MOD_MOD_REFL]);;

let VM_HASH_TAC =
  FULL_INIT_TAC THEN
  VM_ALIGNED_TAC [128; 144; 160; 176; 192; 208; 224; 240; 256; 272; 288; 304; 320;
                  3296; 3312; 3328; 3344] THEN
  VM_UNPACK_TAC THEN VM_BND_TAC THEN
  X86_STEPS_TAC VM_EXEC (20--21) THEN VERIF_PC_TAC [VM_NORMOK_TM] THEN
  X86_STEPS_TAC VM_EXEC (22--23) THEN VM_EXT_PC_TAC THEN
  MP_TAC(SPECL [`pk:int64`; `1312`; `pkb:num->byte`; `s23:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  VM_CALL_TAC "H_TR" [`rsp0:int64`; `pk:int64`; `pc:num`; VM_PKNUM] 24 THEN
  VM_TR_CHUNKS_TAC `s24:x86state` THEN
  YMM_GHOST_TAC `s24:x86state`
   ["YMM0","ymm0_24"; "YMM1","ymm1_24"; "YMM2","ymm2_24"; "YMM3","ymm3_24"] THEN
  X86_STEPS_TAC VM_EXEC (25--69) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_TR_OF_CHUNKS_TAC `s69:x86state` THEN
  VM_H_ALIGN_TAC THEN
  VM_FCALL_TAC "H_H44"
   [`read RDI s`; `64`; `read RDX s`; `64`; `read R8 s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    subst [VM_PKNUM,`p:num`]
     `val(keccak_f1600 (mld_shake256_state 1312 p)) MOD 2 EXP 512`;
    `PRE':num`; `M:num`] 70 THEN
  X86_STEPS_TAC VM_EXEC (71--75) THEN
  REWRITE_TAC[mld_verify_mu; SPEC `1312` VM_SHAKE_BYTES] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2 EXP (8 * 64)` (concl th)
    then REWRITE_RULE[ARITH_RULE `8 * 64 = 512`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The values of the code (as in the gcc proof): rho, zhat, c, cphat, row i  *)
(* of w1' and its packing.                                                   *)
(* ------------------------------------------------------------------------- *)

let VM_ZHAT = mk_comb(`mld_polyvec_map mld_poly_ntt`,VM_Z);;
let VM_C = `num_of_bytelist (list_of_seq (sigb:num->byte) 32)`;;
let VM_CP = mk_comb(`mld_poly_challenge 39 32`,VM_C);;
let VM_CPHAT = mk_comb(`mld_poly_ntt`,VM_CP);;

let VM_PWM = list_mk_comb(`mld_poly_pointwise_montgomery`,[VM_NTT1;VM_CPHAT]);;
let VM_ROWL =
  subst [VM_RHO,`rho:num`; VM_ZHAT,`zhat:num->int32`]
   `mld_polyvec_matrix_row_lazy 4 rho zhat i`;;
let VM_SUBL = list_mk_comb(`mld_poly_sub`,[VM_ROWL;VM_PWM]);;
let VM_REDL = mk_comb(`mld_poly_reduce`,VM_SUBL);;
let VM_INVTL = mk_comb(`mld_poly_invntt_tomont`,VM_REDL);;
let VM_CADDQL = mk_comb(`mld_poly_caddq`,VM_INVTL);;
let VM_HB = `\t. (sigb:num->byte) (2336 + t)`;;
let VM_HINTS = `mld_unpack_hints 80 (\t. (sigb:num->byte) (2336 + t)) i`;;

let VM_W1B =
  subst [VM_RHO,`rho:num`; VM_ZHAT,`zhat:num->int32`;
         VM_CPHAT,`cphat:num->int32`]
   `mld_polyvec_pack 192 mld_polyw1_pack_88
     (mld_polyvec
       (mld_verify_w1 4 mld_poly_use_hint_88 rho zhat cphat pkb 80
         (\t. (sigb:num->byte) (2336 + t))))`;;

(* ------------------------------------------------------------------------- *)
(* From join3 to join4: the NTT of the 4 polynomials of z, rho copied to the *)
(* structure of the matrix, the challenge from c~ and its NTT.               *)
(* ------------------------------------------------------------------------- *)

let VM_INV =
  subst [VM_MU,`VMMU:num`; VM_W1B,`VMW1B:num->byte`; VM_RHO,`VMRHO:num`;
         VM_ZHAT,`VMZHAT:num->int32`; VM_CPHAT,`VMCPHAT:num->int32`]
  (parse_term ("\\i s. " ^ VM_FRAME ^ " /\\
     read R12 s = word 0x0380200100000000 /\\
     read (memory :> bytes (word_add rsp0 (word 1152),32)) s = VMRHO /\\
     (!j. j < 1024 ==> read (memory :> bytes32 (word_add rsp0 (word (4320 + 4 * j)))) s =
                       VMZHAT j) /\\
     (!j. j < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (3296 + 4 * j)))) s =
                      VMCPHAT j) /\\
     read (memory :> bytes (word_add rsp0 (word 1184),64)) s = VMMU /\\
     ((!j. j < i ==> " ^ "mld_unpack_hints_ok 80 4 (\\t. sigb(2336 + t)) j" ^ ")
      ==> read RCX s = word i /\\
          read R14 s = word_add rsp0 (word 2272) /\\
          read R15 s = word_add rsp0 (word 4320) /\\
          read RSI s = word_add rsp0 (word 128) /\\
          read R13 s = word_add rsp0 (word (8418 + 192 * i)) /\\
          read RBX s = word_add pk (word (33 + 320 * i)) /\\
          (!j. j < 192 * i
               ==> read (memory :> bytes8 (word_add rsp0 (word (8416 + j)))) s =
                   VMW1B j))"));;

let VM_PC2 =
  parse_term("if " ^ VM_HINTSOK ^
             " then pc + " ^ string_of_int (layout "mldsa44_verify_internal" + 0x1995) ^
             " else pc + mldsa44_verify_internal_join1");;

let VM_MID_TAC =
  FULL_INIT_TAC THEN VM_ALIGNED_TAC [1152; 1168] THEN
  MAP_EVERY (fun k -> VM_SPLIT_TAC 4320 VM_Z k `s0:x86state`) [0;1;2;3] THEN
  X86_STEPS_TAC VM_EXEC (1--4) THEN
  VM_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,VM_Z),`0`)] 5 THEN
  X86_STEPS_TAC VM_EXEC (6--7) THEN
  VM_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,VM_Z),`1`)] 8 THEN
  X86_STEPS_TAC VM_EXEC (9--10) THEN
  VM_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,VM_Z),`2`)] 11 THEN
  X86_STEPS_TAC VM_EXEC (12--13) THEN
  VM_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,VM_Z),`3`)] 14 THEN
  VM_JOIN_TAC 4320 (mk_abs(`k:num`,mk_comb(`mld_poly_ntt`,
                     mk_comb(mk_comb(`mld_poly_of`,VM_Z),`k:num`)))) `s14:x86state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_polyvec_map]) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`pk:int64`; `1312`; `pkb:num->byte`; `s14:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1] THEN
  YMM_GHOST_TAC `s14:x86state` ["YMM0","ymm0_14"; "YMM1","ymm1_14"] THEN
  X86_STEPS_TAC VM_EXEC (15--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  MP_TAC(SPECL [`word_add rsp0 (word 1152):int64`; `pkb:num->byte`; `s22:x86state`]
               MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`word_add rsp0 (word 64):int64`; `sigb:num->byte`; `s22:x86state`]
               MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  VM_FCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; VM_C] 23 THEN
  X86_STEPS_TAC VM_EXEC (24--26) THEN
  VM_FCALL_TAC "H_NTT" [`read RDI s`; VM_CP] 27 THEN
  X86_STEPS_TAC VM_EXEC (28--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body for row i (as in the gcc proof, VI44_BODY_TAC), with the    *)
(* region lemmas in place of the callees that clang has inlined.             *)
(* ------------------------------------------------------------------------- *)

let VM_ACC =
  subst [VM_RHO,`rho:num`; VM_ZHAT,`zhat:num->int32`]
   `mld_polyvec_pointwise_acc_montgomery 4
     (\j. mld_polyvec_matrix_expand 4 rho (1024 * i + j)) zhat`;;
let VM_SUB = list_mk_comb(`mld_poly_sub`,[VM_ACC;VM_PWM]);;
let VM_RED = mk_comb(`mld_poly_reduce`,VM_SUB);;
let VM_INVT = mk_comb(`mld_poly_invntt_tomont`,VM_RED);;
let VM_CADDQ = mk_comb(`mld_poly_caddq`,VM_INVT);;
let VM_UH = list_mk_comb(`mld_poly_use_hint_88`,[VM_CADDQ;VM_HINTS]);;
let VM_HOK_TM = parse_term VM_HOK;;
let VM_HINTSOK_TM = parse_term VM_HINTSOK;;

let VM_ZHAT_BOUND =
  subst [VM_ZHAT,`zhat:num->int32`]
   `!j. j < 1024 ==> abs(ival((zhat:num->int32) j)) < &94279689`;;

let VM_ZHAT_BOUND_TAC =
  SUBGOAL_THEN VM_ZHAT_BOUND ASSUME_TAC THENL
   [MP_TAC(SPECL [`4`; VM_Z] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_Z_UNPACK_BOUND];
    ALL_TAC];;

let VM_CADDQ_TAC =
  FIRST_ASSUM(fun th ->
    if not(is_forall(concl th)) ||
       not(can (find_term ((=) VM_CADDQL)) (concl th))
    then failwith "VM_CADDQ_TAC" else
    SUBGOAL_THEN (subst [VM_CADDQ,VM_CADDQL] (concl th)) ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun nth -> REWRITE_TAC[MP (SPEC `n:num` th) nth] THEN
                            ASSUME_TAC nth) THEN
      MP_TAC(SPECL [`4`; `4`; VM_RHO; VM_ZHAT; VM_PWM; `i:num`; `n:num`]
                   MLD_LAZY_VERIFY) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MLD_LAZY_POINTWISE_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[]];
      ALL_TAC]);;

let VM_ROWS_TAC =
  MP_TAC(BETA_RULE(SPECL [mk_abs(`i:num`,VM_HOK_TM); `4`; `i:num`]
                         VERIF_ROWS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(lhand(concl th)) &&
    fst(dest_forall(lhand(concl th))) = `j:num`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;


(* a region lemma or callee in the loop body, where the pre may need a word
   equation of a register (by WORD_RULE from its value) *)
let VM_LCALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,VM_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [VM_PRE_TAC VM_ALLOWED_LOOP; LABEL_TAC name th]);;

let VM_LFCALL_TAC name ilist n =
  VM_LCALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC;;

(* The constants that the row body loads from the image by RIP-relative
   loads, for IMAGE_RIPREL_TAC: the two 64-bit vectors of the unpacking of
   t1 (movq) and the two 128-bit vectors of the reduction (loop8, aligned
   movdqa). *)
let VM_CONSTS64 =
  map (fun n -> IMAGE_CONST_RULE_FOR VM_MC (layout n) 64)
   ["mldsa44_verify_internal_const3"; "mldsa44_verify_internal_const4"];;

let VM_CONSTS128 =
  map (fun n -> IMAGE_CONST_RULE_FOR VM_MC (layout n) 128)
   ["mld_compute_pack_t0_t144_const1"; "mld_compute_pack_t0_t144_const2"];;


let VM_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  VERIF_GEN_TAIL_TAC false "front" THEN
  FULL_INIT_TAC THEN VM_ROWS_TAC THEN
  VM_ALIGNED_TAC [128; 1248; 2272; 3296; 4320] THEN
  X86_STEPS_TAC VM_EXEC (1--4) THEN
  VM_LFCALL_TAC "H_ROW"
   [`read RDI s`; `read RSI s`; `read RDX s`; VM_RHO; VM_ZHAT; `i:num`] 5 THEN
  YMM_GHOST_TAC `s5:x86state`
   ["YMM2","ymm2_5"; "YMM3","ymm3_5"; "YMM4","ymm4_5"] THEN
  IMAGE_RIPREL_TAC (el 1 VM_CONSTS64) (layout "mldsa44_verify_internal" + 0xf6e) THEN
  X86_STEPS_TAC VM_EXEC (6--6) THEN
  IMAGE_RIPREL_TAC (el 0 VM_CONSTS64) (layout "mldsa44_verify_internal" + 0xf76) THEN
  X86_STEPS_TAC VM_EXEC (7--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_SLICE_TAC
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word((32 + 320 * i) + j)))) s11 =
            (pkb:num->byte)(32 + 320 * i + j)` THEN
  VM_LCALL_TAC "H_T1"
   [`word_add pk (word(32 + 320 * i)):int64`; `rsp0:int64`; `pc:num`;
    `\j. (pkb:num->byte)(32 + 320 * i + j)`] 12 THEN
  VM_LCALL_TAC "H_SHL" [`rsp0:int64`; `pc:num`; VM_T1] 13 THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = word x`) (concl th)
    then CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th else th) THEN
  X86_STEPS_TAC VM_EXEC (14--15) THEN
  VM_LFCALL_TAC "H_NTT" [`read RDI s`; VM_SHL] 16 THEN
  X86_STEPS_TAC VM_EXEC (17--18) THEN
  VM_LCALL_TAC "H_PWM" [`rsp0:int64`; `pc:num`; VM_NTT1; VM_CPHAT] 19 THEN
  YMM_GHOST_TAC `s19:x86state` ["YMM5","ymm5_19"; "YMM6","ymm6_19"] THEN
  X86_STEPS_TAC VM_EXEC (20--20) THEN
  IMAGE_RIPREL_TAC (el 0 VM_CONSTS128) (layout "mldsa44_verify_internal" + 0x1641) THEN
  X86_STEPS_TAC VM_EXEC (21--21) THEN
  IMAGE_RIPREL_TAC (el 1 VM_CONSTS128) (layout "mldsa44_verify_internal" + 0x1649) THEN
  X86_STEPS_TAC VM_EXEC (22--23) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_LCALL_TAC "H_SUB" [`rsp0:int64`; `pc:num`; VM_ROWL; VM_PWM] 24 THEN
  X86_STEPS_TAC VM_EXEC (25--26) THEN
  VM_LCALL_TAC "H_RED" [`rsp0:int64`; `pc:num`; VM_SUBL] 27 THEN
  X86_STEPS_TAC VM_EXEC (28--29) THEN
  VM_LFCALL_TAC "H_INV" [`read RDI s`; VM_REDL] 30 THEN
  X86_STEPS_TAC VM_EXEC (31--32) THEN
  VM_LCALL_TAC "H_CADDQ" [`rsp0:int64`; `pc:num`; VM_INVTL] 33 THEN
  VM_CADDQ_TAC THEN
  VM_SLICE_TAC
   `!j. j < 84
        ==> read(memory :> bytes8(word_add sig (word(2336 + j)))) s33 =
            (sigb:num->byte)(2336 + j)` THEN
  VM_LCALL_TAC "H_HINTS"
   [`sig:int64`; `rsp0:int64`; `pc:num`; VM_HB; `i:num`;
    `word_add rsp0 (word 4320):int64`; `word_add pk (word(33 + 320 * i)):int64`] 34;;

let VM_PC_OK_TAC =
  ASM_CASES_TAC `i + 1 < 4` THENL
   [SUBGOAL_THEN `~(i + 1 = 4)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i + 1 < 4`; ASSUME `~(i + 1 = 4)`];
    SUBGOAL_THEN `i + 1 = 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN VM_HINTSOK_TM ASSUME_TAC THENL
     [VERIF_IMP_CASE_TAC `~(i + 1 < 4)`; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~(i + 1 < 4)`; ASSUME `i + 1 = 4`;
                ASSUME VM_HINTSOK_TM]];;

let VM_JOIN_W1_TAC =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[MATCH_MP (SPEC_ALL VERIF_W1B_ROW_88) (ASSUME `k < 192`)] THEN
    REWRITE_TAC[mld_verify_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(fun th ->
      MATCH_MP_TAC(REWRITE_RULE[GSYM ADD_ASSOC] th)) THEN
    FIRST_ASSUM ACCEPT_TAC];;

let VM_BODY_OK_TAC =
  VERIF_MP_CASE_TAC VM_HOK_TM THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  VM_LCALL_TAC "H_USEHINT" [`rsp0:int64`; `pc:num`; VM_CADDQ; VM_HINTS] 35 THEN
  X86_STEPS_TAC VM_EXEC (36--38) THEN
  VM_LCALL_TAC "H_W1PACK"
   [`word_add rsp0 (word 2272):int64`; `word_add rsp0 (word (8416 + 192 * i)):int64`;
    `pc:num`; VM_UH] 39 THEN
  VM_LCALL_TAC "H_LT"
   [`rsp0:int64`; `pc:num`; `i:num`; `word_add pk (word (33 + 320 * i)):int64`;
    `word_add rsp0 (word (8418 + 192 * i)):int64`] 40 THEN
  VERIF_FINAL_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(VM_PC_OK_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN VM_JOIN_W1_TAC THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN
  VM_EVENTS_TAC [`front:(uarch_event)list`];;

let VM_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg VM_HOK_TM) THEN VERIF_FINAL_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg VM_HOK_TM)] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN
  VM_EVENTS_TAC [`front:(uarch_event)list`];;

let VM_BODY_TAC =
  VM_BODY1_TAC THEN
  ASM_CASES_TAC VM_HOK_TM THEN VERIF_PC_TAC [VM_HOK_TM] THENL
   [VM_BODY_OK_TAC; VM_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop. All hints unpack: c2 = H(mu, w1') (mld_H44, 32 bytes at   *)
(* rsp0 + 96), and the comparison of c~ and c2 (the region CMP). Some do     *)
(* not: join1 sets -6.                                                       *)
(* ------------------------------------------------------------------------- *)


let VM_OK_THM = GEN_ALL(prove
 (subst [VM_W1B,`w1b:num->byte`]
  `mld_verify_internal_ok 4 4 32 mld_polyz_unpack_17 576 130994
       mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39 (sigb:num->byte)
       (pkb:num->byte) mu <=>
     mld_polyvec_chknorm 4
       (mld_polyvec_unpack 576 mld_polyz_unpack_17 (\j. sigb(32 + j)))
       (word 130994) = word 0 /\
     (!i. i < 4 ==> mld_unpack_hints_ok 80 4 (\t. sigb(2336 + t)) i) /\
     (!j. j < 32
          ==> sigb j =
              mld_shake256_byte 832
               (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b 768)) j)`,
  REWRITE_TAC[mld_verify_internal_ok; VM_HRET] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `32 + 4 * 576 + t = 2336 + t`;
              ARITH_RULE `64 + 4 * 192 = 832`; ARITH_RULE `4 * 192 = 768`]));;

let VM_W1NUM =
  mk_comb(`num_of_bytelist`,
          mk_comb(mk_comb(`list_of_seq:(num->byte)->num->byte list`,VM_W1B),
                  `768`));;

let VM_SQ = subst [VM_MU,`mu:num`; VM_W1NUM,`w:num`]
  `mld_shake256_byte 832 (mu + 2 EXP 512 * w)`;;


let VM_POST_OK_TAC =
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`word_add rsp0 (word 8416):int64`; `768`; VM_W1B; `s0:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_88`)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  VERIF_NULL_TAC [`word_add rsp0 (word 96):int64`,`32`;
                  `word_sub rsp0 (word 584):int64`,`576`] THEN
  YMM_GHOST_TAC `s0:x86state` ["YMM0","ymm0_0"] THEN
  X86_STEPS_TAC VM_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_SPLIT128_TAC `rsp0:int64` `s10:x86state` THEN
  VM_H_ALIGN_TAC THEN
  VM_FCALL_TAC "H_H44"
   [`read RDI s`; `32`; `read RDX s`; `64`; `read R8 s`; `768`;
    `word 0:int64`; `0`; VM_MU; VM_W1NUM; `0`] 11 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES;
    ARITH_RULE `64 + 768 = 832`; ARITH_RULE `8 * 64 = 512`]) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(word_add rsp0 (word 96),32)) (s:x86state) = n`)
           (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`word_add rsp0 (word 96):int64`; `32`; VM_SQ; `s11:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    DISCH_TAC) [0;1] THEN
  VM_ALIGNED_TAC [64; 96] THEN
  VM_CALL_TAC "H_CMP"
   [`rsp0:int64`; `pc:num`; `mld_chunk128 sigb 0`; `mld_chunk128 sigb 1`;
    mk_comb(mk_comb(`mld_chunk128`,VM_SQ),`0`);
    mk_comb(mk_comb(`mld_chunk128`,VM_SQ),`1`)] 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VM_OK_THM; ASSUME VM_NORMOK_TM; EQT_INTRO(ASSUME VM_HINTSOK_TM)] THEN
  MP_TAC(ISPECL [`sigb:num->byte`; VM_SQ; `2`] MLD_CHUNK128_EQ) THEN
  CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
  REWRITE_TAC[ARITH_RULE `16 * 2 = 32`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN VM_EVENTS_TAC [`old:(uarch_event)list`];;

let VM_POST_HF_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC VM_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VM_OK_THM] THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN VM_EVENTS_TAC [`old:(uarch_event)list`];;

let VM_POST_TAC =
  VERIF_GEN_TAIL_TAC true "old" THEN
  ASM_CASES_TAC VM_HINTSOK_TM THENL
   [REWRITE_TAC[EQT_INTRO(ASSUME VM_HINTSOK_TM); ARITH_RULE `0 < 4`] THEN
    VM_POST_OK_TAC;
    REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg VM_HINTSOK_TM))] THEN
    VM_POST_HF_TAC];;

(* ------------------------------------------------------------------------- *)
(* The body as a whole.                                                      *)
(* ------------------------------------------------------------------------- *)

let VM_MAIN_TAC =
  VM_SETUP_TAC THEN VM_ZHAT_BOUND_TAC THEN
  ASM_CASES_TAC VM_NORMOK_TM THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[if is_neg(concl th) then th else EQT_INTRO th]) THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term VM_K)
     `pc + mldsa44_verify_internal_join4` VM_PC2 VM_INV THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                  CONJUNCT1 LT; LT_REFL] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa44_verify_internal_join3` VM_J3 THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC `ext = (word 0:int32)` THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[if is_neg(concl th) then th else EQT_INTRO th]) THEN
        FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM VAL_EQ_0] o
                      check (fun th -> concl th = `ext = (word 0:int32)` ||
                                       concl th = `~(ext = (word 0:int32))`)) THENL
         [VM_HASH_TAC; VM_COPY_TAC];
        VM_MID_TAC];
      VM_BODY_TAC;
      VM_POST_TAC];
    VM_NF_TAC];;

let VI44_MAIN = prove(VM_STMT, VM_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)


let VI44_TOP_CALL_TAC name ilist n =
  FULL_CALL_TAC VM_MC VM_EXEC name ilist VI44_TOP_ALLOWED n;;


let VI44_TOP_A0_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPEC_ALL VI44_MAIN) th) "H_MAIN" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPEC_ALL VI44_CLEANUP) (CONJUNCT1 th))
      "H_CL") THEN
  CONCRETIZE_F_EVENTS_TAC VI44_TOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst VM_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 10901 THEN REALIGN_FRAME_TAC 10949 10901 THEN
  REALIGN_NONOV_TAC 10870
   [`sig:int64,2420`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `pk:int64,1312`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 10901):int64,48`;
    `word_add stackpointer (word 10949):int64,8`;
    `word_add stackpointer (word 10957):int64,4`] THEN
  REALIGN_ALIGNED_TAC [1718; 1734] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word k))
                            (word 18446744073709551584):int64 = x`) (concl th)
    then ASSUME_TAC(MATCH_MP (MESON[ALIGNED_WORD_SUB; ALIGNED_WORD_ADD]
                                `aligned 32 (x:int64) ==> aligned 32 x`)
                     (REWRITE_RULE[th] (SPEC (lhand(lhs(concl th))) REALIGN_ALIGNED_AND)))
    else NO_TAC) THEN
  SUBGOAL_THEN `aligned 32 (word_add bot (word 1654):int64)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if can (term_match [] `aligned 32 (word_add bot (word n):int64)`) (concl th)
      then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[WORD_RULE `word_add bot (word 10870):int64 =
                           word_add (word_add bot (word 1654)) (word 9216)`] THEN
    MATCH_MP_TAC VI44_ALIGNED32_LEMMA THEN
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV DIVIDES_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let VI44_TOP_A1_TAC =
  FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes32 a) s0 = ext`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th) THEN
  YMM_GHOST_TAC `s0:x86state` ["YMM0","ymm0_0"; "YMM1","ymm1_0"] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `2420`; `sigb:num->byte`; `s0:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1] THEN
  X86_STEPS_TAC VM_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  MAP_EVERY (fun k ->
    SUBGOAL_THEN (subst [mk_small_numeral k,`k:num`]
      `aligned 16 (word_add (word_add bot (word 1654)) (word k):int64)`)
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC]) [64;80] THEN
  X86_STEPS_TAC VM_EXEC (9--27) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]);;

let VI44_TOP_B_TAC =
  VI44_TOP_CALL_TAC "H_MAIN"
   [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`; `pk:int64`;
    `ext:int32`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `PRE':num`;
    `pc:num`; VI44_RSP0] 28;;

let VI44_TOP_C_TAC =
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                      `word_add bot (word 1646):int64,9224`),r))
     ASSUME_TAC THENL
     [EXPAND_TAC "bot" THEN NONOVERLAPPING_TAC; ALL_TAC])
   [`word pc:int64,libmldsa_size`; `word(pc + got_memset):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 10901):int64,56`] THEN
  VI44_TOP_CALL_TAC "H_CL"
   [VI44_RSP0; `word_add stackpointer (word 10901):int64`; `read R14 s`; `pc:num`;
    `rbx_init:int64`; `r12_init:int64`; `r13_init:int64`; `r14_init:int64`;
    `r15_init:int64`; `rbp_init:int64`; `returnaddress:int64`] 29 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let VI44_TOP_TAC = VI44_TOP_A0_TAC THEN VI44_TOP_A1_TAC THEN VI44_TOP_B_TAC THEN VI44_TOP_C_TAC;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  VI44_TOP_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
