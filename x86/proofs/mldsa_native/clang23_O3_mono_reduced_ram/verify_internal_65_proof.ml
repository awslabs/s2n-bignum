(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature, ML-DSA-65: the proof (see                    *)
(* verify_internal_65_spec.ml). It is that of verify_internal_44_proof.ml    *)
(* with the parameters of ML-DSA-65 (K = 6, l = 5, 48 bytes of c~, the       *)
(* unpacking of z for gamma1 = 2^19, use_hint and the packing of w1 for      *)
(* gamma2 = (q - 1) / 32) and the frame and registers of the clang code:     *)
(*                                                                           *)
(*   c~ (copied)    rsp0 + 1120     mu  rsp0 + 1248     rho  rsp0 + 1088     *)
(*   the matrix     rsp0 + 64 (and the Keccak state for tr)                  *)
(*   t1, hints      rsp0 + 1312     w  rsp0 + 2336      cp   rsp0 + 3360     *)
(*   w1 (packed)    rsp0 + 4384     z  rsp0 + 5152 + 1024 k, k = 0..4        *)
(*                                                                           *)
(* VI65_MAIN is the body, from loop1 to join2, with the result in R14, and   *)
(* the whole function is the prologue, VI65_MAIN and the zeroing at the end  *)
(* (VI65_CLEANUP), as for 44. The row index is in R13 and the pointer to the *)
(* packed w1 in R15 (44: RCX and R13).                                       *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_65_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_tools.ml";;

(* ------------------------------------------------------------------------- *)
(* The body, from loop1 to join2.                                            *)
(* ------------------------------------------------------------------------- *)

let V6_FN = "mldsa65_verify_internal";;
let v6_off n = layout V6_FN + n;;

let V6_HOK = "mld_unpack_hints_ok 55 6 (\\t. sigb(3248 + t)) i";;

let V6_HINTSOK = "(!i. i < 6 ==> " ^ V6_HOK ^ ")";;

let V6_K =
  "(if " ^ V6_HINTSOK ^ " then 6 else (minimal i. ~(" ^ V6_HOK ^
  ")) + 1)";;

let V6_NORMOK =
  "mld_polyvec_chknorm 5 (mld_polyvec_unpack 640 mld_polyz_unpack_19 " ^
  "(\\j. sigb(48 + j))) (word 524092) = word 0";;

let V6_OK =
  "mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092 " ^
  "mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 sigb pkb " ^
  "(if ext = (word 0:int32) " ^
  "then mld_verify_mu 1952 pkb prelen PRE' mlen M else M MOD 2 EXP 512)";;

let V6_TEMPLATE_CASE =
  let f n = "(f_ev_" ^ n ^ " " ^ VM_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ " " ^ VM_ARGS ^ " i)" in
  "(if " ^ V6_NORMOK ^ " then " ^
  "APPEND (if " ^ V6_HINTSOK ^ " then " ^ f "post" ^ " else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ V6_K ^ " (\\i. if " ^ V6_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ")";;

let V6_TEMPLATE =
  parse_term(VM_LAMBDA ^ " " ^ V6_TEMPLATE_CASE ^ " :(uarch_event)list");;

let V6_READS =
  "[sig,3309; m,mlen; pre,prelen; pk,1952;
    word_sub rsp0 (word 1654),11958;
    word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
    word(pc + rodata_mld_zetas),1024;
    word(pc + mldsa65_poly_challenge_consts),48;
    word(pc + rodata_mld_KeccakF_RoundConstants),192;
    word(pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
    word(pc + mldsa65_verify_internal_consts),784]";;

let V6_STMT =
  parse_term(subst_tokens ["@MC@",image_mc; "@READS@",V6_READS]
  "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc rsp0.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          mlen < 2 EXP 64 /\\ prelen < 2 EXP 64 /\\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\\
          aligned 32 rsp0 /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1654),11958))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + mldsa65_verify_internal_loop1) /\\
                    read RSP s = rsp0 /\\
                    read RAX s = word_add sig (word 52) /\\ read RCX s = word 0 /\\
                    read RDI s = sig /\\ read R12 s = m /\\ read R13 s = word mlen /\\
                    read R14 s = word prelen /\\
                    read RBX s = pk /\\ read R15 s = word_zx ext /\\
                    read (memory :> bytes64 (word_add rsp0 (word 1176))) s = pre /\\
                    read (memory :> bytes128 (word_add rsp0 (word 1120))) s =
                      mld_chunk128 sigb 0 /\\
                    read (memory :> bytes128 (word_add rsp0 (word 1136))) s =
                      mld_chunk128 sigb 1 /\\
                    read (memory :> bytes128 (word_add rsp0 (word 1152))) s =
                      mld_chunk128 sigb 2 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s = sigb j) /\\
                    read (memory :> bytes(m,mlen)) s = M /\\
                    read (memory :> bytes(pre,prelen)) s = PRE /\\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s = pkb j) /\\
                    read events s = e)
               (\\s. read RIP s = word (pc + mldsa65_verify_internal_join2) /\\
                    read RSP s = rsp0 /\\
                    read R14 s =
                    (if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 1952 pkb prelen PRE mlen M
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
                        [word_sub rsp0 (word 1654),11958]))
               (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1654),11958)])");;

(* ------------------------------------------------------------------------- *)
(* The z vector as the code unpacks it, polynomial by polynomial, at         *)
(* rsp0 + 5152.                                                              *)
(* ------------------------------------------------------------------------- *)

let V6_VEC5 = prove
 (`!(r:int64) (sigb:num->byte) (s:x86state).
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(5152 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(48 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(6176 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(688 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(7200 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(1328 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(8224 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(1968 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(9248 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(2608 + j)) i)
     ==> !i. i < 1280
             ==> read(memory :> bytes32(word_add r (word(5152 + 4 * i)))) s =
                 mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(48 + j)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  SUBGOAL_THEN `i = 256 * (i DIV 256) + i MOD 256 /\ i MOD 256 < 256 /\ i DIV 256 < 5`
   MP_TAC THENL
   [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = i DIV 256` THEN ABBREV_TAC `t = i MOD 256` THEN
  REWRITE_TAC[ARITH_RULE `q < 5 <=> q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `i:num`
                          then SUBST1_TAC th else NO_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let V6_SPLIT = prove
 (`!(r:int64) base (x:num->int32) (s:x86state) k.
     (!i. i < 1280 ==> read(memory :> bytes32(word_add r (word(base + 4 * i)))) s = x i) /\
     k < 5
     ==> !i. i < 256
             ==> read(memory :> bytes32(word_add r (word((base + 1024 * k) + 4 * i)))) s =
                 mld_poly_of x k i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * k + i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `base + 4 * (256 * k + i) = (base + 1024 * k) + 4 * i`]);;

let V6_JOIN = prove
 (`!(r:int64) base (f:num->num->int32) (s:x86state).
     (!k i. k < 5 /\ i < 256
            ==> read(memory :> bytes32(word_add r (word((base + 1024 * k) + 4 * i)))) s =
                f k i)
     ==> !i. i < 1280
             ==> read(memory :> bytes32(word_add r (word(base + 4 * i)))) s =
                 mld_polyvec f i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(base + 1024 * i DIV 256) + 4 * i MOD 256 = base + 4 * i`
   (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC);;

let V6_JOIN_TAC (base:int) (f:term) (st:term) =
  MP_TAC(SPECL [`rsp0:int64`; mk_small_numeral base; f; st] V6_JOIN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k < 5 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4`] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC];;

let V6_SPLIT_TAC (base:int) (x:term) (k:int) (st:term) =
  MP_TAC(SPECL [`rsp0:int64`; mk_small_numeral base; x; st; mk_small_numeral k] V6_SPLIT) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC;;

(* 48 bytes from three chunks *)
let V6_BYTES48_OF_CHUNKS = prove
 (`!a:int64 (f:num->byte) s.
        read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
        read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1 /\
        read (memory :> bytes128 (word_add a (word 32))) s = mld_chunk128 f 2
        ==> read (memory :> bytes(a,48)) s = num_of_bytelist(list_of_seq f 48)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `f:num->byte`; `s:x86state`] MLD_BYTES32_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int128->num` o
    check (fun th -> can (find_term ((=) `2`)) (concl th))) THEN
  REWRITE_TAC[VAL_MLD_CHUNK128; BYTES128_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `48 = 32 + 16`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_ADD_GEN; NUM_OF_BYTELIST_APPEND;
                  LENGTH_LIST_OF_SEQ; ADD_CLAUSES; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The callees and the region lemmas, assumed before the template.           *)
(* ------------------------------------------------------------------------- *)

let V6_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* The loop test at the end of a row (loop12_exit): the index in R13, the
   pointers to t1 (RBX) and to the packed w1 (R15) advanced, RDI and RSI the
   row of w and the matrix structure again, and the branch back to join4,
   or to the jump past the end of the loop for the last row. *)
let V6_LT_STMT = parse_term(subst_tokens ["@MC@",image_mc; "@END@",string_of_int(v6_off 0x1afe)]
 "exists f_events. forall e rsp0 pc i (tb:int64) (wp:int64).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\ i < 6
    ==> ensures x86
      (\\s. bytes_loaded s (word pc) @MC@ /\\
           read RIP s = word (pc + mldsa65_verify_internal_loop12_exit) /\\
           read RSP s = rsp0 /\\ read R13 s = word i /\\
           read RBX s = tb /\\ read R15 s = wp /\\
           read events s = e)
      (\\s. read RIP s = word (if i + 1 = 6 then pc + @END@
                              else pc + mldsa65_verify_internal_join4) /\\
           read RSP s = rsp0 /\\ read R13 s = word (i + 1) /\\
           read RBX s = word_add tb (word 320) /\\
           read R15 s = word_add wp (word 128) /\\
           read RDI s = word_add rsp0 (word 2336) /\\
           read RSI s = word_add rsp0 (word 64) /\\
           (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc i /\\
              memaccess_inbounds e2 [] []))
      (MAYCHANGE [RIP; R13; RBX; R15; RDI; RSI] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])");;

let V6_LT_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num) (i:num). f_ev_lt rsp0 pc i :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `i:num`;
                       `tb:int64`; `wp:int64`] THEN
  REWRITE_TAC[fst V6_EXEC; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC V6_EXEC (1--7) THEN
  SUBGOAL_THEN `val (word_add (word i) (word 18446744073709551611):int64) = 0 <=>
                i + 1 = 6`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `i < 6` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_CASES_TAC `i + 1 = 6` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let V6_LT = prove(V6_LT_STMT, V6_LT_TAC);;

(* VM_PRE_TAC, and the 32-bit row index (ECX = R13D for the row of the
   matrix product) as word_zx (word_zx (word i)) = word i *)
let V6_PRE_TAC allowed =
  REPEAT CONJ_TAC THEN
  (fun g -> (TRY(MATCH_MP_TAC WORD_ZX2_SMALL THEN LOCAL_ARITH_TAC THEN NO_TAC) THEN
             VM_PRE_TAC allowed) g);;

let V6_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,V6_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [V6_PRE_TAC VM_ALLOWED; LABEL_TAC name th]);;

(* The precondition aligned 16 (stackpointer + 8) of mld_H, with the stack
   pointer word_sub rsp0 (word 8) after the call, from aligned 32 rsp0 *)
let VM_H_ALIGN_TAC =
  VM_ALIGNED_TAC [] THEN
  SUBGOAL_THEN `aligned 16 (word_add (word_sub rsp0 (word 8)) (word 8):int64)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`];
    ALL_TAC];;

let V6_FCALL_TAC name ilist n =
  V6_CALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC;;

let V6_CALLEES_TAC =
  let [uz0;uz1;uz2;uz3;uz4] = VI65_UNPACKZ_LOOPS in
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    VM_ASSUME_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
      "H_CHKNORM" THEN
    VM_ASSUME_TAC MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
    VM_ASSUME_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
      "H_INV" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)
      "H_CHAL" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)
      "H_ROW" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) mcs)
      "H_H65" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL VI65_HINTS) ms) "H_HINTS" THEN
    VM_ASSUME_TAC uz0 "H_UZ0" THEN VM_ASSUME_TAC uz1 "H_UZ1" THEN
    VM_ASSUME_TAC uz2 "H_UZ2" THEN VM_ASSUME_TAC uz3 "H_UZ3" THEN
    VM_ASSUME_TAC uz4 "H_UZ4" THEN
    VM_ASSUME_TAC VI65_UNPACKT1_LOOP "H_T1" THEN
    VM_ASSUME_TAC VI65_SHIFTL "H_SHL" THEN
    VM_ASSUME_TAC VI65_PWM_LOOP "H_PWM" THEN
    VM_ASSUME_TAC VI65_SUB_LOOP "H_SUB" THEN
    VM_ASSUME_TAC VI65_REDUCE_LOOP "H_RED" THEN
    VM_ASSUME_TAC VI65_CADDQ_LOOP "H_CADDQ" THEN
    VM_ASSUME_TAC VI65_USEHINT_LOOP "H_USEHINT" THEN
    VM_ASSUME_TAC VI65_PACKW1_LOOP "H_W1PACK" THEN
    VM_ASSUME_TAC VI65_CMP "H_CMP" THEN
    VM_ASSUME_TAC VI65_TR "H_TR" THEN
    VM_ASSUME_TAC V6_LT "H_LT");;

let V6_SETUP_TAC =
  REPEAT GEN_TAC THEN V6_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC V6_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `pre:int64`;
    `prelen:num`; `pk:int64`; `ext:int32`; `sigb:num->byte`; `pkb:num->byte`;
    `M:num`; `PRE':num`; `pc:num`; `rsp0:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              NONOVERLAPPING_CLAUSES; fst V6_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

(* ------------------------------------------------------------------------- *)
(* From loop1 to the return of the norm check, from state 0 to state 22.     *)
(* ------------------------------------------------------------------------- *)

let V6_Z = parse_term
  "mld_polyvec_unpack 640 mld_polyz_unpack_19 (\\j. (sigb:num->byte)(48 + j))";;

let V6_UZ_TAC k n =
  let off = 48 + 640 * k in
  let offt = mk_small_numeral off in
  VERIF_SLICE_TAC (subst [offt,`off:num`;
     mk_var("s"^string_of_int(n-1),`:x86state`),`s:x86state`]
    `!j. j < 640 ==> read(memory :> bytes8(word_add sig (word(off + j)))) s =
                     (sigb:num->byte)(off + j)`) THEN
  V6_CALL_TAC ("H_UZ"^string_of_int k)
   [subst [offt,`off:num`] `word_add sig (word off):int64`; `rsp0:int64`; `pc:num`;
    subst [offt,`off:num`] `\j. (sigb:num->byte)(off + j)`] n;;

let V6_UNPACK_TAC =
  V6_UZ_TAC 0 1 THEN
  X86_STEPS_TAC V6_EXEC (2--4) THEN V6_UZ_TAC 1 5 THEN
  X86_STEPS_TAC V6_EXEC (6--8) THEN V6_UZ_TAC 2 9 THEN
  X86_STEPS_TAC V6_EXEC (10--12) THEN V6_UZ_TAC 3 13 THEN
  X86_STEPS_TAC V6_EXEC (14--17) THEN V6_UZ_TAC 4 18 THEN
  X86_STEPS_TAC V6_EXEC (19--21) THEN
  W(fun (asl,w) ->
    let fs = filter (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `mld_polyz_unpack_19`)) (concl th))
                    (map snd asl) in
    let st = rand(lhs(snd(dest_imp(snd(dest_forall(concl(hd fs))))))) in
    MP_TAC(SPECL [`rsp0:int64`; `sigb:num->byte`; st] V6_VEC5) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  V6_FCALL_TAC "H_CHKNORM" [`read RDI s`; V6_Z; `read RSI s`] 22;;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: join1 sets the result -6.                           *)
(* ------------------------------------------------------------------------- *)

let V6_NORMOK_TM = parse_term V6_NORMOK;;
let V6_OK_TM = parse_term V6_OK;;

let V6_OK_NORM = prove
 (`!sigb pkb mu.
     mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
       mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 sigb pkb mu
     ==> mld_polyvec_chknorm 5
          (mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(48 + j)))
          (word 524092) = word 0`,
  REWRITE_TAC[mld_verify_internal_ok] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[]);;

let V6_BND_TAC =
  let tm = `word_zx (word 524092:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let V6_NOT_OK_TAC =
  SUBGOAL_THEN (mk_neg V6_OK_TM) (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN(MP_TAC o MATCH_MP V6_OK_NORM) THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let V6_NF_TAC =
  FULL_INIT_TAC THEN V6_UNPACK_TAC THEN V6_BND_TAC THEN
  X86_STEPS_TAC V6_EXEC (23--24) THEN VERIF_PC_TAC [V6_NORMOK_TM] THEN
  X86_STEPS_TAC V6_EXEC (25--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN V6_NOT_OK_TAC THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join3, where mu is ready at rsp0 + 1248.                     *)
(* ------------------------------------------------------------------------- *)

let V6_MU =
  `if ext = (word 0:int32)
   then mld_verify_mu 1952 pkb prelen PRE' mlen M else M MOD 2 EXP 512`;;

let V6_FRAME =
  "read RSP s = rsp0 /\\
   read (memory :> bytes64 (word_add rsp0 (word 40))) s = sig /\\
   read (memory :> bytes128 (word_add rsp0 (word 1120))) s = mld_chunk128 sigb 0 /\\
   read (memory :> bytes128 (word_add rsp0 (word 1136))) s = mld_chunk128 sigb 1 /\\
   read (memory :> bytes128 (word_add rsp0 (word 1152))) s = mld_chunk128 sigb 2 /\\
   (read DF s <=> false) /\\
   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
   read (memory :> bytes(ea,el)) s = ev /\\
   (!j. j < 3309 ==> read(memory :> bytes8(word_add sig (word j))) s = sigb j) /\\
   (!j. j < 1952 ==> read(memory :> bytes8(word_add pk (word j))) s = pkb j)";;

let V6_J3 =
  subst [V6_Z,`VMZ:num->int32`; V6_MU,`VMMU:num`]
  (parse_term ("\\s. " ^ V6_FRAME ^ " /\\
     read RBX s = pk /\\
     (!i. i < 1280 ==> read (memory :> bytes32 (word_add rsp0 (word (5152 + 4 * i)))) s =
                       VMZ i) /\\
     read (memory :> bytes (word_add rsp0 (word 1248),64)) s = VMMU"));;

let V6_COPY_TAC =
  FULL_INIT_TAC THEN VM_M_CHUNKS_TAC THEN VM_ALIGNED_TAC [1248; 1264; 1280; 1296] THEN
  V6_UNPACK_TAC THEN V6_BND_TAC THEN
  X86_STEPS_TAC V6_EXEC (23--24) THEN VERIF_PC_TAC [V6_NORMOK_TM] THEN
  X86_STEPS_TAC V6_EXEC (25--26) THEN VM_EXT_PC_TAC THEN
  YMM_GHOST_TAC `s26:x86state`
   ["YMM0","ymm0_26"; "YMM1","ymm1_26"; "YMM2","ymm2_26"; "YMM3","ymm3_26"] THEN
  X86_STEPS_TAC V6_EXEC (27--35) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_MU_OF_CHUNKS_TAC `word_add rsp0 (word 1248):int64` `s35:x86state` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* ext = 0: tr = SHAKE256(pk) (the region TR, then the 64 bytes of the state *)
(* copied to rsp0 + 3360 and the state zeroed), and mu = H(tr, pre, m) by a  *)
(* call of mld_H65 (steps 27 to 78).                                         *)
(* ------------------------------------------------------------------------- *)

let V6_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 1952)`;;

let V6_TRNUM = subst [V6_PKNUM,`p:num`]
  `num_of_bytelist (list_of_seq (mld_shake256_byte 1952 p) 64)`;;

let V6_TR_CHUNKS_TAC st =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> wbytes (word_add rsp0 (word 64))) s = x`)
           (concl th)
    then MAP_EVERY (fun k ->
           MP_TAC(SPECL [`word_add rsp0 (word 64):int64`; rhs(concl th);
                         mk_small_numeral k; st] READ_MEMORY_BYTES128_OF_WBYTES) THEN
           ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC th; ARITH_TAC]; ALL_TAC] THEN
           MP_TAC(SPECL [`1952`; V6_PKNUM; mk_small_numeral k] VM_TR_CHUNK) THEN
           ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
           CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
           REWRITE_TAC[WORD_ADD_0; EXP; DIV_1] THEN DISCH_TAC) [0;1;2;3]
    else NO_TAC);;

let V6_TR_OF_CHUNKS_TAC s =
  MP_TAC(SPECL [`word_add rsp0 (word 3360):int64`; V6_TRNUM; `4`; s]
               VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VM_SHAKE_BYTES; MOD_MOD_REFL]);;

let V6_HASH_TAC =
  FULL_INIT_TAC THEN
  VM_ALIGNED_TAC [64; 80; 96; 112; 128; 144; 160; 176; 192; 208; 224; 240; 256;
                  3360; 3376; 3392; 3408] THEN
  V6_UNPACK_TAC THEN V6_BND_TAC THEN
  X86_STEPS_TAC V6_EXEC (23--24) THEN VERIF_PC_TAC [V6_NORMOK_TM] THEN
  X86_STEPS_TAC V6_EXEC (25--26) THEN VM_EXT_PC_TAC THEN
  MP_TAC(SPECL [`pk:int64`; `1952`; `pkb:num->byte`; `s26:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  V6_CALL_TAC "H_TR" [`rsp0:int64`; `pk:int64`; `pc:num`; V6_PKNUM] 27 THEN
  V6_TR_CHUNKS_TAC `s27:x86state` THEN
  YMM_GHOST_TAC `s27:x86state`
   ["YMM0","ymm0_27"; "YMM1","ymm1_27"; "YMM2","ymm2_27"; "YMM3","ymm3_27"] THEN
  X86_STEPS_TAC V6_EXEC (28--72) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  V6_TR_OF_CHUNKS_TAC `s72:x86state` THEN
  VM_H_ALIGN_TAC THEN
  V6_FCALL_TAC "H_H65"
   [`read RDI s`; `64`; `read RDX s`; `64`; `read R8 s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    subst [V6_PKNUM,`p:num`]
     `val(keccak_f1600 (mld_shake256_state 1952 p)) MOD 2 EXP 512`;
    `PRE':num`; `M:num`] 73 THEN
  X86_STEPS_TAC V6_EXEC (74--78) THEN
  REWRITE_TAC[mld_verify_mu; SPEC `1952` VM_SHAKE_BYTES] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2 EXP (8 * 64)` (concl th)
    then REWRITE_RULE[ARITH_RULE `8 * 64 = 512`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The values of the code (as in the gcc proof).                             *)
(* ------------------------------------------------------------------------- *)

let V6_ZHAT = mk_comb(`mld_polyvec_map mld_poly_ntt`,V6_Z);;
let V6_C = `num_of_bytelist (list_of_seq (sigb:num->byte) 48)`;;
let V6_CP = mk_comb(`mld_poly_challenge 49 48`,V6_C);;
let V6_CPHAT = mk_comb(`mld_poly_ntt`,V6_CP);;

let V6_PWM = list_mk_comb(`mld_poly_pointwise_montgomery`,[VM_NTT1;V6_CPHAT]);;
let V6_ROWL =
  subst [VM_RHO,`rho:num`; V6_ZHAT,`zhat:num->int32`]
   `mld_polyvec_matrix_row_lazy 5 rho zhat i`;;
let V6_SUBL = list_mk_comb(`mld_poly_sub`,[V6_ROWL;V6_PWM]);;
let V6_REDL = mk_comb(`mld_poly_reduce`,V6_SUBL);;
let V6_INVTL = mk_comb(`mld_poly_invntt_tomont`,V6_REDL);;
let V6_CADDQL = mk_comb(`mld_poly_caddq`,V6_INVTL);;
let V6_HB = `\t. (sigb:num->byte) (3248 + t)`;;
let V6_HINTS = `mld_unpack_hints 55 (\t. (sigb:num->byte) (3248 + t)) i`;;

let V6_W1B =
  subst [VM_RHO,`rho:num`; V6_ZHAT,`zhat:num->int32`;
         V6_CPHAT,`cphat:num->int32`]
   `mld_polyvec_pack 128 mld_polyw1_pack_32
     (mld_polyvec
       (mld_verify_w1 5 mld_poly_use_hint_32 rho zhat cphat pkb 55
         (\t. (sigb:num->byte) (3248 + t))))`;;

(* ------------------------------------------------------------------------- *)
(* From join3 to join4: the NTT of the 5 polynomials of z, rho copied to the *)
(* structure of the matrix, the challenge from c~ and its NTT.               *)
(* ------------------------------------------------------------------------- *)

(* The invariant at join4 for row i: as for 44, except that the constant of
   the Montgomery multiplication in R12 is only known while the hints of the
   rows so far unpack (the hints code clobbers R12 and restores it at join8,
   not on the way to join1). *)
let V6_INV =
  subst [V6_MU,`VMMU:num`; V6_W1B,`VMW1B:num->byte`; VM_RHO,`VMRHO:num`;
         V6_ZHAT,`VMZHAT:num->int32`; V6_CPHAT,`VMCPHAT:num->int32`]
  (parse_term ("\\i s. " ^ V6_FRAME ^ " /\\
     read (memory :> bytes (word_add rsp0 (word 1088),32)) s = VMRHO /\\
     (!j. j < 1280 ==> read (memory :> bytes32 (word_add rsp0 (word (5152 + 4 * j)))) s =
                       VMZHAT j) /\\
     (!j. j < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (3360 + 4 * j)))) s =
                      VMCPHAT j) /\\
     read (memory :> bytes (word_add rsp0 (word 1248),64)) s = VMMU /\\
     ((!j. j < i ==> " ^ "mld_unpack_hints_ok 55 6 (\\t. sigb(3248 + t)) j" ^ ")
      ==> read R12 s = word 0x0380200100000000 /\\
          read R13 s = word i /\\
          read R14 s = word_add rsp0 (word 5152) /\\
          read R15 s = word_add rsp0 (word (4388 + 128 * i)) /\\
          read RSI s = word_add rsp0 (word 64) /\\
          read RDI s = word_add rsp0 (word 2336) /\\
          read RBX s = word_add pk (word (33 + 320 * i)) /\\
          (!j. j < 128 * i
               ==> read (memory :> bytes8 (word_add rsp0 (word (4384 + j)))) s =
                   VMW1B j))"));;

let V6_PC2 =
  parse_term("if " ^ V6_HINTSOK ^
             " then pc + " ^ string_of_int (v6_off 0x1afe) ^
             " else pc + mldsa65_verify_internal_join1");;

let V6_MID_TAC =
  FULL_INIT_TAC THEN VM_ALIGNED_TAC [1088; 1104] THEN
  MAP_EVERY (fun k -> V6_SPLIT_TAC 5152 V6_Z k `s0:x86state`) [0;1;2;3;4] THEN
  X86_STEPS_TAC V6_EXEC (1--4) THEN
  V6_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,V6_Z),`0`)] 5 THEN
  X86_STEPS_TAC V6_EXEC (6--7) THEN
  V6_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,V6_Z),`1`)] 8 THEN
  X86_STEPS_TAC V6_EXEC (9--10) THEN
  V6_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,V6_Z),`2`)] 11 THEN
  X86_STEPS_TAC V6_EXEC (12--13) THEN
  V6_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,V6_Z),`3`)] 14 THEN
  X86_STEPS_TAC V6_EXEC (15--16) THEN
  V6_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,V6_Z),`4`)] 17 THEN
  V6_JOIN_TAC 5152 (mk_abs(`k:num`,mk_comb(`mld_poly_ntt`,
                     mk_comb(mk_comb(`mld_poly_of`,V6_Z),`k:num`)))) `s17:x86state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_polyvec_map]) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`pk:int64`; `1952`; `pkb:num->byte`; `s17:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1] THEN
  YMM_GHOST_TAC `s17:x86state` ["YMM0","ymm0_17"; "YMM1","ymm1_17"] THEN
  X86_STEPS_TAC V6_EXEC (18--25) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  MP_TAC(SPECL [`word_add rsp0 (word 1088):int64`; `pkb:num->byte`; `s25:x86state`]
               MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`word_add rsp0 (word 1120):int64`; `sigb:num->byte`; `s25:x86state`]
               V6_BYTES48_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  V6_FCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; V6_C] 26 THEN
  X86_STEPS_TAC V6_EXEC (27--28) THEN
  V6_FCALL_TAC "H_NTT" [`read RDI s`; V6_CP] 29 THEN
  X86_STEPS_TAC V6_EXEC (30--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body for row i.                                                  *)
(* ------------------------------------------------------------------------- *)

let V6_ACC =
  subst [VM_RHO,`rho:num`; V6_ZHAT,`zhat:num->int32`]
   `mld_polyvec_pointwise_acc_montgomery 5
     (\j. mld_polyvec_matrix_expand 5 rho (1280 * i + j)) zhat`;;
let V6_SUB = list_mk_comb(`mld_poly_sub`,[V6_ACC;V6_PWM]);;
let V6_RED = mk_comb(`mld_poly_reduce`,V6_SUB);;
let V6_INVT = mk_comb(`mld_poly_invntt_tomont`,V6_RED);;
let V6_CADDQ = mk_comb(`mld_poly_caddq`,V6_INVT);;
let V6_UH = list_mk_comb(`mld_poly_use_hint_32`,[V6_CADDQ;V6_HINTS]);;
let V6_HOK_TM = parse_term V6_HOK;;
let V6_HINTSOK_TM = parse_term V6_HINTSOK;;

let V6_ZHAT_BOUND =
  subst [V6_ZHAT,`zhat:num->int32`]
   `!j. j < 1280 ==> abs(ival((zhat:num->int32) j)) < &94279689`;;

let V6_ZHAT_BOUND_TAC =
  SUBGOAL_THEN V6_ZHAT_BOUND ASSUME_TAC THENL
   [MP_TAC(SPECL [`5`; V6_Z] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_Z_UNPACK_BOUND];
    ALL_TAC];;

let V6_CADDQ_TAC =
  FIRST_ASSUM(fun th ->
    if not(is_forall(concl th)) ||
       not(can (find_term ((=) V6_CADDQL)) (concl th))
    then failwith "V6_CADDQ_TAC" else
    SUBGOAL_THEN (subst [V6_CADDQ,V6_CADDQL] (concl th)) ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun nth -> REWRITE_TAC[MP (SPEC `n:num` th) nth] THEN
                            ASSUME_TAC nth) THEN
      MP_TAC(SPECL [`6`; `5`; VM_RHO; V6_ZHAT; V6_PWM; `i:num`; `n:num`]
                   MLD_LAZY_VERIFY) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MLD_LAZY_POINTWISE_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[]];
      ALL_TAC]);;

let V6_ROWS_TAC =
  MP_TAC(BETA_RULE(SPECL [mk_abs(`i:num`,V6_HOK_TM); `6`; `i:num`]
                         VERIF_ROWS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(lhand(concl th)) &&
    fst(dest_forall(lhand(concl th))) = `j:num`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

let V6_LCALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,V6_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [V6_PRE_TAC VM_ALLOWED_LOOP; LABEL_TAC name th]);;

let V6_LFCALL_TAC name ilist n =
  V6_LCALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC;;

(* The constants that the row body loads RIP-relative: the two 64-bit vectors
   of the unpacking of t1 (movq) and the two 128-bit vectors of the reduction
   (aligned movdqa). *)
let V6_CONSTS64 =
  map (fun n -> IMAGE_CONST_RULE_FOR VM_MC (layout n) 64)
   ["mldsa65_verify_internal_const3"; "mldsa65_verify_internal_const4"];;

let V6_CONSTS128 =
  map (fun n -> IMAGE_CONST_RULE_FOR VM_MC (layout n) 128)
   ["mldsa65_verify_internal_const1"; "mldsa65_verify_internal_const2"];;

let V6_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  VERIF_GEN_TAIL_TAC false "front" THEN
  FULL_INIT_TAC THEN V6_ROWS_TAC THEN
  VM_ALIGNED_TAC [64; 1312; 2336; 3360; 5152] THEN
  X86_STEPS_TAC V6_EXEC (1--3) THEN
  V6_LFCALL_TAC "H_ROW"
   [`read RDI s`; `read RSI s`; `read RDX s`; VM_RHO; V6_ZHAT; `i:num`] 4 THEN
  YMM_GHOST_TAC `s4:x86state`
   ["YMM2","ymm2_4"; "YMM3","ymm3_4"; "YMM4","ymm4_4"] THEN
  X86_STEPS_TAC V6_EXEC (5--7) THEN
  IMAGE_RIPREL_TAC (el 0 V6_CONSTS64) (v6_off 0x10b5) THEN
  X86_STEPS_TAC V6_EXEC (8--8) THEN
  IMAGE_RIPREL_TAC (el 1 V6_CONSTS64) (v6_off 0x10bd) THEN
  X86_STEPS_TAC V6_EXEC (9--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_SLICE_TAC
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word((32 + 320 * i) + j)))) s10 =
            (pkb:num->byte)(32 + 320 * i + j)` THEN
  V6_LCALL_TAC "H_T1"
   [`word_add pk (word(32 + 320 * i)):int64`; `rsp0:int64`; `pc:num`;
    `\j. (pkb:num->byte)(32 + 320 * i + j)`] 11 THEN
  V6_LCALL_TAC "H_SHL" [`rsp0:int64`; `pc:num`; VM_T1] 12 THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = word x`) (concl th)
    then CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th else th) THEN
  X86_STEPS_TAC V6_EXEC (13--14) THEN
  V6_LFCALL_TAC "H_NTT" [`read RDI s`; VM_SHL] 15 THEN
  X86_STEPS_TAC V6_EXEC (16--17) THEN
  V6_LCALL_TAC "H_PWM" [`rsp0:int64`; `pc:num`; VM_NTT1; V6_CPHAT] 18 THEN
  YMM_GHOST_TAC `s18:x86state` ["YMM5","ymm5_18"; "YMM6","ymm6_18"] THEN
  X86_STEPS_TAC V6_EXEC (19--20) THEN
  IMAGE_RIPREL_TAC (el 0 V6_CONSTS128) (v6_off 0x1789) THEN
  X86_STEPS_TAC V6_EXEC (21--21) THEN
  IMAGE_RIPREL_TAC (el 1 V6_CONSTS128) (v6_off 0x1791) THEN
  X86_STEPS_TAC V6_EXEC (22--23) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  V6_LCALL_TAC "H_SUB" [`rsp0:int64`; `pc:num`; V6_ROWL; V6_PWM] 24 THEN
  X86_STEPS_TAC V6_EXEC (25--26) THEN
  V6_LCALL_TAC "H_RED" [`rsp0:int64`; `pc:num`; V6_SUBL] 27 THEN
  X86_STEPS_TAC V6_EXEC (28--28) THEN
  V6_LFCALL_TAC "H_INV" [`read RDI s`; V6_REDL] 29 THEN
  X86_STEPS_TAC V6_EXEC (30--31) THEN
  V6_LCALL_TAC "H_CADDQ" [`rsp0:int64`; `pc:num`; V6_INVTL] 32 THEN
  V6_CADDQ_TAC THEN
  VM_SLICE_TAC
   `!j. j < 61
        ==> read(memory :> bytes8(word_add sig (word(3248 + j)))) s32 =
            (sigb:num->byte)(3248 + j)` THEN
  V6_LCALL_TAC "H_HINTS"
   [`sig:int64`; `rsp0:int64`; `pc:num`; V6_HB; `i:num`;
    `word_add pk (word(33 + 320 * i)):int64`] 33;;

let V6_PC_OK_TAC =
  ASM_CASES_TAC `i + 1 < 6` THENL
   [SUBGOAL_THEN `~(i + 1 = 6)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i + 1 < 6`; ASSUME `~(i + 1 = 6)`];
    SUBGOAL_THEN `i + 1 = 6` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN V6_HINTSOK_TM ASSUME_TAC THENL
     [VERIF_IMP_CASE_TAC `~(i + 1 < 6)`; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~(i + 1 < 6)`; ASSUME `i + 1 = 6`;
                ASSUME V6_HINTSOK_TM]];;

let V6_JOIN_W1_TAC =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[MATCH_MP (SPEC_ALL VERIF_W1B_ROW_32) (ASSUME `k < 128`)] THEN
    REWRITE_TAC[mld_verify_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(fun th ->
      MATCH_MP_TAC(REWRITE_RULE[GSYM ADD_ASSOC] th)) THEN
    FIRST_ASSUM ACCEPT_TAC];;

let V6_BODY_OK_TAC =
  VERIF_MP_CASE_TAC V6_HOK_TM THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  V6_LCALL_TAC "H_USEHINT" [`rsp0:int64`; `pc:num`; V6_CADDQ; V6_HINTS] 34 THEN
  V6_LCALL_TAC "H_W1PACK"
   [`rsp0:int64`; `word_add rsp0 (word (4384 + 128 * i)):int64`;
    `pc:num`; V6_UH] 35 THEN
  V6_LCALL_TAC "H_LT"
   [`rsp0:int64`; `pc:num`; `i:num`; `word_add pk (word (33 + 320 * i)):int64`;
    `word_add rsp0 (word (4388 + 128 * i)):int64`] 36 THEN
  VERIF_FINAL_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(V6_PC_OK_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN V6_JOIN_W1_TAC THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN
  VM_EVENTS_TAC [`front:(uarch_event)list`];;

let V6_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg V6_HOK_TM) THEN VERIF_FINAL_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg V6_HOK_TM)] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN
  VM_EVENTS_TAC [`front:(uarch_event)list`];;

let V6_BODY_TAC =
  V6_BODY1_TAC THEN
  ASM_CASES_TAC V6_HOK_TM THEN VERIF_PC_TAC [V6_HOK_TM] THENL
   [V6_BODY_OK_TAC; V6_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop. All hints unpack: c2 = H(mu, w1') (mld_H65, 48 bytes at   *)
(* rsp0 + 1184), and the comparison of c~ and c2 (the region CMP). Some do   *)
(* not: join1 sets -6.                                                       *)
(* ------------------------------------------------------------------------- *)

let V6_OK_THM = GEN_ALL(prove
 (subst [V6_W1B,`w1b:num->byte`]
  `mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
       mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 (sigb:num->byte)
       (pkb:num->byte) mu <=>
     mld_polyvec_chknorm 5
       (mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(48 + j)))
       (word 524092) = word 0 /\
     (!i. i < 6 ==> mld_unpack_hints_ok 55 6 (\t. sigb(3248 + t)) i) /\
     (!j. j < 48
          ==> sigb j =
              mld_shake256_byte 832
               (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b 768)) j)`,
  REWRITE_TAC[mld_verify_internal_ok; VM_HRET] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `48 + 5 * 640 + t = 3248 + t`;
              ARITH_RULE `64 + 6 * 128 = 832`; ARITH_RULE `6 * 128 = 768`]));;

let V6_W1NUM =
  mk_comb(`num_of_bytelist`,
          mk_comb(mk_comb(`list_of_seq:(num->byte)->num->byte list`,V6_W1B),
                  `768`));;

let V6_SQ = subst [V6_MU,`mu:num`; V6_W1NUM,`w:num`]
  `mld_shake256_byte 832 (mu + 2 EXP 512 * w)`;;

let V6_POST_OK_TAC =
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`word_add rsp0 (word 4384):int64`; `768`; V6_W1B; `s0:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_32`)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  VERIF_NULL_TAC [`word_add rsp0 (word 1184):int64`,`48`;
                  `word_sub rsp0 (word 584):int64`,`576`] THEN
  YMM_GHOST_TAC `s0:x86state` ["YMM0","ymm0_0"] THEN
  X86_STEPS_TAC V6_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_SPLIT128_TAC `rsp0:int64` `s10:x86state` THEN
  VM_H_ALIGN_TAC THEN
  V6_FCALL_TAC "H_H65"
   [`read RDI s`; `48`; `read RDX s`; `64`; `read R8 s`; `768`;
    `word 0:int64`; `0`; V6_MU; V6_W1NUM; `0`] 11 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES;
    ARITH_RULE `64 + 768 = 832`; ARITH_RULE `8 * 64 = 512`]) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(word_add rsp0 (word 1184),48)) (s:x86state) = n`)
           (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`word_add rsp0 (word 1184):int64`; `48`; V6_SQ; `s11:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    DISCH_TAC) [0;1;2] THEN
  VM_ALIGNED_TAC [48; 1120; 1184] THEN
  V6_CALL_TAC "H_CMP"
   [`rsp0:int64`; `pc:num`; `mld_chunk128 sigb 0`; `mld_chunk128 sigb 1`;
    `mld_chunk128 sigb 2`;
    mk_comb(mk_comb(`mld_chunk128`,V6_SQ),`0`);
    mk_comb(mk_comb(`mld_chunk128`,V6_SQ),`1`);
    mk_comb(mk_comb(`mld_chunk128`,V6_SQ),`2`)] 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[V6_OK_THM; ASSUME V6_NORMOK_TM; EQT_INTRO(ASSUME V6_HINTSOK_TM)] THEN
  MP_TAC(ISPECL [`sigb:num->byte`; V6_SQ; `3`] MLD_CHUNK128_EQ) THEN
  CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
  REWRITE_TAC[ARITH_RULE `16 * 3 = 48`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN VM_EVENTS_TAC [`old:(uarch_event)list`];;

let V6_POST_HF_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC V6_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[V6_OK_THM] THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN VM_EVENTS_TAC [`old:(uarch_event)list`];;

let V6_POST_TAC =
  VERIF_GEN_TAIL_TAC true "old" THEN
  ASM_CASES_TAC V6_HINTSOK_TM THENL
   [REWRITE_TAC[EQT_INTRO(ASSUME V6_HINTSOK_TM); ARITH_RULE `0 < 6`] THEN
    V6_POST_OK_TAC;
    REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg V6_HINTSOK_TM))] THEN
    V6_POST_HF_TAC];;

(* ------------------------------------------------------------------------- *)
(* The body as a whole.                                                      *)
(* ------------------------------------------------------------------------- *)

let V6_MAIN_TAC =
  V6_SETUP_TAC THEN V6_ZHAT_BOUND_TAC THEN
  ASM_CASES_TAC V6_NORMOK_TM THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[if is_neg(concl th) then th else EQT_INTRO th]) THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term V6_K)
     `pc + mldsa65_verify_internal_join4` V6_PC2 V6_INV THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                  CONJUNCT1 LT; LT_REFL] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_verify_internal_join3` V6_J3 THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC `ext = (word 0:int32)` THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[if is_neg(concl th) then th else EQT_INTRO th]) THEN
        FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM VAL_EQ_0] o
                      check (fun th -> concl th = `ext = (word 0:int32)` ||
                                       concl th = `~(ext = (word 0:int32))`)) THENL
         [V6_HASH_TAC; V6_COPY_TAC];
        V6_MID_TAC];
      V6_BODY_TAC;
      V6_POST_TAC];
    V6_NF_TAC];;

let VI65_MAIN = prove(V6_STMT, V6_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

let VI65_TOP_TEMPLATE = VI44_TOP_TEMPLATE;;

let VI65_TOP_CALL_TAC name ilist n =
  FULL_CALL_TAC VM_MC V6_EXEC name ilist VI44_TOP_ALLOWED n;;

let VI65_TOP_A0_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPEC_ALL VI65_MAIN) th) "H_MAIN" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPEC_ALL VI65_CLEANUP) (CONJUNCT1 th))
      "H_CL") THEN
  CONCRETIZE_F_EVENTS_TAC VI65_TOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst V6_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 11989 THEN REALIGN_FRAME_TAC 12037 11989 THEN
  REALIGN_NONOV_TAC 11958
   [`sig:int64,3309`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `pk:int64,1952`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 11989):int64,48`;
    `word_add stackpointer (word 12037):int64,8`;
    `word_add stackpointer (word 12045):int64,4`] THEN
  REALIGN_ALIGNED_TAC [2774; 2790; 2806] THEN
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
    REWRITE_TAC[WORD_RULE `word_add bot (word 11958):int64 =
                           word_add (word_add bot (word 1654)) (word 10304)`] THEN
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

let VI65_TOP_A1_TAC =
  FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes32 a) s0 = ext`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th) THEN
  YMM_GHOST_TAC `s0:x86state` ["YMM0","ymm0_0"; "YMM1","ymm1_0"; "YMM2","ymm2_0"] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `3309`; `sigb:num->byte`; `s0:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1;2] THEN
  X86_STEPS_TAC V6_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  MAP_EVERY (fun k ->
    SUBGOAL_THEN (subst [mk_small_numeral k,`k:num`]
      `aligned 16 (word_add (word_add bot (word 1654)) (word k):int64)`)
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC]) [1120;1136;1152] THEN
  X86_STEPS_TAC V6_EXEC (9--28) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]);;

let VI65_TOP_B_TAC =
  VI65_TOP_CALL_TAC "H_MAIN"
   [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`; `pk:int64`;
    `ext:int32`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `PRE':num`;
    `pc:num`; VI44_RSP0] 29;;

let VI65_TOP_C_TAC =
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                      `word_add bot (word 1646):int64,10312`),r))
     ASSUME_TAC THENL
     [EXPAND_TAC "bot" THEN NONOVERLAPPING_TAC; ALL_TAC])
   [`word pc:int64,libmldsa_size`; `word(pc + got_memset):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 11989):int64,56`] THEN
  VI65_TOP_CALL_TAC "H_CL"
   [VI44_RSP0; `word_add stackpointer (word 11989):int64`; `read R14 s`; `pc:num`;
    `rbx_init:int64`; `r12_init:int64`; `r13_init:int64`; `r14_init:int64`;
    `r15_init:int64`; `rbp_init:int64`; `returnaddress:int64`] 30 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let VI65_TOP_TAC = VI65_TOP_A0_TAC THEN VI65_TOP_A1_TAC THEN VI65_TOP_B_TAC THEN VI65_TOP_C_TAC;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  VI65_TOP_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
