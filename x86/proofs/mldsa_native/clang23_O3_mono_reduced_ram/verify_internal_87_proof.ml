(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature, ML-DSA-87: the proof (see                    *)
(* verify_internal_87_spec.ml). It is that of verify_internal_65_proof.ml    *)
(* with the parameters of ML-DSA-87 (K = 8, l = 7, 64 bytes of c~) and the   *)
(* frame of the clang code:                                                  *)
(*                                                                           *)
(*   the matrix, the Keccak state of tr  rsp0 + 256, the state of c2 rsp0+32 *)
(*   rho rsp0 + 1280, c~ rsp0 + 1344, mu rsp0 + 1408, c2 rsp0 + 1472         *)
(*   t1, hints rsp0 + 1536, w rsp0 + 2560, w1 (packed) and tr rsp0 + 3584    *)
(*   cp rsp0 + 4608, z rsp0 + 5632 + 1024 k, k = 0..6                        *)
(*                                                                           *)
(* Unlike 44 and 65, clang inlines mld_H for c2 = H(mu, w1') (the region C2  *)
(* of inline_verify87.ml), and the pointer to the prefix is saved to the     *)
(* stack in the absorption of pk (TRG with a saved register).                *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_87_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_tools.ml";;

(* ------------------------------------------------------------------------- *)
(* The body, from loop1 to join2.                                            *)
(* ------------------------------------------------------------------------- *)

let V8_FN = "mldsa87_verify_internal";;
let v8_off n = layout V8_FN + n;;

let V8_HOK = "mld_unpack_hints_ok 75 8 (\\t. sigb(4544 + t)) i";;

let V8_HINTSOK = "(!i. i < 8 ==> " ^ V8_HOK ^ ")";;

let V8_K =
  "(if " ^ V8_HINTSOK ^ " then 8 else (minimal i. ~(" ^ V8_HOK ^
  ")) + 1)";;

let V8_NORMOK =
  "mld_polyvec_chknorm 7 (mld_polyvec_unpack 640 mld_polyz_unpack_19 " ^
  "(\\j. sigb(64 + j))) (word 524168) = word 0";;

let V8_OK =
  "mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168 " ^
  "mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 sigb pkb " ^
  "(if ext = (word 0:int32) " ^
  "then mld_verify_mu 2592 pkb prelen PRE' mlen M else M MOD 2 EXP 512)";;

let V8_TEMPLATE_CASE =
  let f n = "(f_ev_" ^ n ^ " " ^ VM_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ " " ^ VM_ARGS ^ " i)" in
  "(if " ^ V8_NORMOK ^ " then " ^
  "APPEND (if " ^ V8_HINTSOK ^ " then " ^ f "post" ^ " else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ V8_K ^ " (\\i. if " ^ V8_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ")";;

let V8_TEMPLATE =
  parse_term(VM_LAMBDA ^ " " ^ V8_TEMPLATE_CASE ^ " :(uarch_event)list");;

let V8_READS =
  "[sig,4627; m,mlen; pre,prelen; pk,2592;
    word_sub rsp0 (word 1654),14486;
    word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
    word(pc + rodata_mld_zetas),1024;
    word(pc + rodata_mld_KeccakF_RoundConstants),192;
    word(pc + mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
    word(pc + mldsa87_verify_internal_consts),784]";;

let V8_STMT =
  parse_term(subst_tokens ["@MC@",image_mc; "@READS@",V8_READS]
  "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc rsp0.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          mlen < 2 EXP 64 /\\ prelen < 2 EXP 64 /\\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\\
          aligned 32 rsp0 /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1654),14486))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + mldsa87_verify_internal_loop1) /\\
                    read RSP s = rsp0 /\\
                    read RAX s = word_add sig (word 68) /\\ read RCX s = word 0 /\\
                    read RDI s = sig /\\ read R12 s = m /\\ read R13 s = pre /\\
                    read R14 s = word prelen /\\
                    read RBX s = pk /\\ read R15 s = word_zx ext /\\
                    read (memory :> bytes64 (word_add rsp0 (word 24))) s = word mlen /\\
                    read (memory :> bytes128 (word_add rsp0 (word 1344))) s =
                      mld_chunk128 sigb 0 /\\
                    read (memory :> bytes128 (word_add rsp0 (word 1360))) s =
                      mld_chunk128 sigb 1 /\\
                    read (memory :> bytes128 (word_add rsp0 (word 1376))) s =
                      mld_chunk128 sigb 2 /\\
                    read (memory :> bytes128 (word_add rsp0 (word 1392))) s =
                      mld_chunk128 sigb 3 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s = sigb j) /\\
                    read (memory :> bytes(m,mlen)) s = M /\\
                    read (memory :> bytes(pre,prelen)) s = PRE /\\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s = pkb j) /\\
                    read events s = e)
               (\\s. read RIP s = word (pc + mldsa87_verify_internal_join2) /\\
                    read RSP s = rsp0 /\\
                    read R14 s =
                    (if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 2592 pkb prelen PRE mlen M
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
                        [word_sub rsp0 (word 1654),14486]))
               (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1654),14486)])");;

(* ------------------------------------------------------------------------- *)
(* The z vector as the code unpacks it, polynomial by polynomial, at         *)
(* rsp0 + 5632.                                                              *)
(* ------------------------------------------------------------------------- *)

let V8_VEC7 = prove
 (`!(r:int64) (sigb:num->byte) (s:x86state).
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(5632 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(64 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(6656 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(704 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(7680 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(1344 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(8704 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(1984 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(9728 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(2624 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(10752 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(3264 + j)) i) /\
     (!i. i < 256 ==> read(memory :> bytes32(word_add r (word(11776 + 4 * i)))) s =
                      mld_polyz_unpack_19 (\j. sigb(3904 + j)) i)
     ==> !i. i < 1792
             ==> read(memory :> bytes32(word_add r (word(5632 + 4 * i)))) s =
                 mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(64 + j)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  SUBGOAL_THEN `i = 256 * (i DIV 256) + i MOD 256 /\ i MOD 256 < 256 /\ i DIV 256 < 7`
   MP_TAC THENL
   [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = i DIV 256` THEN ABBREV_TAC `t = i MOD 256` THEN
  REWRITE_TAC[ARITH_RULE `q < 7 <=> q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `i:num`
                          then SUBST1_TAC th else NO_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


let V8_SPLIT = prove
 (`!(r:int64) base (x:num->int32) (s:x86state) k.
     (!i. i < 1792 ==> read(memory :> bytes32(word_add r (word(base + 4 * i)))) s = x i) /\
     k < 7
     ==> !i. i < 256
             ==> read(memory :> bytes32(word_add r (word((base + 1024 * k) + 4 * i)))) s =
                 mld_poly_of x k i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * k + i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `base + 4 * (256 * k + i) = (base + 1024 * k) + 4 * i`]);;

let V8_JOIN = prove
 (`!(r:int64) base (f:num->num->int32) (s:x86state).
     (!k i. k < 7 /\ i < 256
            ==> read(memory :> bytes32(word_add r (word((base + 1024 * k) + 4 * i)))) s =
                f k i)
     ==> !i. i < 1792
             ==> read(memory :> bytes32(word_add r (word(base + 4 * i)))) s =
                 mld_polyvec f i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(base + 1024 * i DIV 256) + 4 * i MOD 256 = base + 4 * i`
   (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC);;

let V8_JOIN_TAC (base:int) (f:term) (st:term) =
  MP_TAC(SPECL [`rsp0:int64`; mk_small_numeral base; f; st] V8_JOIN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k < 7 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6`] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC];;

let V8_SPLIT_TAC (base:int) (x:term) (k:int) (st:term) =
  MP_TAC(SPECL [`rsp0:int64`; mk_small_numeral base; x; st; mk_small_numeral k] V8_SPLIT) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC;;

(* 64 bytes from four chunks *)
let V8_BYTES64_OF_CHUNKS = prove
 (`!a:int64 (f:num->byte) s.
        read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
        read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1 /\
        read (memory :> bytes128 (word_add a (word 32))) s = mld_chunk128 f 2 /\
        read (memory :> bytes128 (word_add a (word 48))) s = mld_chunk128 f 3
        ==> read (memory :> bytes(a,64)) s = num_of_bytelist(list_of_seq f 64)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. mld_chunk128 (\j. (f:num->byte)(32 + j)) k = mld_chunk128 f (2 + k)`
   ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mld_chunk128] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `f:num->byte`; `s:x86state`] MLD_BYTES32_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word 32):int64`; `\j. (f:num->byte)(32 + j)`; `s:x86state`]
               MLD_BYTES32_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_ADD_GEN; NUM_OF_BYTELIST_APPEND;
                  LENGTH_LIST_OF_SEQ; ADD_CLAUSES; ETA_AX]);;


(* ------------------------------------------------------------------------- *)
(* The callees and the region lemmas, assumed before the template.           *)
(* ------------------------------------------------------------------------- *)

let V8_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* The loop test at the end of a row (loop12_exit): the index in R13, the
   pointers to t1 (RBX) and to the packed w1 (R15) advanced, RDI and RSI the
   row of w and the matrix structure again, and the branch back to join4,
   or to the jump past the end of the loop for the last row. *)
let V8_LT_STMT = parse_term(subst_tokens ["@MC@",image_mc; "@END@",string_of_int(v8_off 0x2191)]
 "exists f_events. forall e rsp0 pc i (tb:int64) (wp:int64).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\ i < 8
    ==> ensures x86
      (\\s. bytes_loaded s (word pc) @MC@ /\\
           read RIP s = word (pc + mldsa87_verify_internal_loop14_exit) /\\
           read RSP s = rsp0 /\\ read R13 s = word i /\\
           read RBX s = tb /\\ read R15 s = wp /\\
           read events s = e)
      (\\s. read RIP s = word (if i + 1 = 8 then pc + @END@
                              else pc + mldsa87_verify_internal_join4) /\\
           read RSP s = rsp0 /\\ read R13 s = word (i + 1) /\\
           read RBX s = word_add tb (word 320) /\\
           read R15 s = word_add wp (word 128) /\\
           read RDI s = word_add rsp0 (word 2560) /\\
           read RSI s = word_add rsp0 (word 256) /\\
           (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc i /\\
              memaccess_inbounds e2 [] []))
      (MAYCHANGE [RIP; R13; RBX; R15; RDI; RSI] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])");;

let V8_LT_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num) (i:num). f_ev_lt rsp0 pc i :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `i:num`;
                       `tb:int64`; `wp:int64`] THEN
  REWRITE_TAC[fst V8_EXEC; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC V8_EXEC (1--7) THEN
  SUBGOAL_THEN `val (word_add (word i) (word 18446744073709551609):int64) = 0 <=>
                i + 1 = 8`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `i < 8` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_CASES_TAC `i + 1 = 8` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let V8_LT = prove(V8_LT_STMT, V8_LT_TAC);;

(* VM_PRE_TAC, and the 32-bit row index (ECX = R13D for the row of the
   matrix product) as word_zx (word_zx (word i)) = word i *)
let V8_PRE_TAC allowed =
  REPEAT CONJ_TAC THEN
  (fun g -> (TRY(MATCH_MP_TAC WORD_ZX2_SMALL THEN LOCAL_ARITH_TAC THEN NO_TAC) THEN
             VM_PRE_TAC allowed) g);;

let V8_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,V8_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [V8_PRE_TAC VM_ALLOWED; LABEL_TAC name th]);;

(* The precondition aligned 16 (stackpointer + 8) of mld_H, with the stack
   pointer word_sub rsp0 (word 8) after the call, from aligned 32 rsp0 *)
let VM_H_ALIGN_TAC =
  VM_ALIGNED_TAC [] THEN
  SUBGOAL_THEN `aligned 16 (word_add (word_sub rsp0 (word 8)) (word 8):int64)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`];
    ALL_TAC];;

let V8_FCALL_TAC name ilist n =
  V8_CALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC;;

let V8_CALLEES_TAC =
  let [uz0;uz1;uz2;uz3;uz4;uz5;uz6] = VI87_UNPACKZ_LOOPS in
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    VM_ASSUME_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
      "H_CHKNORM" THEN
    VM_ASSUME_TAC MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
    VM_ASSUME_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
      "H_INV" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)
      "H_CHAL" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)
      "H_ROW" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) mcs)
      "H_H87" THEN
    VM_ASSUME_TAC (MP (SPEC_ALL VI87_HINTS) ms) "H_HINTS" THEN
    VM_ASSUME_TAC uz0 "H_UZ0" THEN VM_ASSUME_TAC uz1 "H_UZ1" THEN
    VM_ASSUME_TAC uz2 "H_UZ2" THEN VM_ASSUME_TAC uz3 "H_UZ3" THEN
    VM_ASSUME_TAC uz4 "H_UZ4" THEN VM_ASSUME_TAC uz5 "H_UZ5" THEN
    VM_ASSUME_TAC uz6 "H_UZ6" THEN
    VM_ASSUME_TAC VI87_UNPACKT1_LOOP "H_T1" THEN
    VM_ASSUME_TAC VI87_SHIFTL "H_SHL" THEN
    VM_ASSUME_TAC VI87_PWM_LOOP "H_PWM" THEN
    VM_ASSUME_TAC VI87_SUB_LOOP "H_SUB" THEN
    VM_ASSUME_TAC VI87_REDUCE_LOOP "H_RED" THEN
    VM_ASSUME_TAC VI87_CADDQ_LOOP "H_CADDQ" THEN
    VM_ASSUME_TAC VI87_USEHINT_LOOP "H_USEHINT" THEN
    VM_ASSUME_TAC VI87_PACKW1_LOOP "H_W1PACK" THEN
    VM_ASSUME_TAC VI87_CMP "H_CMP" THEN
    VM_ASSUME_TAC VI87_TR "H_TR" THEN
    VM_ASSUME_TAC VI87_C2 "H_C2" THEN
    VM_ASSUME_TAC V8_LT "H_LT");;

let V8_SETUP_TAC =
  REPEAT GEN_TAC THEN V8_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC V8_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `pre:int64`;
    `prelen:num`; `pk:int64`; `ext:int32`; `sigb:num->byte`; `pkb:num->byte`;
    `M:num`; `PRE':num`; `pc:num`; `rsp0:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              NONOVERLAPPING_CLAUSES; fst V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

(* ------------------------------------------------------------------------- *)
(* From loop1 to the return of the norm check, from state 0 to state 30.     *)
(* ------------------------------------------------------------------------- *)

let V8_Z = parse_term
  "mld_polyvec_unpack 640 mld_polyz_unpack_19 (\\j. (sigb:num->byte)(64 + j))";;

let V8_UZ_TAC k n =
  let off = 64 + 640 * k in
  let offt = mk_small_numeral off in
  VERIF_SLICE_TAC (subst [offt,`off:num`;
     mk_var("s"^string_of_int(n-1),`:x86state`),`s:x86state`]
    `!j. j < 640 ==> read(memory :> bytes8(word_add sig (word(off + j)))) s =
                     (sigb:num->byte)(off + j)`) THEN
  V8_CALL_TAC ("H_UZ"^string_of_int k)
   [subst [offt,`off:num`] `word_add sig (word off):int64`; `rsp0:int64`; `pc:num`;
    subst [offt,`off:num`] `\j. (sigb:num->byte)(off + j)`] n;;

let V8_UNPACK_TAC =
  V8_UZ_TAC 0 1 THEN
  X86_STEPS_TAC V8_EXEC (2--4) THEN V8_UZ_TAC 1 5 THEN
  X86_STEPS_TAC V8_EXEC (6--8) THEN V8_UZ_TAC 2 9 THEN
  X86_STEPS_TAC V8_EXEC (10--12) THEN V8_UZ_TAC 3 13 THEN
  X86_STEPS_TAC V8_EXEC (14--16) THEN V8_UZ_TAC 4 17 THEN
  X86_STEPS_TAC V8_EXEC (18--20) THEN V8_UZ_TAC 5 21 THEN
  X86_STEPS_TAC V8_EXEC (22--25) THEN V8_UZ_TAC 6 26 THEN
  X86_STEPS_TAC V8_EXEC (27--29) THEN
  W(fun (asl,w) ->
    let fs = filter (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `mld_polyz_unpack_19`)) (concl th))
                    (map snd asl) in
    let st = rand(lhs(snd(dest_imp(snd(dest_forall(concl(hd fs))))))) in
    MP_TAC(SPECL [`rsp0:int64`; `sigb:num->byte`; st] V8_VEC7) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  V8_FCALL_TAC "H_CHKNORM" [`read RDI s`; V8_Z; `read RSI s`] 30;;

(* ------------------------------------------------------------------------- *)
(* The norm check fails: join1 sets the result -6.                           *)
(* ------------------------------------------------------------------------- *)

let V8_NORMOK_TM = parse_term V8_NORMOK;;
let V8_OK_TM = parse_term V8_OK;;

let V8_OK_NORM = prove
 (`!sigb pkb mu.
     mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168
       mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 sigb pkb mu
     ==> mld_polyvec_chknorm 7
          (mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(64 + j)))
          (word 524168) = word 0`,
  REWRITE_TAC[mld_verify_internal_ok] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[]);;

let V8_BND_TAC =
  let tm = `word_zx (word 524168:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let V8_NOT_OK_TAC =
  SUBGOAL_THEN (mk_neg V8_OK_TM) (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN(MP_TAC o MATCH_MP V8_OK_NORM) THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let V8_NF_TAC =
  FULL_INIT_TAC THEN V8_UNPACK_TAC THEN V8_BND_TAC THEN
  X86_STEPS_TAC V8_EXEC (31--32) THEN VERIF_PC_TAC [V8_NORMOK_TM] THEN
  X86_STEPS_TAC V8_EXEC (33--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN V8_NOT_OK_TAC THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join3, where mu is ready at rsp0 + 1408.                     *)
(* ------------------------------------------------------------------------- *)

let V8_MU =
  `if ext = (word 0:int32)
   then mld_verify_mu 2592 pkb prelen PRE' mlen M else M MOD 2 EXP 512`;;

let V8_FRAME =
  "read RSP s = rsp0 /\\
   read (memory :> bytes64 (word_add rsp0 (word 248))) s = sig /\\
   read (memory :> bytes128 (word_add rsp0 (word 1344))) s = mld_chunk128 sigb 0 /\\
   read (memory :> bytes128 (word_add rsp0 (word 1360))) s = mld_chunk128 sigb 1 /\\
   read (memory :> bytes128 (word_add rsp0 (word 1376))) s = mld_chunk128 sigb 2 /\\
   read (memory :> bytes128 (word_add rsp0 (word 1392))) s = mld_chunk128 sigb 3 /\\
   (read DF s <=> false) /\\
   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
   read (memory :> bytes(ea,el)) s = ev /\\
   (!j. j < 4627 ==> read(memory :> bytes8(word_add sig (word j))) s = sigb j) /\\
   (!j. j < 2592 ==> read(memory :> bytes8(word_add pk (word j))) s = pkb j)";;

let V8_J3 =
  subst [V8_Z,`VMZ:num->int32`; V8_MU,`VMMU:num`]
  (parse_term ("\\s. " ^ V8_FRAME ^ " /\\
     read RBX s = pk /\\
     (!i. i < 1792 ==> read (memory :> bytes32 (word_add rsp0 (word (5632 + 4 * i)))) s =
                       VMZ i) /\\
     read (memory :> bytes (word_add rsp0 (word 1408),64)) s = VMMU"));;

let V8_COPY_TAC =
  FULL_INIT_TAC THEN VM_M_CHUNKS_TAC THEN VM_ALIGNED_TAC [1408; 1424; 1440; 1456] THEN
  V8_UNPACK_TAC THEN V8_BND_TAC THEN
  X86_STEPS_TAC V8_EXEC (31--32) THEN VERIF_PC_TAC [V8_NORMOK_TM] THEN
  X86_STEPS_TAC V8_EXEC (33--34) THEN VM_EXT_PC_TAC THEN
  YMM_GHOST_TAC `s34:x86state`
   ["YMM0","ymm0_34"; "YMM1","ymm1_34"; "YMM2","ymm2_34"; "YMM3","ymm3_34"] THEN
  X86_STEPS_TAC V8_EXEC (35--43) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_MU_OF_CHUNKS_TAC `word_add rsp0 (word 1408):int64` `s43:x86state` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* ext = 0: tr = SHAKE256(pk) (the region TR, then the 64 bytes of the state *)
(* copied to rsp0 + 3584 and the state zeroed), and mu = H(tr, pre, m) by a  *)
(* call of mld_H87 (steps 35 to 86).                                         *)
(* ------------------------------------------------------------------------- *)

let V8_PKNUM = `num_of_bytelist (list_of_seq (pkb:num->byte) 2592)`;;

let V8_TRNUM = subst [V8_PKNUM,`p:num`]
  `num_of_bytelist (list_of_seq (mld_shake256_byte 2592 p) 64)`;;

let V8_TR_CHUNKS_TAC st =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> wbytes (word_add rsp0 (word 256))) s = x`)
           (concl th)
    then MAP_EVERY (fun k ->
           MP_TAC(SPECL [`word_add rsp0 (word 256):int64`; rhs(concl th);
                         mk_small_numeral k; st] READ_MEMORY_BYTES128_OF_WBYTES) THEN
           ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC th; ARITH_TAC]; ALL_TAC] THEN
           MP_TAC(SPECL [`2592`; V8_PKNUM; mk_small_numeral k] VM_TR_CHUNK) THEN
           ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
           CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
           REWRITE_TAC[WORD_ADD_0; EXP; DIV_1] THEN DISCH_TAC) [0;1;2;3]
    else NO_TAC);;

let V8_TR_OF_CHUNKS_TAC s =
  MP_TAC(SPECL [`word_add rsp0 (word 3584):int64`; V8_TRNUM; `4`; s]
               VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VM_SHAKE_BYTES; MOD_MOD_REFL]);;

let V8_HASH_TAC =
  FULL_INIT_TAC THEN
  VM_ALIGNED_TAC [256; 272; 288; 304; 320; 336; 352; 368; 384; 400; 416; 432; 448;
                  3584; 3600; 3616; 3632] THEN
  V8_UNPACK_TAC THEN V8_BND_TAC THEN
  X86_STEPS_TAC V8_EXEC (31--32) THEN VERIF_PC_TAC [V8_NORMOK_TM] THEN
  X86_STEPS_TAC V8_EXEC (33--34) THEN VM_EXT_PC_TAC THEN
  MP_TAC(SPECL [`pk:int64`; `2592`; `pkb:num->byte`; `s34:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  V8_CALL_TAC "H_TR" [`rsp0:int64`; `pk:int64`; `pc:num`; V8_PKNUM; `pre:int64`] 35 THEN
  V8_TR_CHUNKS_TAC `s35:x86state` THEN
  YMM_GHOST_TAC `s35:x86state`
   ["YMM0","ymm0_35"; "YMM1","ymm1_35"; "YMM2","ymm2_35"; "YMM3","ymm3_35"] THEN
  X86_STEPS_TAC V8_EXEC (36--80) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  V8_TR_OF_CHUNKS_TAC `s80:x86state` THEN
  VM_H_ALIGN_TAC THEN
  V8_FCALL_TAC "H_H87"
   [`read RDI s`; `read RSI s`; `64`; `read RCX s`; `prelen:num`;
    `m:int64`; `mlen:num`;
    subst [V8_PKNUM,`p:num`]
     `val(keccak_f1600 (mld_shake256_state 2592 p)) MOD 2 EXP 512`;
    `PRE':num`; `M:num`] 81 THEN
  X86_STEPS_TAC V8_EXEC (82--86) THEN
  (* mu in the form of the H87 result: its 64-byte output matches
     VM_SHAKE_BYTES, so V8_TR_OF_CHUNKS_TAC has rewritten the H87
     assumption into the keccak form as well (in 65 the output length is a
     parameter) *)
  REWRITE_TAC[mld_verify_mu; VM_SHAKE_BYTES] THEN
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

let V8_ZHAT = mk_comb(`mld_polyvec_map mld_poly_ntt`,V8_Z);;
let V8_C = `num_of_bytelist (list_of_seq (sigb:num->byte) 64)`;;
let V8_CP = mk_comb(`mld_poly_challenge 60 64`,V8_C);;
let V8_CPHAT = mk_comb(`mld_poly_ntt`,V8_CP);;

let V8_PWM = list_mk_comb(`mld_poly_pointwise_montgomery`,[VM_NTT1;V8_CPHAT]);;
let V8_ROWL =
  subst [VM_RHO,`rho:num`; V8_ZHAT,`zhat:num->int32`]
   `mld_polyvec_matrix_row_lazy 7 rho zhat i`;;
let V8_SUBL = list_mk_comb(`mld_poly_sub`,[V8_ROWL;V8_PWM]);;
let V8_REDL = mk_comb(`mld_poly_reduce`,V8_SUBL);;
let V8_INVTL = mk_comb(`mld_poly_invntt_tomont`,V8_REDL);;
let V8_CADDQL = mk_comb(`mld_poly_caddq`,V8_INVTL);;
let V8_HB = `\t. (sigb:num->byte) (4544 + t)`;;
let V8_HINTS = `mld_unpack_hints 75 (\t. (sigb:num->byte) (4544 + t)) i`;;

let V8_W1B =
  subst [VM_RHO,`rho:num`; V8_ZHAT,`zhat:num->int32`;
         V8_CPHAT,`cphat:num->int32`]
   `mld_polyvec_pack 128 mld_polyw1_pack_32
     (mld_polyvec
       (mld_verify_w1 7 mld_poly_use_hint_32 rho zhat cphat pkb 75
         (\t. (sigb:num->byte) (4544 + t))))`;;

(* ------------------------------------------------------------------------- *)
(* From join3 to join4: the NTT of the 7 polynomials of z, rho copied to the *)
(* structure of the matrix, the challenge from c~ and its NTT.               *)
(* ------------------------------------------------------------------------- *)

(* The invariant at join4 for row i, in the form of the 65 proof: the
   registers only while the hints of the rows so far unpack. (The hints code
   of 65 clobbers R12, the constant of the Montgomery multiplication, on the
   way to join1; that of 87 keeps R12 but saves the pointer to t1 at
   rsp0 + 24, so the frame does not state mlen there.) *)
let V8_INV =
  subst [V8_MU,`VMMU:num`; V8_W1B,`VMW1B:num->byte`; VM_RHO,`VMRHO:num`;
         V8_ZHAT,`VMZHAT:num->int32`; V8_CPHAT,`VMCPHAT:num->int32`]
  (parse_term ("\\i s. " ^ V8_FRAME ^ " /\\
     read (memory :> bytes (word_add rsp0 (word 1280),32)) s = VMRHO /\\
     (!j. j < 1792 ==> read (memory :> bytes32 (word_add rsp0 (word (5632 + 4 * j)))) s =
                       VMZHAT j) /\\
     (!j. j < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (4608 + 4 * j)))) s =
                      VMCPHAT j) /\\
     read (memory :> bytes (word_add rsp0 (word 1408),64)) s = VMMU /\\
     ((!j. j < i ==> " ^ "mld_unpack_hints_ok 75 8 (\\t. sigb(4544 + t)) j" ^ ")
      ==> read R12 s = word 0x0380200100000000 /\\
          read R13 s = word i /\\
          read R14 s = word_add rsp0 (word 5632) /\\
          read R15 s = word_add rsp0 (word (3588 + 128 * i)) /\\
          read RSI s = word_add rsp0 (word 256) /\\
          read RDI s = word_add rsp0 (word 2560) /\\
          read RBX s = word_add pk (word (33 + 320 * i)) /\\
          (!j. j < 128 * i
               ==> read (memory :> bytes8 (word_add rsp0 (word (3584 + j)))) s =
                   VMW1B j))"));;

let V8_PC2 =
  parse_term("if " ^ V8_HINTSOK ^
             " then pc + " ^ string_of_int (v8_off 0x2191) ^
             " else pc + mldsa87_verify_internal_join1");;

let V8_MID_TAC =
  FULL_INIT_TAC THEN VM_ALIGNED_TAC [1280; 1296] THEN
  MAP_EVERY (fun k -> V8_SPLIT_TAC 5632 V8_Z k `s0:x86state`) (0--6) THEN
  X86_STEPS_TAC V8_EXEC (1--4) THEN
  V8_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,V8_Z),`0`)] 5 THEN
  MAP_EVERY (fun k ->
    X86_STEPS_TAC V8_EXEC ((3 * k + 3)--(3 * k + 4)) THEN
    V8_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,V8_Z),mk_small_numeral k)]
      (3 * k + 5)) (1--6) THEN
  V8_JOIN_TAC 5632 (mk_abs(`k:num`,mk_comb(`mld_poly_ntt`,
                     mk_comb(mk_comb(`mld_poly_of`,V8_Z),`k:num`)))) `s23:x86state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_polyvec_map]) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`pk:int64`; `2592`; `pkb:num->byte`; `s23:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1] THEN
  YMM_GHOST_TAC `s23:x86state` ["YMM0","ymm0_23"; "YMM1","ymm1_23"] THEN
  X86_STEPS_TAC V8_EXEC (24--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  MP_TAC(SPECL [`word_add rsp0 (word 1280):int64`; `pkb:num->byte`; `s31:x86state`]
               MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`word_add rsp0 (word 1344):int64`; `sigb:num->byte`; `s31:x86state`]
               V8_BYTES64_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  V8_FCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; V8_C] 32 THEN
  X86_STEPS_TAC V8_EXEC (33--34) THEN
  V8_FCALL_TAC "H_NTT" [`read RDI s`; V8_CP] 35 THEN
  X86_STEPS_TAC V8_EXEC (36--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VM_DISCHARGE_TAC;;


(* ------------------------------------------------------------------------- *)
(* The loop body for row i.                                                  *)
(* ------------------------------------------------------------------------- *)

let V8_ACC =
  subst [VM_RHO,`rho:num`; V8_ZHAT,`zhat:num->int32`]
   `mld_polyvec_pointwise_acc_montgomery 7
     (\j. mld_polyvec_matrix_expand 7 rho (1792 * i + j)) zhat`;;
let V8_SUB = list_mk_comb(`mld_poly_sub`,[V8_ACC;V8_PWM]);;
let V8_RED = mk_comb(`mld_poly_reduce`,V8_SUB);;
let V8_INVT = mk_comb(`mld_poly_invntt_tomont`,V8_RED);;
let V8_CADDQ = mk_comb(`mld_poly_caddq`,V8_INVT);;
let V8_UH = list_mk_comb(`mld_poly_use_hint_32`,[V8_CADDQ;V8_HINTS]);;
let V8_HOK_TM = parse_term V8_HOK;;
let V8_HINTSOK_TM = parse_term V8_HINTSOK;;

let V8_ZHAT_BOUND =
  subst [V8_ZHAT,`zhat:num->int32`]
   `!j. j < 1792 ==> abs(ival((zhat:num->int32) j)) < &94279689`;;

let V8_ZHAT_BOUND_TAC =
  SUBGOAL_THEN V8_ZHAT_BOUND ASSUME_TAC THENL
   [MP_TAC(SPECL [`7`; V8_Z] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_Z_UNPACK_BOUND];
    ALL_TAC];;

let V8_CADDQ_TAC =
  FIRST_ASSUM(fun th ->
    if not(is_forall(concl th)) ||
       not(can (find_term ((=) V8_CADDQL)) (concl th))
    then failwith "V8_CADDQ_TAC" else
    SUBGOAL_THEN (subst [V8_CADDQ,V8_CADDQL] (concl th)) ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun nth -> REWRITE_TAC[MP (SPEC `n:num` th) nth] THEN
                            ASSUME_TAC nth) THEN
      MP_TAC(SPECL [`8`; `7`; VM_RHO; V8_ZHAT; V8_PWM; `i:num`; `n:num`]
                   MLD_LAZY_VERIFY) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MLD_LAZY_POINTWISE_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[]];
      ALL_TAC]);;

let V8_ROWS_TAC =
  MP_TAC(BETA_RULE(SPECL [mk_abs(`i:num`,V8_HOK_TM); `8`; `i:num`]
                         VERIF_ROWS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(lhand(concl th)) &&
    fst(dest_forall(lhand(concl th))) = `j:num`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

let V8_LCALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,V8_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [V8_PRE_TAC VM_ALLOWED_LOOP; LABEL_TAC name th]);;

let V8_LFCALL_TAC name ilist n =
  V8_LCALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC;;

(* The constants that the row body loads RIP-relative: the two 64-bit vectors
   of the unpacking of t1 (movq) and the two 128-bit vectors of the reduction
   (aligned movdqa). *)
let V8_CONSTS64 =
  map (fun n -> IMAGE_CONST_RULE_FOR VM_MC (layout n) 64)
   ["mldsa87_verify_internal_const3"; "mldsa87_verify_internal_const4"];;

let V8_CONSTS128 =
  map (fun n -> IMAGE_CONST_RULE_FOR VM_MC (layout n) 128)
   ["mldsa87_verify_internal_const1"; "mldsa87_verify_internal_const2"];;

let V8_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  VERIF_GEN_TAIL_TAC false "front" THEN
  FULL_INIT_TAC THEN V8_ROWS_TAC THEN
  VM_ALIGNED_TAC [256; 1536; 2560; 4608; 5632] THEN
  X86_STEPS_TAC V8_EXEC (1--3) THEN
  V8_LFCALL_TAC "H_ROW"
   [`read RDI s`; `read RSI s`; `read RDX s`; VM_RHO; V8_ZHAT; `i:num`] 4 THEN
  YMM_GHOST_TAC `s4:x86state`
   ["YMM2","ymm2_4"; "YMM3","ymm3_4"; "YMM4","ymm4_4"] THEN
  X86_STEPS_TAC V8_EXEC (5--7) THEN
  IMAGE_RIPREL_TAC (el 0 V8_CONSTS64) (v8_off 0x174e) THEN
  X86_STEPS_TAC V8_EXEC (8--8) THEN
  IMAGE_RIPREL_TAC (el 1 V8_CONSTS64) (v8_off 0x1756) THEN
  X86_STEPS_TAC V8_EXEC (9--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  VM_SLICE_TAC
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word((32 + 320 * i) + j)))) s10 =
            (pkb:num->byte)(32 + 320 * i + j)` THEN
  V8_LCALL_TAC "H_T1"
   [`word_add pk (word(32 + 320 * i)):int64`; `rsp0:int64`; `pc:num`;
    `\j. (pkb:num->byte)(32 + 320 * i + j)`] 11 THEN
  V8_LCALL_TAC "H_SHL" [`rsp0:int64`; `pc:num`; VM_T1] 12 THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = word x`) (concl th)
    then CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th else th) THEN
  X86_STEPS_TAC V8_EXEC (13--14) THEN
  V8_LFCALL_TAC "H_NTT" [`read RDI s`; VM_SHL] 15 THEN
  X86_STEPS_TAC V8_EXEC (16--17) THEN
  V8_LCALL_TAC "H_PWM" [`rsp0:int64`; `pc:num`; VM_NTT1; V8_CPHAT] 18 THEN
  YMM_GHOST_TAC `s18:x86state` ["YMM5","ymm5_18"; "YMM6","ymm6_18"] THEN
  X86_STEPS_TAC V8_EXEC (19--20) THEN
  IMAGE_RIPREL_TAC (el 0 V8_CONSTS128) (v8_off 0x1e29) THEN
  X86_STEPS_TAC V8_EXEC (21--21) THEN
  IMAGE_RIPREL_TAC (el 1 V8_CONSTS128) (v8_off 0x1e31) THEN
  X86_STEPS_TAC V8_EXEC (22--23) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  V8_LCALL_TAC "H_SUB" [`rsp0:int64`; `pc:num`; V8_ROWL; V8_PWM] 24 THEN
  X86_STEPS_TAC V8_EXEC (25--26) THEN
  V8_LCALL_TAC "H_RED" [`rsp0:int64`; `pc:num`; V8_SUBL] 27 THEN
  X86_STEPS_TAC V8_EXEC (28--28) THEN
  V8_LFCALL_TAC "H_INV" [`read RDI s`; V8_REDL] 29 THEN
  X86_STEPS_TAC V8_EXEC (30--31) THEN
  V8_LCALL_TAC "H_CADDQ" [`rsp0:int64`; `pc:num`; V8_INVTL] 32 THEN
  V8_CADDQ_TAC THEN
  VM_SLICE_TAC
   `!j. j < 83
        ==> read(memory :> bytes8(word_add sig (word(4544 + j)))) s32 =
            (sigb:num->byte)(4544 + j)` THEN
  V8_LCALL_TAC "H_HINTS"
   [`sig:int64`; `rsp0:int64`; `pc:num`; V8_HB; `i:num`;
    `word_add pk (word(33 + 320 * i)):int64`] 33;;

let V8_PC_OK_TAC =
  ASM_CASES_TAC `i + 1 < 8` THENL
   [SUBGOAL_THEN `~(i + 1 = 8)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i + 1 < 8`; ASSUME `~(i + 1 = 8)`];
    SUBGOAL_THEN `i + 1 = 8` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN V8_HINTSOK_TM ASSUME_TAC THENL
     [VERIF_IMP_CASE_TAC `~(i + 1 < 8)`; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~(i + 1 < 8)`; ASSUME `i + 1 = 8`;
                ASSUME V8_HINTSOK_TM]];;

let V8_JOIN_W1_TAC =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[MATCH_MP (SPEC_ALL VERIF_W1B_ROW_32) (ASSUME `k < 128`)] THEN
    REWRITE_TAC[mld_verify_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(fun th ->
      MATCH_MP_TAC(REWRITE_RULE[GSYM ADD_ASSOC] th)) THEN
    FIRST_ASSUM ACCEPT_TAC];;

let V8_BODY_OK_TAC =
  VERIF_MP_CASE_TAC V8_HOK_TM THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  V8_LCALL_TAC "H_USEHINT" [`rsp0:int64`; `pc:num`; V8_CADDQ; V8_HINTS] 34 THEN
  V8_LCALL_TAC "H_W1PACK"
   [`rsp0:int64`; `word_add rsp0 (word (3584 + 128 * i)):int64`;
    `pc:num`; V8_UH] 35 THEN
  V8_LCALL_TAC "H_LT"
   [`rsp0:int64`; `pc:num`; `i:num`; `word_add pk (word (33 + 320 * i)):int64`;
    `word_add rsp0 (word (3588 + 128 * i)):int64`] 36 THEN
  VERIF_FINAL_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(V8_PC_OK_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN V8_JOIN_W1_TAC THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN
  VM_EVENTS_TAC [`front:(uarch_event)list`];;

let V8_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg V8_HOK_TM) THEN VERIF_FINAL_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg V8_HOK_TM)] THEN NO_TAC) THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN
  VM_EVENTS_TAC [`front:(uarch_event)list`];;

let V8_BODY_TAC =
  V8_BODY1_TAC THEN
  ASM_CASES_TAC V8_HOK_TM THEN VERIF_PC_TAC [V8_HOK_TM] THENL
   [V8_BODY_OK_TAC; V8_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop. All hints unpack: c2 = H(mu, w1') (the region C2, 64      *)
(* bytes copied to rsp0 + 1472), and the comparison of c~ and c2 (the region *)
(* CMP). Some do not: join1 sets -6.                                         *)
(* ------------------------------------------------------------------------- *)

let V8_OK_THM = GEN_ALL(prove
 (subst [V8_W1B,`w1b:num->byte`]
  `mld_verify_internal_ok 8 7 64 mld_polyz_unpack_19 640 524168
       mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60 (sigb:num->byte)
       (pkb:num->byte) mu <=>
     mld_polyvec_chknorm 7
       (mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(64 + j)))
       (word 524168) = word 0 /\
     (!i. i < 8 ==> mld_unpack_hints_ok 75 8 (\t. sigb(4544 + t)) i) /\
     (!j. j < 64
          ==> sigb j =
              mld_shake256_byte 1088
               (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b 1024)) j)`,
  REWRITE_TAC[mld_verify_internal_ok; VM_HRET] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `64 + 7 * 640 + t = 4544 + t`;
              ARITH_RULE `64 + 8 * 128 = 1088`; ARITH_RULE `8 * 128 = 1024`]));;


let V8_W1NUM =
  mk_comb(`num_of_bytelist`,
          mk_comb(mk_comb(`list_of_seq:(num->byte)->num->byte list`,V8_W1B),
                  `1024`));;

let V8_SQ = subst [V8_MU,`mu:num`; V8_W1NUM,`w:num`]
  `mld_shake256_byte 1088 (mu + 2 EXP 512 * w)`;;

(* c2 = H(mu, w1') is inlined: the region C2 (inline_verify87.ml) absorbs
   mu || w1' into the state at rsp0 + 32, the code copies the first 64 bytes
   of the state to rsp0 + 1472 and zeroes the state, and CMP87 compares them
   with c~ *)
let V8_C2P = subst [V8_MU,`mu:num`; V8_W1NUM,`w:num`] `mu + 2 EXP 512 * w`;;
let V8_C2NUM = subst [V8_C2P,`p:num`]
  `num_of_bytelist (list_of_seq (mld_shake256_byte 1088 p) 64)`;;

(* After the chunks of c2 at rsp0 + 1472 are turned into bytes, drop their
   first form (from the state of C2) so that the call of CMP87 sees them as
   chunks of the bytes of c2 *)
let V8_DROP_C2_WORDS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let pat = `read (memory :> bytes128 (word_add rsp0 (word k))) s = word (x:num):int128` in
    let c = concl th in
    if can (term_match [] pat) c &&
       mem (dest_small_numeral (rev_assoc `k:num` ((fun (_,i,_) -> i) (term_match [] pat c))))
           [1472; 1488; 1504; 1520]
    then ALL_TAC else NO_TAC));;

let V8_POST_OK_TAC =
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`word_add rsp0 (word 3584):int64`; `1024`; V8_W1B; `s0:x86state`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_32`)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  X86_STEPS_TAC V8_EXEC (1--1) THEN
  V8_CALL_TAC "H_C2" [`rsp0:int64`; `pc:num`; V8_MU; V8_W1NUM] 2 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> wbytes (word_add rsp0 (word 32))) s = x`)
           (concl th)
    then MAP_EVERY (fun k ->
           MP_TAC(SPECL [`word_add rsp0 (word 32):int64`; rhs(concl th);
                         mk_small_numeral k; `s2:x86state`] READ_MEMORY_BYTES128_OF_WBYTES) THEN
           ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC th; ARITH_TAC]; ALL_TAC] THEN
           MP_TAC(SPECL [`1088`; V8_C2P; mk_small_numeral k] VM_TR_CHUNK) THEN
           ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
           CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
           REWRITE_TAC[WORD_ADD_0; EXP; DIV_1] THEN DISCH_TAC) [0;1;2;3]
    else NO_TAC) THEN
  VM_ALIGNED_TAC [32; 48; 64; 80; 96; 112; 128; 144; 160; 176; 192; 208; 224;
                  1344; 1472; 1488; 1504; 1520] THEN
  YMM_GHOST_TAC `s2:x86state`
   ["YMM0","ymm0_2"; "YMM1","ymm1_2"; "YMM2","ymm2_2"; "YMM3","ymm3_2"] THEN
  X86_STEPS_TAC V8_EXEC (3--37) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  MP_TAC(SPECL [`word_add rsp0 (word 1472):int64`; V8_C2NUM; `4`; `s37:x86state`]
               VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(word_add rsp0 (word 1472),64)) s = x MOD n`)
           (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES
           (REWRITE_RULE[MATCH_MP MOD_LT
              (REWRITE_RULE[LENGTH_LIST_OF_SEQ; ARITH_RULE `256 EXP 64 = 2 EXP 512`]
                 (ISPEC (rand(lhand(rhs(concl th)))) NUM_OF_BYTELIST_BOUND))] th))
    else NO_TAC) THEN
  V8_DROP_C2_WORDS_TAC THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`word_add rsp0 (word 1472):int64`; `64`; V8_SQ; `s37:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    DISCH_TAC) [0;1;2;3] THEN
  V8_CALL_TAC "H_CMP"
   [`rsp0:int64`; `pc:num`; `mld_chunk128 sigb 0`; `mld_chunk128 sigb 1`;
    `mld_chunk128 sigb 2`; `mld_chunk128 sigb 3`;
    mk_comb(mk_comb(`mld_chunk128`,V8_SQ),`0`);
    mk_comb(mk_comb(`mld_chunk128`,V8_SQ),`1`);
    mk_comb(mk_comb(`mld_chunk128`,V8_SQ),`2`);
    mk_comb(mk_comb(`mld_chunk128`,V8_SQ),`3`)] 38 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[V8_OK_THM; ASSUME V8_NORMOK_TM; EQT_INTRO(ASSUME V8_HINTSOK_TM)] THEN
  MP_TAC(ISPECL [`sigb:num->byte`; V8_SQ; `4`] MLD_CHUNK128_EQ) THEN
  CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 = 64`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN VM_EVENTS_TAC [`old:(uarch_event)list`];;


let V8_POST_HF_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC V8_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[V8_OK_THM] THEN
  TRY(VM_MAYCHANGE_TAC THEN NO_TAC) THEN VERIF_EVENTS_ONLY_TAC THEN VM_EVENTS_TAC [`old:(uarch_event)list`];;

let V8_POST_TAC =
  VERIF_GEN_TAIL_TAC true "old" THEN
  ASM_CASES_TAC V8_HINTSOK_TM THENL
   [REWRITE_TAC[EQT_INTRO(ASSUME V8_HINTSOK_TM); ARITH_RULE `0 < 8`] THEN
    V8_POST_OK_TAC;
    REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg V8_HINTSOK_TM))] THEN
    V8_POST_HF_TAC];;

(* ------------------------------------------------------------------------- *)
(* The body as a whole.                                                      *)
(* ------------------------------------------------------------------------- *)

let V8_MAIN_TAC =
  V8_SETUP_TAC THEN V8_ZHAT_BOUND_TAC THEN
  ASM_CASES_TAC V8_NORMOK_TM THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[if is_neg(concl th) then th else EQT_INTRO th]) THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term V8_K)
     `pc + mldsa87_verify_internal_join4` V8_PC2 V8_INV THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                  CONJUNCT1 LT; LT_REFL] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa87_verify_internal_join3` V8_J3 THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC `ext = (word 0:int32)` THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[if is_neg(concl th) then th else EQT_INTRO th]) THEN
        FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM VAL_EQ_0] o
                      check (fun th -> concl th = `ext = (word 0:int32)` ||
                                       concl th = `~(ext = (word 0:int32))`)) THENL
         [V8_HASH_TAC; V8_COPY_TAC];
        V8_MID_TAC];
      V8_BODY_TAC;
      V8_POST_TAC];
    V8_NF_TAC];;

let VI87_MAIN = prove(V8_STMT, V8_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

let VI87_TOP_TEMPLATE = VI44_TOP_TEMPLATE;;

let VI87_TOP_CALL_TAC name ilist n =
  FULL_CALL_TAC VM_MC V8_EXEC name ilist VI44_TOP_ALLOWED n;;

let VI87_TOP_A0_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPEC_ALL VI87_MAIN) th) "H_MAIN" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPEC_ALL VI87_CLEANUP) (CONJUNCT1 th))
      "H_CL") THEN
  CONCRETIZE_F_EVENTS_TAC VI87_TOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 14517 THEN REALIGN_FRAME_TAC 14565 14517 THEN
  REALIGN_NONOV_TAC 14486
   [`sig:int64,4627`; `m:int64,mlen:num`; `pre:int64,prelen:num`;
    `pk:int64,2592`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 14517):int64,48`;
    `word_add stackpointer (word 14565):int64,8`;
    `word_add stackpointer (word 14573):int64,4`] THEN
  REALIGN_ALIGNED_TAC [2998; 3014; 3030; 3046] THEN
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
    REWRITE_TAC[WORD_RULE `word_add bot (word 14486):int64 =
                           word_add (word_add bot (word 1654)) (word 12832)`] THEN
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

let VI87_TOP_A1_TAC =
  FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes32 a) s0 = ext`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th) THEN
  YMM_GHOST_TAC `s0:x86state`
   ["YMM0","ymm0_0"; "YMM1","ymm1_0"; "YMM2","ymm2_0"; "YMM3","ymm3_0"] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `4627`; `sigb:num->byte`; `s0:x86state`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1;2;3] THEN
  X86_STEPS_TAC V8_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  MAP_EVERY (fun k ->
    SUBGOAL_THEN (subst [mk_small_numeral k,`k:num`]
      `aligned 16 (word_add (word_add bot (word 1654)) (word k):int64)`)
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC]) [1344;1360;1376;1392] THEN
  X86_STEPS_TAC V8_EXEC (9--32) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]);;

let VI87_TOP_B_TAC =
  VI87_TOP_CALL_TAC "H_MAIN"
   [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`; `pk:int64`;
    `ext:int32`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `PRE':num`;
    `pc:num`; VI44_RSP0] 33;;

let VI87_TOP_C_TAC =
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                      `word_add bot (word 1646):int64,12840`),r))
     ASSUME_TAC THENL
     [EXPAND_TAC "bot" THEN NONOVERLAPPING_TAC; ALL_TAC])
   [`word pc:int64,libmldsa_size`; `word(pc + got_memset):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 14517):int64,56`] THEN
  VI87_TOP_CALL_TAC "H_CL"
   [VI44_RSP0; `word_add stackpointer (word 14517):int64`; `read R14 s`; `pc:num`;
    `rbx_init:int64`; `r12_init:int64`; `r13_init:int64`; `r14_init:int64`;
    `r15_init:int64`; `rbp_init:int64`; `returnaddress:int64`] 34 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let VI87_TOP_TAC = VI87_TOP_A0_TAC THEN VI87_TOP_A1_TAC THEN VI87_TOP_B_TAC THEN VI87_TOP_C_TAC;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  VI87_TOP_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
