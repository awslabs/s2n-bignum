(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The stages of an attempt of mldsa65_signature_internal (clang 23 -O3 mono *)
(* reduced-RAM), as FULL lemmas for segments of the code at the frame rsp0   *)
(* of the attempt, made from those of signature_internal_44_stages.ml for    *)
(* the parameters of ML-DSA-65 (K = 6, L = 5), with the region lemmas of     *)
(* signature_internal_65_inline.ml. The frame of the attempt is 12576 bytes  *)
(* at rsp0, and the callees use the 1471 bytes below it.                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_stage2.ml";;

let SI65_FRAME = 14047;;

(* ------------------------------------------------------------------------- *)
(* s2 and t0 in the NTT domain, from the secret key skb (as in the gcc       *)
(* proof, SIGN65_S2H and SIGN65_T0H).                                        *)
(* ------------------------------------------------------------------------- *)

let SI65_S2H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. (skb:num->byte)(768 + j)))`;;

let SI65_T0H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(1536 + j)))`;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over the rows of w0 (RIT), from loop51 with row *)
(* j in R12, its address in R13 and the offsets of s2_j and t0_j in the key  *)
(* in R15 and R14: s2_j unpacked into the scratch polynomial at rsp0 + 0x220 *)
(* and transformed, its product with the challenge, w0_j - c s2_j in place   *)
(* and reduced, its norm check; then t0_j likewise, c t0_j reduced and       *)
(* checked, and the sum in place in row j. ok1 and ok2 are the results of    *)
(* the two checks (ok2 matters only when ok1 holds): if both pass, the code  *)
(* goes back to loop51 or, after the last row, to loop51_exit1, else to the  *)
(* rejection at join19. On success XMM4 is 0 and XMM5 holds the constant of  *)
(* the unpacking of w1 that follows the loop. The callees (NTT, inverse NTT) *)
(* use the stack below rsp0.                                                 *)
(* ------------------------------------------------------------------------- *)

let R65_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_32`; `w:num->int32`; SI65_S2H; `cphat:num->int32`; `j:num`]);;
let R65_CT0 = list_mk_comb(`mld_sign_ct0`, [SI65_T0H; `cphat:num->int32`; `j:num`]);;

let SI65_RIT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@R0@",string_of_term R65_R0; "@CT0@",string_of_term R65_CT0;
   "@FAIL@",string_of_int(layout "mldsa65_signature_internal_join19")]
 "exists f_events.
    forall e ok1 ok2 sk skb rsp0 j w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\ j < 6 /\\
      (ok1 <=> mld_poly_chknorm (@R0@) (word 261692) = word 0) /\\
      (ok1 ==> (ok2 <=> mld_poly_chknorm (@CT0@) (word 261888) = word 0)) /\\
      ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
          [(sk,4032); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_loop51) /\\
                read RSP s = rsp0 /\\ read R12 s = word j /\\ read R15 s = word (128 * j) /\\
                read R14 s = word (12 + 416 * j) /\\
                read R13 s = word_add rsp0 (word (5376 + 1024 * j)) /\\
                read RBX s = word 0x0380200100000000 /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 768) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 1536) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * i)))) s =
                                 cphat i) /\\
                (!i. i < 4032 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                (!i. i < 256 ==> read (memory :> bytes32
                                   (word_add rsp0 (word ((5376 + 1024 * j) + 4 * i)))) s =
                                 mld_poly_decompose_lo_32 (mld_poly_of w j) i) /\\
                read events s = e)
           (\\s. read RIP s =
                (if ok1 /\\ ok2
                 then (if j + 1 < 6 then word (pc + mldsa65_signature_internal_loop51)
                       else word (pc + mldsa65_signature_internal_loop51_exit1))
                 else word (pc + @FAIL@)) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                (ok1 /\\ ok2
                 ==> read R12 s = word (j + 1) /\\ read R15 s = word (128 * (j + 1)) /\\
                     read R14 s = word (12 + 416 * (j + 1)) /\\
                     read R13 s = word_add rsp0 (word (5376 + 1024 * (j + 1))) /\\
                     read XMM4 s = word 0 /\\
                     read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
                     (!i. i < 256 ==> read (memory :> bytes32
                                        (word_add rsp0 (word ((5376 + 1024 * j) + 4 * i)))) s =
                                      mld_poly_add (@R0@) (@CT0@) i)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok1 ok2 sk rsp0 j pc /\\
                   memaccess_inbounds e2
                    [sk,4032; word_sub rsp0 (word 1471),14047;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 16),16);
                       memory :> bytes(word_add rsp0 (word 24),8);
                       memory :> bytes(word_add rsp0 (word 160),8);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word (5376 + 1024 * j)),1024)])");;

let SI65_RIT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_loop51", layout "mldsa65_signature_internal_loop51_exit1")];;

let R65_TEMPLATE =
 `\(ok1:bool) (ok2:bool) (sk:int64) (rsp0:int64) (j:num) (pc:num).
   if ok1 then
    (if ok2 then (if j + 1 < 6 then f_ev_mid sk rsp0 j pc else f_ev_last sk rsp0 j pc)
     else f_ev_f2 sk rsp0 j pc)
   else f_ev_f1 sk rsp0 j pc :(uarch_event)list`;;

let R65_ALLOWED = [`ok1:bool`; `ok2:bool`; `sk:int64`; `rsp0:int64`; `j:num`; `pc:num`];;

let R65_CALL_TAC = SI_GCALL_TAC SI65_RIT_EXEC R65_ALLOWED ALL_TAC;;
let R65_FCALL_TAC = SI_GFCALL_TAC SI65_RIT_EXEC R65_ALLOWED ALL_TAC;;

let R65_RCONST_TAC = SI_RCONST_TAC "mldsa65_signature_internal"
  ["mldsa65_signature_internal_const1"; "mldsa65_signature_internal_const2"] ["YMM5"; "YMM6"];;

let R65_B = `word_add rsp0 (word (5376 + 1024 * j)):int64`;;
let R65_S2I = mk_comb(mk_comb(`mld_poly_of`,SI65_S2H),`j:num`);;
let R65_T0I = mk_comb(mk_comb(`mld_poly_of`,SI65_T0H),`j:num`);;
let R65_PW1 = list_mk_comb(`mld_poly_pointwise_montgomery`,[R65_S2I; `cphat:num->int32`]);;
let R65_PW2 = list_mk_comb(`mld_poly_pointwise_montgomery`,[R65_T0I; `cphat:num->int32`]);;
let R65_W0J = `mld_poly_decompose_lo_32 (mld_poly_of (w:num->int32) j)`;;
let R65_CS2 = mk_comb(`mld_poly_invntt_tomont`,R65_PW1);;
let R65_SUBX = list_mk_comb(`mld_poly_sub`,[R65_W0J; R65_CS2]);;

(* bytes off .. off + n - 1 of the secret key at state st *)
let R65_SLICE_TAC off n st =
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `4032`; off; n; st] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `j < 6` THEN ARITH_TAC; DISCH_TAC];;

let R65_TEST = SI_TEST_RULE 6;;

(*** w0_j - c s2_j: steps 1 to 26 ***)

let R65_PART1_TAC =
  X86_STEPS_TAC SI65_RIT_EXEC (1--4) THEN
  R65_SLICE_TAC `768 + 128 * j` `128` `s4:x86state` THEN
  R65_CALL_TAC "H_ETA" [`word_add sk (word (768 + 128 * j)):int64`; `rsp0:int64`; `pc:num`;
                        `\i. (skb:num->byte)((768 + 128 * j) + i)`] 5 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_4` THEN
  X86_STEPS_TAC SI65_RIT_EXEC (6--7) THEN
  R65_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. (skb:num->byte)(768 + j))) j`] 8 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI65_RIT_EXEC (9--10) THEN
  R65_CALL_TAC "H_PWM1" [`rsp0:int64`; `pc:num`; R65_S2I; `cphat:num->int32`] 11 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (12--13) THEN
  R65_FCALL_TAC "H_INV" [`read RDI s`; R65_PW1] 14 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (15--16) THEN
  R65_CALL_TAC "H_SUB" [R65_B; `rsp0:int64`; `pc:num`; R65_W0J; R65_CS2] 17 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (18--18) THEN R65_RCONST_TAC 18 0x2365 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (19--21) THEN
  R65_CALL_TAC "H_RED1" [R65_B; `pc:num`; R65_SUBX] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  X86_STEPS_TAC SI65_RIT_EXEC (23--25) THEN
  R65_CALL_TAC "H_CHK1" [R65_B; `pc:num`; R65_R0] 26;;

(*** c t0_j, once the first check passed: steps 29 to 56 ***)

let R65_PART2_TAC =
  SI_PASS_TAC `ok1:bool` THEN
  X86_STEPS_TAC SI65_RIT_EXEC (29--34) THEN
  R65_SLICE_TAC `1536 + 416 * j` `416` `s34:x86state` THEN
  R65_CALL_TAC "H_T0U" [`word_add sk (word (1536 + 416 * j)):int64`; `rsp0:int64`; `pc:num`;
                        `\i. (skb:num->byte)((1536 + 416 * j) + i)`] 35 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyt0_unpack` THEN
  X86_STEPS_TAC SI65_RIT_EXEC (36--37) THEN
  R65_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(1536 + j))) j`] 38 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI65_RIT_EXEC (39--41) THEN
  R65_CALL_TAC "H_PWM2" [`rsp0:int64`; `pc:num`; R65_T0I; `cphat:num->int32`] 42 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (43--44) THEN
  R65_FCALL_TAC "H_INV" [`read RDI s`; R65_PW2] 45 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (46--46) THEN R65_RCONST_TAC 46 0x26fb THEN
  X86_STEPS_TAC SI65_RIT_EXEC (47--50) THEN
  R65_CALL_TAC "H_RED2" [`rsp0:int64`; `pc:num`; mk_comb(`mld_poly_invntt_tomont`,R65_PW2)] 51 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  X86_STEPS_TAC SI65_RIT_EXEC (52--53) THEN
  YMM_GHOST_TAC `s53:x86state` ["YMM4","ymm4_53"] THEN
  X86_STEPS_TAC SI65_RIT_EXEC (54--55) THEN
  R65_CALL_TAC "H_CHK2" [`rsp0:int64`; `pc:num`; R65_CT0] 56 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (57--57) THEN
  SI_RCONST_TAC "mldsa65_signature_internal" ["mldsa65_signature_internal_const3"] ["YMM5"]
    57 0x27ef THEN
  X86_STEPS_TAC SI65_RIT_EXEC (58--59);;

(*** the sum, once both checks passed, and the back edge: steps 60 to 68 ***)

let R65_PART3_TAC =
  SI_PASS_TAC `ok2:bool` THEN
  X86_STEPS_TAC SI65_RIT_EXEC (60--61) THEN
  R65_CALL_TAC "H_ADD" [R65_B; `rsp0:int64`; `pc:num`; R65_CT0; R65_R0] 62 THEN
  X86_STEPS_TAC SI65_RIT_EXEC (63--68) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP R65_TEST (ASSUME `j < 6`)]) THEN
  ASM_CASES_TAC `j + 1 < 6` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(SI_WORD_ADD_TAC THEN NO_TAC) THEN TRY(SI_XMM_PRE_TAC THEN NO_TAC) THEN
  SI_END_TAC 1471;;

let SI65_RIT = prove
 (SI65_RIT_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [SI65_ETA52,"H_ETA"; SI65_PWM53,"H_PWM1"; SI65_SUB54,"H_SUB"; SI65_RED55,"H_RED1";
    SI65_CHK56,"H_CHK1"; SI65_T0U57,"H_T0U"; SI65_PWM58,"H_PWM2"; SI65_RED59,"H_RED2";
    SI65_CHK60,"H_CHK2"; SI65_ADD61,"H_ADD";
    MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"] THEN
  CONCRETIZE_F_EVENTS_TAC R65_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok1:bool`; `ok2:bool`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `j:num`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst SI65_RIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ORIENT_TAC THEN SI_ALIGNED16_TAC [0x220; 0x2d00] THEN
  SI_ROW_ALIGNED_TAC 5376 THEN
  FULL_INIT_TAC THEN R65_PART1_TAC THEN
  X86_STEPS_TAC SI65_RIT_EXEC (27--28) THEN SI_DECIDE_TAC `ok1:bool` THEN
  ASM_CASES_TAC `ok1:bool` THENL [ALL_TAC; SI_FAIL_TAC 1471 `ok1:bool`] THEN
  R65_PART2_TAC THEN SI_DECIDE_TAC `ok2:bool` THEN
  ASM_CASES_TAC `ok2:bool` THENL [ALL_TAC; SI_FAIL_TAC 1471 `ok2:bool`] THEN
  R65_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass (RPRE), from the exit of the loop over z (+0x21e1), where the code   *)
(* sets up row 0, as gcc's SIGN65_RPRE: row j of w holds w0_j - c s2_j +     *)
(* c t0_j afterwards (mld_sign_hint_x), the rows after the first m are      *)
(* unchanged. After a row, XMM4 and XMM5 are as RIT leaves them.             *)
(* ------------------------------------------------------------------------- *)

let RP65_R0 = R65_R0;;
let RP65_CT0 = R65_CT0;;
let RP65_HX = list_mk_comb(`mld_sign_hint_x 6 mld_poly_decompose_lo_32`,
  [`w:num->int32`; SI65_S2H; SI65_T0H; `cphat:num->int32`]);;

let SI65_RSTART = layout "mldsa65_signature_internal" + 0x21e1;;

let SI65_RPRE_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@R0@",string_of_term RP65_R0; "@CT0@",string_of_term RP65_CT0;
   "@HX@",string_of_term RP65_HX; "@START@",string_of_int SI65_RSTART]
 "exists f_events.
    forall e m sk skb rsp0 w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\ m <= 6 /\\
      (!j. j < m ==> mld_poly_chknorm (@R0@) (word 261692) = word 0 /\\
                     mld_poly_chknorm (@CT0@) (word 261888) = word 0) /\\
      ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
          [(sk,4032); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @START@) /\\
                read RSP s = rsp0 /\\
                read RBX s = word 0x0380200100000000 /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 768) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 1536) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * i)))) s =
                                 cphat i) /\\
                (!i. i < 4032 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                (!i. i < 1536 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                read events s = e)
           (\\s. read RIP s =
                (if m < 6 then word (pc + mldsa65_signature_internal_loop51)
                 else word (pc + mldsa65_signature_internal_loop51_exit1)) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                read R12 s = word m /\\ read R15 s = word (128 * m) /\\
                read R14 s = word (12 + 416 * m) /\\
                read R13 s = word_add rsp0 (word (5376 + 1024 * m)) /\\
                (0 < m ==> read XMM4 s = word 0 /\\
                           read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f) /\\
                (!i. i < 256 * m ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                     @HX@ i) /\\
                (!i. 256 * m <= i /\\ i < 1536
                     ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sk rsp0 pc /\\
                   memaccess_inbounds e2
                    [sk,4032; word_sub rsp0 (word 1471),14047;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 16),16);
                       memory :> bytes(word_add rsp0 (word 24),8);
                       memory :> bytes(word_add rsp0 (word 160),8);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word 5376),6144)])");;

let SI65_RPRE_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(SI65_RSTART, layout "mldsa65_signature_internal_loop51_exit1")];;

let RP65_INV = parse_term(subst_tokens ["@HX@",string_of_term RP65_HX]
 "\\i s. read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
       read R12 s = word i /\\ read R15 s = word (128 * i) /\\
       read R14 s = word (12 + 416 * i) /\\
       read R13 s = word_add rsp0 (word (5376 + 1024 * i)) /\\
       (0 < i ==> read XMM4 s = word 0 /\\
                  read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f) /\\
       read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 768) /\\
       read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 1536) /\\
       (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * k)))) s =
                        cphat k) /\\
       (!k. k < 4032 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
       (!k. k < 256 * i ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) s =
                            @HX@ k) /\\
       (!k. 256 * i <= k /\\ k < 1536
            ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) s =
                mld_polyvec_map mld_poly_decompose_lo_32 w k)");;

let RP65_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 6` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`rsp0:int64`; `5376`; `1536`; `mld_poly_decompose_lo_32`;
                `w:num->int32`; `i:num`; `s0:x86state`] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; `s0:x86state`]
             `!k. 256 * i <= k /\ k < 1536
                  ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) s0 = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 6` THEN ARITH_TAC; STRIP_TAC] THEN
  REMOVE_THEN "H_RIT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI65_RPRE_EXEC,0x0,VM_MC,th)
      [`e:(uarch_event)list`; `T`; `T`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `i:num`;
       `w:num->int32`; `cphat:num->int32`; `pc:num`] 1 THENL
     [REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC [`sk:int64`; `rsp0:int64`; `i:num`; `pc:num`];
      LABEL_TAC "H_RIT" th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI_LOOP_PC (CONJ (ASSUME `i < m`) (ASSUME `m <= 6`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `0 < i + 1`] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let RP65_START_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC SI65_RPRE_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; LT_REFL];;

let SI65_RPRE = prove
 (SI65_RPRE_STMT,
  SI_ASSUME_CALLEE_TAILED_TAC SI65_RIT "H_RIT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sk:int64) (rsp0:int64) (pc:num).
     APPEND (f_ev_back m sk rsp0 pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit sk rsp0 pc i)) (f_ev_front sk rsp0 pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_RPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop51`
     `if m < 6 then pc + mldsa65_signature_internal_loop51
      else pc + mldsa65_signature_internal_loop51_exit1`
     RP65_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0; LT_REFL] THEN
      RP65_START_TAC THEN SI_DISCHARGE_TAC 1471;
      RP65_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN RP65_START_TAC THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI_DISCHARGE_TAC 1471]);;

(* ------------------------------------------------------------------------- *)
(* s1 in the NTT domain and y, as in the gcc proof (SIGN65_S1H, SIGN65_YK).   *)
(* ------------------------------------------------------------------------- *)

let SI65_S1H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. (skb:num->byte)(128 + j)))`;;

let SI65_YK = `mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa`;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over z (ZIT), from join11 with i in R15, the    *)
(* offset of s1_i in RCX and the output pointer of the packing (sig + 48 +   *)
(* 640 i, plus 3) in R8: s1_i unpacked into z at rsp0 + 0x720 and            *)
(* transformed, its product with the challenge, y_i sampled again (absorbing *)
(* rho'' || kappa + i, squeezing, unpacking at rsp0 + 0x220 and zeroing the  *)
(* state), z_i = c s1_i + y_i reduced, its norm check (ok), and, if it       *)
(* passes, z_i packed into the signature; then back to join11 or, after the  *)
(* last, to the setup of the rows (+0x21e1); a failed check goes to the      *)
(* rejection at join35 with R15 = 0.                                         *)
(* ------------------------------------------------------------------------- *)

let Z65_ZI = list_mk_comb(`mld_sign_z`, [SI65_S1H; `cphat:num->int32`; SI65_YK; `i:num`]);;

let SI65_ZNEXT = layout "mldsa65_signature_internal" + 0x21e1;;

let SI65_ZIT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@ZI@",string_of_term Z65_ZI; "@NEXT@",string_of_int SI65_ZNEXT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e ok sig sk skb rsp0 rhop kappa i cphat pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ i < 5 /\\
          (mld_poly_chknorm (@ZI@) (word 524092) = word 0 <=> ok) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
              [(sig,3309); (sk,4032); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,3309))
              [(sk,4032); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_join11) /\\
                read RSP s = rsp0 /\\ read R15 s = word i /\\ read RCX s = word (128 * i) /\\
                read R8 s = word_add sig (word (51 + 640 * i)) /\\
                read RBX s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 1760) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 1760),64)) s = rhop /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * k)))) s =
                                 cphat k) /\\
                (!k. k < 4032 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if ok then (if i + 1 < 5 then word (pc + mldsa65_signature_internal_join11)
                             else word (pc + @NEXT@))
                 else word (pc + mldsa65_signature_internal_join35)) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (~ok ==> read R15 s = word 0) /\\
                (ok ==> read R15 s = word (i + 1) /\\ read RCX s = word (128 * (i + 1)) /\\
                        read R8 s = word_add sig (word (51 + 640 * (i + 1))) /\\
                        (!j. j < 640 ==> read (memory :> bytes8 (word_add sig (word (48 + 640 * i + j)))) s =
                                         mld_polyz_pack_19 (@ZI@) j)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok sig sk rsp0 i mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,3309; sk,4032; word_sub rsp0 (word 1471),14047;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,3309; word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                       memory :> bytes(word_add rsp0 (word 24),8);
                       memory :> bytes(word_add rsp0 (word 160),8);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 192),66);
                       memory :> bytes(word_add rsp0 (word 272),208);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word 1824),1024);
                       memory :> bytes(word_add rsp0 (word 4672),680);
                       memory :> bytes(word_add sig (word (48 + 640 * i)),640)])");;

let SI65_ZIT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_join11", SI65_ZNEXT);
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let Z65_TEMPLATE =
 `\(ok:bool) (sig:int64) (sk:int64) (rsp0:int64) (i:num) (mf:int64) (mc:int64) (pc:num).
   if ok then (if i + 1 < 5 then f_ev_mid sig sk rsp0 i mf mc pc else f_ev_last sig sk rsp0 i mf mc pc)
   else f_ev_f sig sk rsp0 i mf mc pc :(uarch_event)list`;;

let Z65_ALLOWED = [`ok:bool`; `sig:int64`; `sk:int64`; `rsp0:int64`; `i:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let Z65_CALL_TAC = SI_GCALL_TAC SI65_ZIT_EXEC Z65_ALLOWED SI_XMM_PRE_TAC;;
let Z65_FCALL_TAC = SI_GFCALL_TAC SI65_ZIT_EXEC Z65_ALLOWED SI_XMM_PRE_TAC;;

let Z65_SLICE_TAC off n st =
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `4032`; off; n; st] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 5` THEN ARITH_TAC; DISCH_TAC];;

let Z65_RCONST_TAC = SI_RCONST_TAC "mldsa65_signature_internal"
  ["mldsa65_signature_internal_const1"; "mldsa65_signature_internal_const2"] ["YMM6"; "YMM7"];;

let Z65_S1I = mk_comb(mk_comb(`mld_poly_of`,SI65_S1H),`i:num`);;
let Z65_PW = list_mk_comb(`mld_poly_pointwise_montgomery`,[Z65_S1I; `cphat:num->int32`]);;
let Z65_CS1 = mk_comb(`mld_poly_invntt_tomont`,Z65_PW);;
let Z65_YI = mk_comb(mk_comb(`mld_poly_of`,SI65_YK),`i:num`);;
let Z65_M = `rhop + 2 EXP 512 * val(word(kappa + i):int16)`;;
let Z65_S = mk_comb(`mld_keccak_absorb_once 136 0x1F 66`,Z65_M);;

let Z65_TEST = SI_TEST_RULE 5;;

(*** steps 1 to 40: z_i and its norm check ***)

let Z65_PART1_TAC =
  X86_STEPS_TAC SI65_ZIT_EXEC (1--6) THEN
  Z65_SLICE_TAC `128 + 128 * i` `128` `s6:x86state` THEN
  Z65_CALL_TAC "H_ETA" [`word_add sk (word (128 + 128 * i)):int64`; `rsp0:int64`; `pc:num`;
                        `\j. (skb:num->byte)((128 + 128 * i) + j)`] 7 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_4` THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (8--10) THEN
  Z65_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. (skb:num->byte)(128 + j))) i`] 11 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (12--13) THEN
  Z65_CALL_TAC "H_PWM" [`rsp0:int64`; `pc:num`; Z65_S1I; `cphat:num->int32`] 14 THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (15--16) THEN
  Z65_FCALL_TAC "H_INV" [`read RDI s`; Z65_PW] 17 THEN
  Z65_CALL_TAC "H_G1A" [`rsp0:int64`; `word_add rsp0 (word 1760):int64`; `rhop:num`;
                        `kappa:num`; `i:num`; `pc:num`] 18 THEN
  Z65_CALL_TAC "H_SQZ" [Z65_S; `rsp0:int64`; `pc:num`] 19 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_stream]) THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (20--22) THEN
  Z65_CALL_TAC "H_UZ" [`word_add rsp0 (word 4672):int64`; `rsp0:int64`; `pc:num`;
                       mk_comb(`mld_shake256_stream 66`,Z65_M)] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_poly_uniform_gamma1_19]) THEN
  SIGN_GAMMA_POLY_OF_TAC `mld_poly_uniform_gamma1_19` THEN
  Z65_CALL_TAC "H_ZER" [`rsp0:int64`; `pc:num`] 24 THEN SI_RIP_NORM_TAC THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (25--28) THEN
  Z65_CALL_TAC "H_ADD" [`rsp0:int64`; `pc:num`; Z65_YI; Z65_CS1] 29 THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (30--30) THEN Z65_RCONST_TAC 30 0x2085 THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (31--33) THEN
  Z65_CALL_TAC "H_RED" [`rsp0:int64`; `pc:num`; list_mk_comb(`mld_poly_add`,[Z65_CS1; Z65_YI])] 34 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (35--36) THEN
  Z65_CALL_TAC "H_CHK" [`rsp0:int64`; `pc:num`; Z65_ZI] 37;;

(*** the packing of z_i and the back edge: steps 41 to 53 ***)

let Z65_PART2_TAC =
  SI_PASS_TAC `ok:bool` THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (41--44) THEN
  Z65_CALL_TAC "H_ZP" [`rsp0:int64`; `word_add sig (word (48 + 640 * i)):int64`;
                       `pc:num`; Z65_ZI] 45 THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (46--53) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP Z65_TEST (ASSUME `i < 5`)]) THEN
  ASM_CASES_TAC `i + 1 < 5` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(SI_WORD_ADD_TAC THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[GSYM ADD_ASSOC]) THEN NO_TAC) THEN
  SI_END_TAC 1471;;

let Z65_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI65_ETA44,"H_ETA"; SI65_PWM45,"H_PWM"; SI65_G1A_Z,"H_G1A";
      MP (SPEC_ALL SI65_SQZ_Z) mcs,"H_SQZ"; SI65_UZ_Z,"H_UZ";
      MP (SPEC_ALL SI65_ZER_Z) ms,"H_ZER"; SI65_ADD47,"H_ADD"; SI65_RED48,"H_RED";
      SI65_CHK49,"H_CHK"; SI65_ZP50,"H_ZP";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"]) THEN
  CONCRETIZE_F_EVENTS_TAC Z65_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `sig:int64`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `rhop:num`; `kappa:num`; `i:num`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst SI65_ZIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0; 0x220; 0x720; 0x2d00] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `i < 65536` ASSUME_TAC THENL [UNDISCH_TAC `i < 5` THEN ARITH_TAC; ALL_TAC];;

let Z65_FAIL_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME `~ok`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI_END_TAC 1471;;

let SI65_ZIT = prove
 (SI65_ZIT_STMT,
  Z65_SETUP_TAC THEN FULL_INIT_TAC THEN Z65_PART1_TAC THEN
  X86_STEPS_TAC SI65_ZIT_EXEC (38--40) THEN SI_DECIDE_TAC `ok:bool` THEN
  ASM_CASES_TAC `ok:bool` THENL [Z65_PART2_TAC; Z65_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check (ZPRE), from after the NTT of the challenge, where the code    *)
(* sets up i = 0, as gcc's SIGN65_ZPRE: z_0 .. z_(m-1) packed into the       *)
(* signature after c~.                                                       *)
(* ------------------------------------------------------------------------- *)

let ZP65_ZV = list_mk_comb(`mld_sign_z`, [SI65_S1H; `cphat:num->int32`; SI65_YK]);;
let ZP65_ZI = mk_comb(ZP65_ZV,`i:num`);;
let ZP65_PACK = mk_comb(`mld_polyvec_pack 640 mld_polyz_pack_19`,
                        mk_comb(`mld_polyvec`,ZP65_ZV));;

let SI65_ZPRE_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@ZI@",string_of_term ZP65_ZI; "@PACK@",string_of_term ZP65_PACK;
   "@NEXT@",string_of_int SI65_ZNEXT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e m sig sk skb rsp0 rhop kappa cphat pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ m <= 5 /\\
          (!i. i < m ==> mld_poly_chknorm (@ZI@) (word 524092) = word 0) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
              [(sig,3309); (sk,4032); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,3309))
              [(sk,4032); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\
                read RBX s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 168))) s = word_add sig (word 51) /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 1760) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 1760),64)) s = rhop /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * k)))) s =
                                 cphat k) /\\
                (!k. k < 4032 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if m < 5 then word (pc + mldsa65_signature_internal_join11)
                 else word (pc + @NEXT@)) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read R15 s = word m /\\ read RCX s = word (128 * m) /\\
                read R8 s = word_add sig (word (51 + 640 * m)) /\\
                (!t. t < 640 * m ==> read (memory :> bytes8 (word_add sig (word (48 + t)))) s =
                                     @PACK@ t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sig sk rsp0 mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,3309; sk,4032; word_sub rsp0 (word 1471),14047;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,3309; word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                       memory :> bytes(word_add rsp0 (word 24),8);
                       memory :> bytes(word_add rsp0 (word 160),8);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 192),66);
                       memory :> bytes(word_add rsp0 (word 272),208);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word 1824),1024);
                       memory :> bytes(word_add rsp0 (word 4672),680);
                       memory :> bytes(word_add sig (word 48),3200)])");;

let SI65_ZPRE_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_after_mldsa_poly_ntt_2", SI65_ZNEXT);
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let ZP65_INV = parse_term(subst_tokens ["@PACK@",string_of_term ZP65_PACK]
 "\\i s. read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
       (read DF s <=> false) /\\
       read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
       read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
       read (memory :> bytes(ea,el)) s = ev /\\
       read R15 s = word i /\\ read RCX s = word (128 * i) /\\
       read R8 s = word_add sig (word (51 + 640 * i)) /\\
       read (memory :> bytes64 (word_add rsp0 (word 168))) s = word_add sig (word 51) /\\
       read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
       read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 1760) /\\
       read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
       read (memory :> bytes (word_add rsp0 (word 1760),64)) s = rhop /\\
       (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * k)))) s =
                        cphat k) /\\
       (!k. k < 4032 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
       (!t. t < 640 * i ==> read (memory :> bytes8 (word_add sig (word (48 + t)))) s =
                            @PACK@ t)");;

let ZP65_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 5` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!i. i < m ==> P i`) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FULL_INIT_TAC THEN
  REMOVE_THEN "H_ZIT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI65_ZPRE_EXEC,0x0,VM_MC,th)
      [`e:(uarch_event)list`; `T`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
       `rhop:num`; `kappa:num`; `i:num`; `cphat:num->int32`; `pc:num`] 1 THENL
     [REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC [`sig:int64`; `sk:int64`; `rsp0:int64`; `i:num`; `mf:int64`; `mc:int64`; `pc:num`];
      LABEL_TAC "H_ZIT" th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI_LOOP_PC (CONJ (ASSUME `i < m`) (ASSUME `m <= 5`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let ZP65_START_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC SI65_ZPRE_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0];;

let SI65_ZPRE = prove
 (SI65_ZPRE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SI_ASSUME_CALLEE_TAILED_TAC (MP (SPEC_ALL SI65_ZIT) th) "H_ZIT") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (sk:int64) (rsp0:int64) (mf:int64) (mc:int64) (pc:num).
     APPEND (f_ev_back m sig sk rsp0 mf mc pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig sk rsp0 mf mc pc i))
              (f_ev_front sig sk rsp0 mf mc pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sig:int64`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `rhop:num`; `kappa:num`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_ZPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_join11`
     (mk_comb(mk_comb(mk_comb(`COND:bool->num->num->num`,`m < 5`),
        `pc + mldsa65_signature_internal_join11`),
        mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral SI65_ZNEXT)))
     ZP65_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      ZP65_START_TAC THEN SI_DISCHARGE_TAC 1471;
      ZP65_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN ZP65_START_TAC THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI_DISCHARGE_TAC 1471]);;

(* ------------------------------------------------------------------------- *)
(* Column j of the product of the matrix with y (YCOL j, j = 0 .. 4), from   *)
(* join4 to join3: y_j sampled (absorbing rho'' || kappa + j, squeezing,     *)
(* unpacking at rsp0 + 0x220, zeroing) and transformed, then for each row r  *)
(* the entry A_rj sampled by mldsa_poly_uniform from rho || j || r at rsp0 + *)
(* 0x1240 and multiplied by it: for j = 0 into row r of w at rsp0 + 0x1500 + *)
(* 1024 r, for j > 0 into the scratch polynomial at rsp0 + 0xe20 and added   *)
(* to row r. Row r is then mld_lazy_acc rho r YHAT j, YHAT being y in the    *)
(* NTT domain. The code zeroes XMM4 (which the sampling of the next y_j      *)
(* needs) and loads the constants of the reduction that follows the loop     *)
(* into XMM5 and XMM6 before the last row. The lemma is made for each j,     *)
(* with j a numeral, from one generator.                                     *)
(* ------------------------------------------------------------------------- *)

let SI65_YHAT = `mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa)`;;

let yc65_row r n =
  Printf.sprintf
   "(!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * k)))) s =
                     mld_lazy_acc rho %d (%s) %d k)"
   (5376 + 1024 * r) r (string_of_term SI65_YHAT) n;;

let yc65_rows n = String.concat " /\\\n " (map (fun r -> yc65_row r n) (0--5));;

let YC65_STMT j = parse_term(subst_tokens
  ["@MC@",image_mc;
   "@PRE@",(if j = 0 then "" else yc65_rows (j - 1) ^ " /\\");
   "@POST@",yc65_rows j;
   "@J@",string_of_int j]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 rho rhop kappa pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ mld_matrix_terminates 6 5 rho /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_join4) /\\
                read RSP s = rsp0 /\\ read R12 s = word @J@ /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 1760) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 1760),64)) s = rhop /\\
                read (memory :> bytes (word_add rsp0 (word 4672),32)) s = rho /\\
                @PRE@
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa65_signature_internal_join3) /\\
                read RSP s = rsp0 /\\ read R12 s = word @J@ /\\
                read RBX s = word 0x0380200100000000 /\\
                read XMM4 s = word 0 /\\
                read XMM5 s = word 0x00400000004000000040000000400000 /\\
                read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 1760) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 1760),64)) s = rhop /\\
                read (memory :> bytes (word_add rsp0 (word 4672),32)) s = rho /\\
                @POST@ /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rho mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),14047;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256]
                    [word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 24),4);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word 1824),208);
                       memory :> bytes(word_add rsp0 (word 2848),66);
                       memory :> bytes(word_add rsp0 (word 3616),1024);
                       memory :> bytes(word_add rsp0 (word 4704),2);
                       memory :> bytes(word_add rsp0 (word 5376),6144);
                       memory :> bytes(word_add rsp0 (word 11520),680)])");;

let SI65_YCOL_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_join4", layout "mldsa65_signature_internal_join10");
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let YC65_ALLOWED = [`rsp0:int64`; `rho:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let YC65_CALL_TAC = SI_GCALL_TAC SI65_YCOL_EXEC YC65_ALLOWED SI_XMM_PRE_TAC;;
let YC65_FCALL_TAC = SI_GFCALL_TAC SI65_YCOL_EXEC YC65_ALLOWED SI_XMM_PRE_TAC;;

let YC65_RCONST_TAC = SI_RCONST_TAC "mldsa65_signature_internal"
  ["mldsa65_signature_internal_const1"; "mldsa65_signature_internal_const2"] ["YMM5"; "YMM6"];;

let YC65_Y = `mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa`;;

(*** y_j and its NTT: steps 1 to 17 ***)

let YC65_HEAD_TAC j =
  let jt = mk_small_numeral j in
  let m = subst [jt,`j:num`] `rhop + 2 EXP 512 * val(word(kappa + j):int16)` in
  YC65_CALL_TAC "H_G1A" [`rsp0:int64`; `word_add rsp0 (word 1760):int64`; `rhop:num`;
                         `kappa:num`; jt; `pc:num`] 1 THEN
  YC65_CALL_TAC "H_SQZ" [mk_comb(`mld_keccak_absorb_once 136 0x1F 66`,m); `rsp0:int64`; `pc:num`] 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_stream]) THEN
  X86_STEPS_TAC SI65_YCOL_EXEC (3--5) THEN
  YC65_CALL_TAC "H_UZ" [`word_add rsp0 (word 11520):int64`; `rsp0:int64`; `pc:num`;
                        mk_comb(`mld_shake256_stream 66`,m)] 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_poly_uniform_gamma1_19]) THEN
  SIGN_GAMMA_POLY_OF_TAC `mld_poly_uniform_gamma1_19` THEN
  YC65_CALL_TAC "H_ZER" [`rsp0:int64`; `pc:num`] 7 THEN SI_RIP_NORM_TAC THEN
  X86_STEPS_TAC SI65_YCOL_EXEC (8--10) THEN
  YC65_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,YC65_Y),jt)] 11 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI65_YCOL_EXEC (12--12) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R12 s = x`) (concl th)
                           then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
  X86_STEPS_TAC SI65_YCOL_EXEC (13--17);;

(*** row r of a column: the seed rho || j || r, the sampling of the entry   ***)
(*** (the CALL at step n), its product with y_j and, for j > 0, the sum     ***)

let YC65_SEED_TAC j r st =
  if j = 0 then
    MP_TAC(SPECL [`word_add rsp0 (word 4672):int64`; `rho:num`; mk_small_numeral r; `0`; st]
                 SI_SEED16) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (x:int64) (word 4672)) (word 32) =
                           word_add x (word 4704)`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC
  else
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes8 a) s = x`) (concl th)
      then CONV_RULE(RAND_CONV(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV)) th
      else th) THEN
    MP_TAC(SPECL [`word_add rsp0 (word 4672):int64`; `rho:num`; mk_small_numeral r;
                  mk_small_numeral j; st] LAZY_SEED) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (x:int64) (word 4672)) (word 32) =
                           word_add x (word 4704)`;
                WORD_RULE `word_add (word_add (x:int64) (word 4672)) (word 33) =
                           word_add x (word 4705)`] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let YC65_PU_TAC j r n =
  let jt = mk_small_numeral j and rt = mk_small_numeral r in
  let sd = list_mk_comb(`mld_matrix_seed`,[`rho:num`; rt; jt]) in
  let st = mk_var("s"^string_of_int (n - 1),`:x86state`) in
  YC65_SEED_TAC j r st THEN
  MLD_LAZY_TERM_TAC (mk_comb(`mld_rej_uniform_terminates`,mk_comb(`mld_shake128_stream 34`,sd))) THEN
  YC65_FCALL_TAC "H_PU" [`read RDI s`; `read RSI s`; sd] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]);;

(* the zeroing of XMM4 at step n, with its old value ghosted first *)
let YC65_PXOR_TAC n =
  YMM_GHOST_TAC (mk_var("s"^string_of_int (n - 1),`:x86state`))
    [("YMM4","ymm4_"^string_of_int (n - 1))] THEN
  X86_STEPS_TAC SI65_YCOL_EXEC (n--n);;

let YC65_TAC j =
  let jt = mk_small_numeral j in
  let yh = mk_comb(mk_comb(`mld_poly_of`,SI65_YHAT),jt) in
  let entry r = list_mk_comb(`mld_matrix_entry`,[`rho:num`; mk_small_numeral r; jt]) in
  let pwm r = list_mk_comb(`mld_poly_pointwise_montgomery`,[entry r; yh]) in
  let acc r n = list_mk_comb(`mld_lazy_acc rho`,[mk_small_numeral r; SI65_YHAT; mk_small_numeral n]) in
  let acc_eq r =
    if j = 0 then GSYM(CONJUNCT1 mld_lazy_acc)
    else SYM(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
              (SPECL [`rho:num`; mk_small_numeral r; SI65_YHAT; mk_small_numeral (j - 1)]
                     MLD_LAZY_ACC_ADD1)) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     ([SI65_G1A_Y,"H_G1A"; MP (SPEC_ALL SI65_SQZ_Y) mcs,"H_SQZ"; SI65_UZ_Y,"H_UZ";
       MP (SPEC_ALL SI65_ZER_Y) ms,"H_ZER";
       MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
       MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th,
       "H_PU"] @
      (if j = 0 then [SI65_PWM14,"H_PWM0"; SI65_PWM15,"H_PWM1"; SI65_PWM16,"H_PWM2";
                      SI65_PWM17,"H_PWM3"; SI65_PWM18,"H_PWM4"; SI65_PWM19,"H_PWM5"]
       else [SI65_PWM2,"H_PWM0"; SI65_PWM4,"H_PWM1"; SI65_PWM6,"H_PWM2"; SI65_PWM8,"H_PWM3";
             SI65_PWM10,"H_PWM4"; SI65_PWM12,"H_PWM5";
             SI65_ADD3,"H_ADD0"; SI65_ADD5,"H_ADD1"; SI65_ADD7,"H_ADD2"; SI65_ADD9,"H_ADD3";
             SI65_ADD11,"H_ADD4"; SI65_ADD13,"H_ADD5"]))) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rho:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_col rsp0 rho mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rho:num`; `rhop:num`;
                       `kappa:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mld_matrix_terminates]) THEN
  SI_ALIGNED16_TAC [0; 0x220; 0xe20; 0x1500; 0x1900; 0x1d00; 0x2100; 0x2500; 0x2900] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  FULL_INIT_TAC THEN YC65_HEAD_TAC j THEN
  (if j = 0 then
    MAP_EVERY (fun r ->
      let n = if r = 0 then 18 else 19 + 7 * r in
      X86_STEPS_TAC SI65_YCOL_EXEC (n--(n+3)) THEN YC65_PU_TAC j r (n+4) THEN
      (if r = 0 then
         X86_STEPS_TAC SI65_YCOL_EXEC ((n+5)--(n+6)) THEN
         YC65_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+7)
       else if r = 5 then
         X86_STEPS_TAC SI65_YCOL_EXEC ((n+5)--(n+5)) THEN YC65_PXOR_TAC (n+6) THEN
         YC65_RCONST_TAC (n+6) 0xf3c THEN
         X86_STEPS_TAC SI65_YCOL_EXEC ((n+7)--(n+9)) THEN
         YC65_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+10)
       else
         X86_STEPS_TAC SI65_YCOL_EXEC ((n+5)--(n+5)) THEN
         YC65_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+6)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[acc_eq r])) (0--5) THEN
    X86_STEPS_TAC SI65_YCOL_EXEC (65--65)
   else
    MAP_EVERY (fun r ->
      let n = 18 + 12 * r in
      X86_STEPS_TAC SI65_YCOL_EXEC (n--(n+4)) THEN YC65_PU_TAC j r (n+5) THEN
      X86_STEPS_TAC SI65_YCOL_EXEC ((n+6)--(n+7)) THEN
      YC65_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+8) THEN
      (if r = 5 then
         X86_STEPS_TAC SI65_YCOL_EXEC ((n+9)--(n+9)) THEN YC65_PXOR_TAC (n+10) THEN
         YC65_RCONST_TAC (n+10) 0xbb2 THEN
         X86_STEPS_TAC SI65_YCOL_EXEC ((n+11)--(n+13))
       else X86_STEPS_TAC SI65_YCOL_EXEC ((n+9)--(n+10))) THEN
      YC65_CALL_TAC ("H_ADD"^string_of_int r) [`rsp0:int64`; `pc:num`; pwm r; acc r (j - 1)]
        (if r = 5 then n+14 else n+11) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[acc_eq r])) (0--5) THEN
    X86_STEPS_TAC SI65_YCOL_EXEC (93--93)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(SI_XMM_PRE_TAC THEN NO_TAC) THEN
  SI_END_TAC 1471;;

let SI65_YCOL0 = prove(YC65_STMT 0, YC65_TAC 0);;
let SI65_YCOL1 = prove(YC65_STMT 1, YC65_TAC 1);;
let SI65_YCOL2 = prove(YC65_STMT 2, YC65_TAC 2);;
let SI65_YCOL3 = prove(YC65_STMT 3, YC65_TAC 3);;
let SI65_YCOL4 = prove(YC65_STMT 4, YC65_TAC 4);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt (CLEAN), from join36 with RBX whose low byte is *)
(* 1 on success and 0 otherwise: the memsets of z (0x720), the challenge     *)
(* (0x2d00), w (0x1500), the packed w1 (0xb20) and the polynomial of y       *)
(* (0x220), the zeroing of XMM4, of the structure of y (0x80) and of c~      *)
(* (0x1e0), and the test of BL: to join37 on success, else to the update of  *)
(* the count of the attempts at +0x2e61, with XMM4 = 0 for the next one.     *)
(* ------------------------------------------------------------------------- *)

let SI65_NX = layout "mldsa65_signature_internal" + 0x2e61;;

let SI65_CLEAN_STMT = parse_term(subst_tokens ["@MC@",image_mc; "@NX@",string_of_int SI65_NX]
 "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ok rsp0 rb0 pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 (rsp0:int64) /\\
          (word_zx (rb0:int64) = (word 0:byte) <=> ~ok) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 8),12584))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + mldsa65_signature_internal_join36) /\\
                    read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read RIP s = (if ok then word (pc + mldsa65_signature_internal_join37)
                                  else word (pc + @NX@)) /\\
                    read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                    read XMM4 s = word 0 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (exists e2. read events s = APPEND e2 e /\\
                       e2 = f_events ok rsp0 mf pc /\\
                       memaccess_inbounds e2
                        [word_sub rsp0 (word 8),12584; word(pc + got_memset),8; ea,el]
                        [word_sub rsp0 (word 8),12584]))
               (MAYCHANGE [RSP; R14] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 8),8);
                           memory :> bytes(word_add rsp0 (word 0x80),16);
                           memory :> bytes(word_add rsp0 (word 0x1e0),48);
                           memory :> bytes(word_add rsp0 (word 0x220),1024);
                           memory :> bytes(word_add rsp0 (word 0x720),1024);
                           memory :> bytes(word_add rsp0 (word 0xb20),768);
                           memory :> bytes(word_add rsp0 (word 0x1500),6144);
                           memory :> bytes(word_add rsp0 (word 0x2d00),1024)])");;

let SI65_CLEAN_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_join36", SI65_NX);
   layout_range "plt_memset"];;

let SI65_CLEAN = prove
 (SI65_CLEAN_STMT,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (rsp0:int64) (mf:int64) (pc:num).
      if ok then f_ev_ok rsp0 mf pc else f_ev_nok rsp0 mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `rsp0:int64`; `rb0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_CLEAN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x80; 0x1e0; 0x1f0; 0x200] THEN
  FULL_INIT_TAC THEN
  SI_RUN_TO_TAC SI65_CLEAN_EXEC "H_MEMSET"
    (ref [`ok:bool`; `rsp0:int64`; `mf:int64`; `pc:num`])
    (layout "mldsa65_signature_internal" + 0x2e25) 1 THEN
  YMM_GHOST_TAC `s35:x86state` ["YMM4","ymm4_35"] THEN
  SI_RUN_TO_TAC SI65_CLEAN_EXEC "H_MEMSET"
    (ref [`ok:bool`; `rsp0:int64`; `mf:int64`; `pc:num`]) (-1) 36) THEN
  (SUBGOAL_THEN `word (val (rb0:int64) MOD 256):byte = word_zx rb0`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; VAL_EQ_0])) THENL
   [REWRITE_TAC[word_zx; GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_iff(concl th) && free_in `ok:bool` (concl th)
                        then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  ASM_CASES_TAC `ok:bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if concl th = `ok:bool` || concl th = `~ok`
     then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th') else NO_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REPEAT CONJ_TAC THEN TRY(SI_XMM_PRE_TAC THEN NO_TAC) THEN
  SI_DISCHARGE_TAC 8));;

(* ------------------------------------------------------------------------- *)
(* After the product with the matrix (HPOST), from join10 to after the NTT  *)
(* of the challenge: the seed buffer zeroed (from XMM4), the rows of w      *)
(* reduced (XMM5 and XMM6 as YCOL 4 left them), transformed back and made   *)
(* nonnegative, which MLD_LAZY_SIGN_W turns into w = A y of the model; w    *)
(* decomposed in place into w0 row by row, w1 packed at rsp0 + 0xb20 after  *)
(* each row (the mask in XMM6), c~ = H(mu || w1) at rsp0 + 0x1e0 with       *)
(* mld_H65 (stack arguments NULL and 0, from XMM5 zeroed), the challenge at *)
(* rsp0 + 0x2d00 and its NTT.                                               *)
(* ------------------------------------------------------------------------- *)

let SI65_A = `mld_polyvec_matrix_expand 5 rho`;;
let SI65_W = list_mk_comb(`mld_sign_w 5`,[SI65_A; YC65_Y]);;
let SI65_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128`,SI65_W);;
let SI65_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,[SI65_W1; `768`]));;
let SI65_CT = mk_comb(`mld_sign_ctilde 6 128 mu`,SI65_W1);;

let SI65_HPOST_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@PRE@",yc65_rows 4; "@W@",string_of_term SI65_W;
   "@W1@",string_of_term SI65_W1; "@CT@",string_of_term SI65_CT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 rho rhop kappa mu C pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ mld_matrix_terminates 6 5 rho /\\
          num_of_bytelist(list_of_seq (@CT@) 48) = C /\\
          mld_poly_challenge_terminates 49 48 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_join10) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                read XMM4 s = word 0 /\\
                read XMM5 s = word 0x00400000004000000040000000400000 /\\
                read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word 1696),64)) s = mu /\\
                @PRE@ /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa65_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (!i. i < 1536 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 (@W@) i) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (2848 + j)))) s =
                                 (@W1@) j) /\\
                read (memory :> bytes (word_add rsp0 (word 480),48)) s = C /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * k)))) s =
                                 mld_poly_ntt (mld_poly_challenge 49 48 C) k) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 C mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),14047;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa65_poly_challenge_consts),48;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 480),48);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word 2848),768);
                       memory :> bytes(word_add rsp0 (word 4672),64);
                       memory :> bytes(word_add rsp0 (word 5376),6144);
                       memory :> bytes(word_add rsp0 (word 11520),1024)])");;

let SI65_HPOST_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_join10", layout "mldsa65_signature_internal_after_mldsa_poly_ntt_2")];;

let HP65_ALLOWED = [`rsp0:int64`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let HP65_CALL_TAC = SI_GCALL_TAC SI65_HPOST_EXEC HP65_ALLOWED SI_XMM_PRE_TAC;;
let HP65_FCALL_TAC = SI_GFCALL_TAC SI65_HPOST_EXEC HP65_ALLOWED SI_XMM_PRE_TAC;;

let HP65_V = `mld_polyvec (\i. mld_lazy_acc rho i
                (mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa)) 4)`;;
let HP65_RV = mk_comb(`mld_polyvec_map mld_poly_reduce`,HP65_V);;
let HP65_IV = mk_comb(`mld_polyvec_map mld_poly_invntt_tomont`,HP65_RV);;
let HP65_CV = mk_comb(`mld_polyvec_map mld_poly_caddq`,HP65_IV);;
let HP65_ROW v r = mk_comb(mk_comb(`mld_poly_of`,v),mk_small_numeral r);;

(* row r of the lazy sums as row r of the vector HP65_V *)
let HP65_V_TAC r =
  let off = 5376 + 1024 * r in
  FIRST_X_ASSUM(fun th ->
    let pat = subst [mk_small_numeral off,`d:num`; mk_small_numeral r,`r:num`]
     `!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (d + 4 * k)))) s =
                      mld_lazy_acc rho r YH 4 k` in
    if can (term_match [] pat) (concl th) then
      ASSUME_TAC(MATCH_MP (BETA_RULE(ISPECL
        [`\i. mld_lazy_acc rho i (mld_polyvec_map mld_poly_ntt
                (mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa)) 4`;
         mk_small_numeral r] SI_POLYVEC_POLY_OF)) th)
    else NO_TAC);;

let HP65_LAZY_W_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
   `!i. i < 1536
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * i)))) s =
            mld_polyvec_map mld_poly_caddq x i`) (concl th))) THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
   (SPECL [`6`; `5`; `rho:num`; YC65_Y] MLD_LAZY_SIGN_W)) THEN
  REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND; ASSUME `mld_matrix_terminates 6 5 rho`] THEN
  DISCH_THEN(fun th -> SIMP_TAC[th]) THEN DISCH_TAC;;

let HP65_YVEC = prove
 (mk_eq(list_mk_comb(`mld_polyvec_matrix_yvec_lazy 5 rho`,[YC65_Y]),HP65_IV),
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy] THEN CONV_TAC NUM_REDUCE_CONV);;

let HP65_ROWS_PAT32 =
 `!r. r < 6 ==> !k. k < 256
      ==> read (memory :> bytes32 (word_add B (word ((off + 1024 * r) + 4 * k)))) s =
          mld_poly_of V r k`;;

(*** the rows of w: steps 1 to 61 ***)

let HP65_PART1_TAC =
  X86_STEPS_TAC SI65_HPOST_EXEC (1--6) THEN
  MAP_EVERY HP65_V_TAC (0--5) THEN
  MAP_EVERY (fun r ->
    (if r > 0 then X86_STEPS_TAC SI65_HPOST_EXEC ((5 + 3 * r)--(6 + 3 * r)) else ALL_TAC) THEN
    HP65_CALL_TAC ("H_RED"^string_of_int r) [`rsp0:int64`; `pc:num`; HP65_ROW HP65_V r]
      (7 + 3 * r) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_reduce`) (0--5) THEN
  MAP_EVERY (fun r ->
    X86_STEPS_TAC SI65_HPOST_EXEC ((23 + 3 * r)--(24 + 3 * r)) THEN
    HP65_FCALL_TAC "H_INV" [`read RDI s`; HP65_ROW HP65_RV r] (25 + 3 * r) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_invntt_tomont`) (0--5) THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (41--42) THEN
  HP65_CALL_TAC "H_CQ0" [`rsp0:int64`; `pc:num`; HP65_ROW HP65_IV 0] 43 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq` THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (44--45) THEN
  SI_RCONST_TAC "mldsa65_signature_internal" ["mldsa65_signature_internal_const4"] ["YMM6"]
    45 0x1442 THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (46--47) THEN
  HP65_CALL_TAC "H_CQ1" [`rsp0:int64`; `pc:num`; HP65_ROW HP65_IV 1] 48 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq` THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (49--49) THEN
  YMM_GHOST_TAC `s49:x86state` ["YMM5","ymm5_49"] THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (50--51) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_REFL]) THEN
  HP65_CALL_TAC "H_CQ2" [`rsp0:int64`; `pc:num`; HP65_ROW HP65_IV 2] 52 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq` THEN
  MAP_EVERY (fun r ->
    X86_STEPS_TAC SI65_HPOST_EXEC ((44 + 3 * r)--(45 + 3 * r)) THEN
    HP65_CALL_TAC ("H_CQ"^string_of_int r) [`rsp0:int64`; `pc:num`; HP65_ROW HP65_IV r]
      (46 + 3 * r) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_caddq`) [3;4;5];;

(*** w as w = A y, its decomposition and the packing of w1: steps 62 to 85 ***)

let HP65_PART2_TAC =
  SI_ROWS_TAC `rsp0:int64` 5376 `s61:x86state` (subst [HP65_CV,`V:num->int32`] HP65_ROWS_PAT32) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
           (MATCH_MP SI_JOIN_VECN32 (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] th)))
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM HP65_YVEC]) THEN
  HP65_LAZY_W_TAC THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (62--63) THEN
  MAP_EVERY (fun r ->
    MP_TAC(SPECL [`rsp0:int64`; `5376`; SI65_W; `s63:x86state`; `6`;
                  mk_small_numeral r] SI_SLICE_VECN32) THEN
    ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC) (0--5) THEN
  MAP_EVERY (fun r ->
    let n = 62 + 4 * r in
    (if r = 0 then ALL_TAC else X86_STEPS_TAC SI65_HPOST_EXEC (n--(n+1))) THEN
    HP65_CALL_TAC ("H_DEC"^string_of_int r) [`rsp0:int64`; `pc:num`; HP65_ROW SI65_W r] (n+2) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_decompose_lo_32` THEN
    HP65_CALL_TAC ("H_W1P"^string_of_int r)
      [`rsp0:int64`; `pc:num`; mk_comb(`mld_poly_decompose_hi_32`,HP65_ROW SI65_W r)] (n+3))
   (0--5);;

let HP65_W1_COEFF = prove
 (mk_forall(`r:num`,mk_forall(`j:num`,mk_imp(`j < 128`,
   mk_eq(mk_comb(SI65_W1,`128 * r + j`),
         list_mk_comb(`mld_polyw1_pack_32`,
           [mk_comb(`mld_poly_decompose_hi_32`,mk_comb(mk_comb(`mld_poly_of`,SI65_W),`r:num`));
            `j:num`]))))),
  REWRITE_TAC[mld_sign_w1] THEN SIMP_TAC[MLD_POLYVEC_PACK_COEFF; o_THM]);;

(*** w0 and w1 as vectors, c~, the challenge and its NTT: steps 86 to 105 ***)

let HP65_PART3_TAC =
  SI_ROWS_TAC `rsp0:int64` 5376 `s85:x86state`
    (subst [mk_comb(`mld_polyvec_map mld_poly_decompose_lo_32`,SI65_W),`V:num->int32`]
           HP65_ROWS_PAT32) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
           (MATCH_MP SI_JOIN_VECN32 (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] th)))
    else NO_TAC) THEN
  SUBGOAL_THEN (subst [SI65_W1,`P:num->byte`]
    `!r j. r < 6 /\ j < 128
           ==> read (memory :> bytes8 (word_add rsp0 (word ((2848 + 128 * r) + j)))) s85 =
               (P:num->byte) (128 * r + j)`) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HP65_W1_COEFF] THEN
    UNDISCH_TAC `r < 6` THEN SPEC_TAC(`r:num`,`r:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (MATCH_MP SI_JOIN_VECN8 th))
    else NO_TAC) THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (86--94) THEN
  VERIF_NULL_TAC [`word_add rsp0 (word 480):int64`,`48`; `word_sub rsp0 (word 600):int64`,`576`] THEN
  VM_SPLIT128_TAC `word_sub rsp0 (word 16):int64` `s94:x86state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SI_ZERO_LO_SPLIT]) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!t. t < 768 ==> read (memory :> bytes8
         (word_add rsp0 (word (2848 + t)))) s = f t`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX; WORD_RULE `word_add (x:int64) (word 2848) =
                                  word_add (word_sub x (word 16)) (word 2864)`]
                      (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SUBGOAL_THEN `aligned 16 (word_sub rsp0 (word 16):int64)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`rsp0:int64`] ALIGNED_WORD_WEAKEN)
                      (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (word_sub (word_sub rsp0 (word 16)) (word 8)) (word 8):int64)`
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_add (word_sub (word_sub (x:int64) (word 16)) (word 8)) (word 8) =
                           word_sub x (word 16)`] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (95--95) THEN
  HP65_FCALL_TAC "H_H65"
   [`read RDI s`; `48`; `read RDX s`; `64`; `read R8 s`; `768`;
    `word 0:int64`; `0`; `mu:num`; SI65_W1NUM; `0`] 96 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES;
    ARITH_RULE `64 + 768 = 832`; ARITH_RULE `8 * 64 = 512`;
    WORD_RULE `word_add (word_sub (x:int64) (word 16)) (word 496) = word_add x (word 480)`]) THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add rsp0 (word 480),48)) s96 = C` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; ARITH_RULE `64 + 6 * 128 = 832`; ARITH_RULE `6 * 128 = 768`] THEN
    FIRST_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add rsp0 (word 480),48)) s96 = num_of_bytelist l`) (concl th)
       then ACCEPT_TAC th else NO_TAC);
    ALL_TAC] THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (97--97) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 16)) (word 16) = x`]) THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (98--101) THEN
  HP65_FCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; `C:num`] 102 THEN
  X86_STEPS_TAC SI65_HPOST_EXEC (103--104) THEN
  HP65_FCALL_TAC "H_NTT" [`read RDI s`; `mld_poly_challenge 49 48 C`] 105 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VERIF_EMPTY_REGIONS_TAC THEN SI_END_TAC 1471;;

let SI65_HPOST = prove
 (SI65_HPOST_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI65_RED20,"H_RED0"; SI65_RED21,"H_RED1"; SI65_RED22,"H_RED2"; SI65_RED23,"H_RED3";
      SI65_RED24,"H_RED4"; SI65_RED25,"H_RED5";
      SI65_CQ26,"H_CQ0"; SI65_CQ27,"H_CQ1"; SI65_CQ28,"H_CQ2"; SI65_CQ29,"H_CQ3";
      SI65_CQ30,"H_CQ4"; SI65_CQ31,"H_CQ5";
      SI65_DEC32,"H_DEC0"; SI65_DEC34,"H_DEC1"; SI65_DEC36,"H_DEC2"; SI65_DEC38,"H_DEC3";
      SI65_DEC40,"H_DEC4"; SI65_DEC42,"H_DEC5";
      SI65_W1P33,"H_W1P0"; SI65_W1P35,"H_W1P1"; SI65_W1P37,"H_W1P2"; SI65_W1P39,"H_W1P3";
      SI65_W1P41,"H_W1P4"; SI65_W1P43,"H_W1P5";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MP (SPEC_ALL MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) mcs,"H_H65";
      MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th,
      "H_CHAL"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (C:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_hp rsp0 C mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rho:num`; `rhop:num`;
                       `kappa:num`; `mu:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_HPOST_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x220; 0x1240; 0x1250; 0x1260; 0x1270;
                    0x1500; 0x1900; 0x1d00; 0x2100; 0x2500; 0x2900] THEN
  FULL_INIT_TAC THEN HP65_PART1_TAC THEN HP65_PART2_TAC THEN HP65_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints (TAIL), from the exit of the loop over *)
(* the rows (loop51_exit1): c~ (48 bytes at rsp0 + 0x1e0) copied to sig, the *)
(* 61 bytes of the hints zeroed from XMM4 (the last two stores overlap), and *)
(* for each row k the unpacking of its w1 (W1U, the nibble mask in XMM5) and *)
(* its hints (HROW). If the hints fit, the code sets BL to 1 and goes to the *)
(* cleanup at join36 with the hints of mld_pack_hints at sig + 3248;         *)
(* otherwise to the rejection at join35. R15, the result, is set to 0       *)
(* before the hints.                                                         *)
(* ------------------------------------------------------------------------- *)

let SI_BYTES128_ZERO_SUFFIX = prove
 (`!(a:int64) k (s:x86state).
     read (memory :> bytes128 a) s = word 0 /\ k <= 16
     ==> read (memory :> bytes (word_add a (word k),16 - k)) s = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (a,16)) s = 0` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD_0;
                DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `16 = k + (16 - k)` SUBST1_TAC THENL
   [UNDISCH_TAC `k <= 16` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB2; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0] THEN
  ARITH_TAC);;

(* the unpackings of w1 of rows 0 to 5 (loops 62 to 67) with the real mask *)
let SI65_W1UM62 = SI_PROVE_W1UNPACK4 "mldsa65_signature_internal" "loop62" "loop62_exit" "RAX" "RCX" 0xb20 0x220;;
let SI65_W1UM63 = SI_PROVE_W1UNPACK4 "mldsa65_signature_internal" "loop63" "loop63_exit" "RCX" "RDX" 0xba0 0x220;;
let SI65_W1UM64 = SI_PROVE_W1UNPACK4 "mldsa65_signature_internal" "loop64" "loop64_exit" "RCX" "RDX" 0xc20 0x220;;
let SI65_W1UM65 = SI_PROVE_W1UNPACK4 "mldsa65_signature_internal" "loop65" "loop65_exit" "RCX" "RDX" 0xca0 0x220;;
let SI65_W1UM66 = SI_PROVE_W1UNPACK4 "mldsa65_signature_internal" "loop66" "loop66_exit" "RCX" "RDX" 0xd20 0x220;;
let SI65_W1UM67 = SI_PROVE_W1UNPACK4 "mldsa65_signature_internal" "loop67" "loop67_exit" "RCX" "RDX" 0xda0 0x220;;

let T65_MH = `mld_polyvec_make_hint_32 x b`;;

let T65_ZX_SUB = WORD_BLAST `!y:int256. word_zx y:int128 = word_subword y (0,128)`;;
let T65_Y4 = ASSUME `word_subword (ymm4_init:int256) (0,128):int128 = word 0`;;

let SI65_TAIL_STMT = parse_term(subst_tokens ["@MC@",image_mc]
 "exists f_events.
    forall e sig rsp0 rb0 (C:num) (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\
      nonoverlapping (sig,3309) (rsp0,12576) /\\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,3309); (rsp0,12576)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_loop51_exit1) /\\
                read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                read XMM4 s = word 0 /\\
                read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
                read (memory :> bytes64 (word_add rsp0 (word 8))) s = sig /\\
                read (memory :> bytes64 (word_add rsp0 (word 16))) s = word_add sig (word 3248) /\\
                read (memory :> bytes (word_add rsp0 (word 480),48)) s = C /\\
                (!j. j < 1536 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * j)))) s = x j) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (2848 + j)))) s = b j) /\\
                read events s = e)
           (\\s. read RIP s =
                (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55
                 then word (pc + mldsa65_signature_internal_join36)
                 else word (pc + mldsa65_signature_internal_join35)) /\\
                read RSP s = rsp0 /\\ read R15 s = word 0 /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55
                 ==> ~(word_zx (read RBX s) = (word 0:byte))) /\\
                read (memory :> bytes (sig,48)) s = C /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55
                 ==> !t. t < 61
                         ==> read (memory :> bytes8 (word_add sig (word (3248 + t)))) s =
                             mld_pack_hints 55 6 (mld_polyvec_make_hint_32 x b) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig rsp0 pc x b /\\
                   memaccess_inbounds e2 [sig,3309; rsp0,12576] [sig,3309; rsp0,12576]))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R15] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(sig,48);
                       memory :> bytes(word_add sig (word 3248),61);
                       memory :> bytes(word_add rsp0 (word 544),1024)])");;

let SI65_TAIL_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_loop51_exit1", layout "mldsa65_signature_internal" + 0x2e8d)];;

let T65_TEMPLATE =
 `\(sig:int64) (rsp0:int64) (pc:num) (x:num->int32) (b:num->byte).
   if mld_hint_count (mld_polyvec_make_hint_32 x b) 256 <= 55 then
    (if mld_hint_count (mld_polyvec_make_hint_32 x b) 512 <= 55 then
      (if mld_hint_count (mld_polyvec_make_hint_32 x b) 768 <= 55 then
        (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1024 <= 55 then
          (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1280 <= 55 then
            (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55
             then f_ev_ok sig rsp0 pc x b else f_ev_r5 sig rsp0 pc x b)
           else f_ev_r4 sig rsp0 pc x b)
         else f_ev_r3 sig rsp0 pc x b)
       else f_ev_r2 sig rsp0 pc x b)
     else f_ev_r1 sig rsp0 pc x b)
   else f_ev_r0 sig rsp0 pc x b :(uarch_event)list`;;

let T65_CALL_TAC = SI_GCALL_TAC SI65_TAIL_EXEC
  [`sig:int64`; `rsp0:int64`; `pc:num`; `x:num->int32`; `b:num->byte`] SI_XMM_PRE_TAC;;

let T65_B_SLICE_TAC k n =
  let ib = 2848 + 128 * k and wb = 128 * k in
  let st = mk_var("s"^string_of_int n,`:x86state`) in
  SUBGOAL_THEN (vsubst [st,`s:x86state`] (parse_term(Printf.sprintf
    "!j. j < 128 ==> read (memory :> bytes8 (word_add rsp0 (word (%d + j)))) s = b (%d + j)" ib wb)))
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" wb)) o check (fun th ->
      is_forall(concl th) && can (term_match [] `!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (2848 + j)))) s = b j`) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "2848 + %d + j = %d + j" wb ib))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `j < 128` THEN ARITH_TAC;
    ALL_TAC];;

let T65_X_SLICE_TAC k n =
  let w = 5376 + 1024 * k and p0 = 256 * k in
  let st = mk_var("s"^string_of_int n,`:x86state`) in
  SUBGOAL_THEN (vsubst [st,`s:x86state`] (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * i)))) s = x (%d + i)" w p0)))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" p0)) o check (fun th ->
      is_forall(concl th) && can (term_match [] `!j. j < 1536 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * j)))) s = x j`) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "5376 + 4 * (%d + i) = %d + 4 * i" p0 w))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC];;

let T65_CNT_TM p = subst [mk_small_numeral p,`p:num`] `mld_hint_count (mld_polyvec_make_hint_32 x b) p <= 55`;;

let T65_SPLIT_TAC p =
  let c = T65_CNT_TM p in
  ASM_CASES_TAC c THEN
  FIRST_ASSUM(fun th -> if concl th = c || concl th = mk_neg c
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `RAX` (concl th)
                                then STRIP_ASSUME_TAC th else NO_TAC));;

let T65_FAIL_TAC p =
  SUBGOAL_THEN (mk_neg(T65_CNT_TM 1536)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; mk_small_numeral p; `1536`] MLD_HINT_COUNT_MONO) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(T65_CNT_TM p))) THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* row k > 0: xor ecx; nop, W1U at n + 2, xor ecx; jmp, HROW at n + 5 *)
let T65_ROW_TAC k n =
  let p1 = 256 * (k + 1) in
  X86_STEPS_TAC SI65_TAIL_EXEC (n--(n+1)) THEN T65_B_SLICE_TAC k (n+1) THEN
  T65_CALL_TAC ("H_W1U"^string_of_int k)
   [`rsp0:int64`; `pc:num`; parse_term(Printf.sprintf "\\t. (b:num->byte) (%d + t)" (128 * k))] (n+2) THEN
  X86_STEPS_TAC SI65_TAIL_EXEC ((n+3)--(n+4)) THEN T65_X_SLICE_TAC k (n+4) THEN
  T65_CALL_TAC ("H_HROW"^string_of_int k)
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `rsp0:int64`; `pc:num`] (n+5) THEN
  T65_SPLIT_TAC p1 THENL [ALL_TAC; T65_FAIL_TAC p1];;

let T65_PACK_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `t = 55 \/ t = 56 \/ t = 57 \/ t = 58 \/ t = 59 \/ t = 60` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`t < 61`; `~(t < 55)`] THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]];;

let SI65_TAIL = prove
 (SI65_TAIL_STMT,
  (MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [SI65_W1UM62,"H_W1U0"; SI65_W1UM63,"H_W1U1"; SI65_W1UM64,"H_W1U2"; SI65_W1UM65,"H_W1U3";
    SI65_W1UM66,"H_W1U4"; SI65_W1UM67,"H_W1U5";
    SI65_HROW0,"H_HROW0"; SI65_HROW1,"H_HROW1"; SI65_HROW2,"H_HROW2"; SI65_HROW3,"H_HROW3";
    SI65_HROW4,"H_HROW4"; SI65_HROW5,"H_HROW5"] THEN
  CONCRETIZE_F_EVENTS_TAC T65_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `rsp0:int64`; `rb0:int64`; `C:num`;
                       `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES; fst SI65_TAIL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x1e0; 0x1f0; 0x200; 0x220] THEN
  MAP_EVERY (fun r -> GHOST_INTRO_TAC (mk_var("ymm"^string_of_int r^"_init",`:int256`))
                       (mk_comb(`read:(x86state,int256)component->x86state->int256`,
                                mk_const("YMM"^string_of_int r,[]))))
    [0;1;2;4] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `word_subword (ymm4_init:int256) (0,128):int128 = word 0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `read XMM4 s0 = word 0`)) THEN
    REWRITE_TAC[XMM4; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[T65_ZX_SUB];
    ALL_TAC]) THEN
  (MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add rsp0 (word 480):int64`; `48`; `C:num`; mk_small_numeral n; `s0:x86state`]
             SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1;2]) THEN
  (X86_STEPS_TAC SI65_TAIL_EXEC (1--9) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; DIV_1; T65_Y4]) THEN
   FIRST_ASSUM(fun th ->
     if can (term_match [] `read (memory :> bytes128 (word_add sig (word 3293))) s9 = x`) (concl th)
     then MP_TAC(SPECL [`word_add sig (word 3293):int64`; `3`; `s9:x86state`] SI_BYTES128_ZERO_SUFFIX)
     else NO_TAC) THEN
   ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC
                      ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN DISCH_TAC THEN
   X86_STEPS_TAC SI65_TAIL_EXEC (10--12) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[T65_Y4])) THEN
  (SUBGOAL_THEN `C < 2 EXP (8 * 48)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (word_add rsp0 (word 480),48)) s0 = C`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sig:int64`; `C:num`; `3`; `s12:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 2 EXP (128 * 3) = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `C < 2 EXP (8 * 48)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC) THEN
  (MP_TAC(SPECL [`word_add sig (word 3248):int64`; `0`; `3`; `s12:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_0] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add sig (word 3248),61)) s12 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `61 = 48 + 13`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word_add sig (word 3248),61)) s12 = 0`) (concl th)
    then ASSUME_TAC(GEN `t:num`
      (REWRITE_RULE[GSYM(INST [T65_MH,`h:num->bool`] (CONJUNCT1 mld_hint_index));
                    WORD_RULE `word_add (word_add sig (word 3248)) (word t) = word_add sig (word (3248 + t))`]
        (SPEC `t:num` (MATCH_MP SIGN_BYTES8_ZERO th))))
    else NO_TAC)) THEN
  (X86_STEPS_TAC SI65_TAIL_EXEC (13--14) THEN T65_B_SLICE_TAC 0 14 THEN
  T65_CALL_TAC "H_W1U0" [`rsp0:int64`; `pc:num`; `\t. (b:num->byte) (0 + t)`] 15) THEN
  (X86_STEPS_TAC SI65_TAIL_EXEC (16--19) THEN T65_X_SLICE_TAC 0 19 THEN
  ASSUME_TAC(INST [T65_MH,`h:num->bool`] (CONJUNCT1 mld_hint_count)) THEN
  ASSUME_TAC(ARITH_RULE `0 <= 55`) THEN
  T65_CALL_TAC "H_HROW0" [`x:num->int32`; `b:num->byte`; `sig:int64`; `rsp0:int64`; `pc:num`] 20) THEN
  (T65_SPLIT_TAC 256 THENL [ALL_TAC; T65_FAIL_TAC 256]) THEN
  (T65_ROW_TAC 1 21) THEN
  (T65_ROW_TAC 2 27) THEN
  (T65_ROW_TAC 3 33) THEN
  (T65_ROW_TAC 4 39) THEN
  (T65_ROW_TAC 5 45) THEN
  (X86_STEPS_TAC SI65_TAIL_EXEC (51--52) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SI_BL_NZ]) THEN
  (CONJ_TAC THENL [T65_PACK_TAC; DISCHARGE_SAFETY_PROPERTY_TAC]));;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt (HEAD), from join2 with the number n of the       *)
(* attempt in RCX and XMM4 = 0: n saved at rsp0 + 0xb0, the pointer to rho'' *)
(* and kappa = 5 n (16 bits) at rsp0 + 0x80 and + 0x88, rho copied from rsp0 *)
(* + 0x1220 to the seed buffer at rsp0 + 0x1240, the five columns of the     *)
(* product with the matrix (YCOL 0 .. 4) and HPOST, to after the NTT of the  *)
(* challenge, as gcc's SIGN65_HEAD.                                          *)
(* ------------------------------------------------------------------------- *)

let HD65_Y = `mld_sign_y mld_poly_uniform_gamma1_19 rhop (5 * n)`;;
let HD65_W = list_mk_comb(`mld_sign_w 5`,[SI65_A; HD65_Y]);;
let HD65_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128`,HD65_W);;
let HD65_CT = mk_comb(`mld_sign_ctilde 6 128 mu`,HD65_W1);;

let SI65_HEAD_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@W@",string_of_term HD65_W; "@W1@",string_of_term HD65_W1;
   "@CT@",string_of_term HD65_CT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 n rho rhop mu C pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ n < 13106 /\\ mld_matrix_terminates 6 5 rho /\\
          num_of_bytelist(list_of_seq (@CT@) 48) = C /\\
          mld_poly_challenge_terminates 49 48 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_join2) /\\
                read RSP s = rsp0 /\\ read RCX s = word n /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word 4640),32)) s = rho /\\
                read (memory :> bytes (word_add rsp0 (word 1696),64)) s = mu /\\
                read (memory :> bytes (word_add rsp0 (word 1760),64)) s = rhop /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa65_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 176))) s = word n /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 1760) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word (5 * n) /\\
                (!i. i < 1536 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 (@W@) i) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (2848 + j)))) s =
                                 (@W1@) j) /\\
                read (memory :> bytes (word_add rsp0 (word 480),48)) s = C /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (11520 + 4 * k)))) s =
                                 mld_poly_ntt (mld_poly_challenge 49 48 C) k) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rho C mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),14047;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa65_poly_challenge_consts),48;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 24),4);
                       memory :> bytes(word_add rsp0 (word 128),16);
                       memory :> bytes(word_add rsp0 (word 176),8);
                       memory :> bytes(word_add rsp0 (word 480),48);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word 1824),208);
                       memory :> bytes(word_add rsp0 (word 2848),768);
                       memory :> bytes(word_add rsp0 (word 3616),1024);
                       memory :> bytes(word_add rsp0 (word 4672),64);
                       memory :> bytes(word_add rsp0 (word 5376),6144);
                       memory :> bytes(word_add rsp0 (word 11520),1024)])");;

let SI65_HEAD_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_join2", layout "mldsa65_signature_internal_after_mldsa_poly_ntt_2")];;

let HD65_ALLOWED = [`rsp0:int64`; `rho:num`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let HD65_CALL_TAC = SI_GCALL_TAC SI65_HEAD_EXEC HD65_ALLOWED SI_XMM_PRE_TAC;;

(* the 16-bit store of 5 n *)
let HD65_KAPPA = prove
 (`!n. n < 13106
       ==> word (val (word_zx (word_sx (word_add (word n) (word (4 * val (word n:int64))):int64):int32):int64)
                 MOD 65536):int16 =
           word (5 * n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SI_SX_ZX; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  SUBGOAL_THEN `n < 2 EXP 64 /\ 4 * n < 2 EXP 64 /\ n + 4 * n < 2 EXP 64 /\
                n + 4 * n < 2 EXP 32 /\ n + 4 * n < 65536`
    STRIP_ASSUME_TAC THENL [UNDISCH_TAC `n < 13106` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN AP_TERM_TAC THEN ARITH_TAC);;

let HD65_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [MP (SPEC_ALL SI65_YCOL0) th,"H_YC0"; MP (SPEC_ALL SI65_YCOL1) th,"H_YC1";
      MP (SPEC_ALL SI65_YCOL2) th,"H_YC2"; MP (SPEC_ALL SI65_YCOL3) th,"H_YC3";
      MP (SPEC_ALL SI65_YCOL4) th,"H_YC4";
      MP (SPEC_ALL SI65_HPOST) th,"H_HP"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rho:num) (C:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_head rsp0 rho C mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `n:num`; `rho:num`; `rhop:num`;
                       `mu:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_HEAD_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x1220; 0x1230; 0x1240; 0x1250] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`word_add rsp0 (word 4640):int64`; `32`; `rho:num`; mk_small_numeral i; `s0:x86state`]
             SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1] THEN
  X86_STEPS_TAC SI65_HEAD_EXEC (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; DIV_1]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HD65_KAPPA (ASSUME `n < 13106`)]) THEN
  SUBGOAL_THEN `rho < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (word_add rsp0 (word 4640),32)) s0 = rho`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add rsp0 (word 4672):int64`; `rho:num`; `2`; `s12:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho MOD 2 EXP (128 * 2) = rho` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `rho < 2 EXP (8 * 32)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  HD65_CALL_TAC "H_YC0" [`rsp0:int64`; `rho:num`; `rhop:num`; `5 * n`; `pc:num`] 13 THEN
  MAP_EVERY (fun j ->
    let n0 = 14 + 4 * (j - 1) in
    X86_STEPS_TAC SI65_HEAD_EXEC (n0--n0) THEN
    RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R12 s = x`) (concl th)
                             then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
    X86_STEPS_TAC SI65_HEAD_EXEC ((n0+1)--(n0+2)) THEN
    HD65_CALL_TAC ("H_YC"^string_of_int j) [`rsp0:int64`; `rho:num`; `rhop:num`; `5 * n`; `pc:num`]
      (n0+3)) [1;2;3;4] THEN
  X86_STEPS_TAC SI65_HEAD_EXEC (30--30) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R12 s = x`) (concl th)
                           then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
  X86_STEPS_TAC SI65_HEAD_EXEC (31--32) THEN
  HD65_CALL_TAC "H_HP" [`rsp0:int64`; `rho:num`; `rhop:num`; `5 * n`; `mu:num`; `C:num`; `pc:num`] 33 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI_END_TAC 1471;;

let SI65_HEAD = prove(SI65_HEAD_STMT, HD65_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt (ATT), from join2 to the decision after the cleanup: to   *)
(* join37 on success (r = 18) and to the count of the attempts at +0x2e61    *)
(* otherwise, by cases on the result r of mld_sign_attempt_declass, as       *)
(* gcc's SIGN65_ATT: r < 5 (z_r fails, ZPRE then ZIT), 5 <= r < 17 (check    *)
(* r - 5 of the rows fails, ZPRE, RPRE then RIT), 17 (too many hints) and 18 *)
(* (success), both through TAIL; then CLEAN, which leaves XMM4 = 0 for the   *)
(* next attempt.                                                             *)
(* ------------------------------------------------------------------------- *)

let AT65_W = HD65_W;;
let AT65_W1 = HD65_W1;;
let AT65_CPH = `mld_poly_ntt (mld_poly_challenge 49 48 C)`;;
let AT65_R0 = list_mk_comb(`mld_sign_r0`,[`mld_poly_decompose_lo_32`; AT65_W; SI65_S2H; AT65_CPH]);;
let AT65_CT0 = list_mk_comb(`mld_sign_ct0`,[SI65_T0H; AT65_CPH]);;
let AT65_SIGATT = list_mk_comb(
 `mld_sign_attempt_sig 6 5 48 49 mld_poly_uniform_gamma1_19 mld_polyz_pack_19
   640 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55`,
  [SI65_A; SI65_S1H; SI65_S2H; SI65_T0H; `mu:num`; `rhop:num`; `5 * n`]);;

let SI65_ATT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@SIGATT@",string_of_term AT65_SIGATT;
   "@S1H@",string_of_term SI65_S1H; "@S2H@",string_of_term SI65_S2H; "@T0H@",string_of_term SI65_T0H;
   "@NX@",string_of_int SI65_NX]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig sk skb rsp0 rho mu rhop n C r x b pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ n < 13106 /\\ mld_matrix_terminates 6 5 rho /\\
          mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
           524092 261692 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
           128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
           (mld_polyvec_matrix_expand 5 rho) (@S1H@) (@S2H@) (@T0H@)
           mu rhop (5 * n) = (C,r,x,b) /\\
          mld_poly_challenge_terminates 49 48 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),14047))
              [(sig,3309); (sk,4032); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,3309))
              [(sk,4032); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa65_signature_internal_join2) /\\
                read RSP s = rsp0 /\\ read RCX s = word n /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 8))) s = sig /\\
                read (memory :> bytes64 (word_add rsp0 (word 16))) s = word_add sig (word 3248) /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 768) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 1536) /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 168))) s = word_add sig (word 51) /\\
                read (memory :> bytes (word_add rsp0 (word 4640),32)) s = rho /\\
                read (memory :> bytes (word_add rsp0 (word 1696),64)) s = mu /\\
                read (memory :> bytes (word_add rsp0 (word 1760),64)) s = rhop /\\
                (!k. k < 4032 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if r = 18 then word (pc + mldsa65_signature_internal_join37)
                 else word (pc + @NX@)) /\\
                read RSP s = rsp0 /\\ read R15 s = word 0 /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 176))) s = word n /\\
                (r = 18
                 ==> !t. t < 3309
                         ==> read (memory :> bytes8 (word_add sig (word t))) s = (@SIGATT@) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig sk rsp0 rho C r x b mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,3309; sk,4032; word_sub rsp0 (word 1471),14047;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),784;
                     word(pc + mldsa65_poly_challenge_consts),48;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,3309; word_sub rsp0 (word 1471),14047]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(sig,3309);
                       memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 24),8);
                       memory :> bytes(word_add rsp0 (word 128),16);
                       memory :> bytes(word_add rsp0 (word 160),8);
                       memory :> bytes(word_add rsp0 (word 176),8);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 192),66);
                       memory :> bytes(word_add rsp0 (word 272),208);
                       memory :> bytes(word_add rsp0 (word 480),48);
                       memory :> bytes(word_add rsp0 (word 544),1024);
                       memory :> bytes(word_add rsp0 (word 1824),1024);
                       memory :> bytes(word_add rsp0 (word 2848),768);
                       memory :> bytes(word_add rsp0 (word 3616),1024);
                       memory :> bytes(word_add rsp0 (word 4672),680);
                       memory :> bytes(word_add rsp0 (word 5376),6144);
                       memory :> bytes(word_add rsp0 (word 11520),1024)])");;

let SI65_ATT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa65_signature_internal_join2", SI65_NX);
   layout_range "plt_memset"];;

let AT65_ALLOWED =
  [`sig:int64`; `sk:int64`; `rsp0:int64`; `rho:num`; `C:num`; `r:num`;
   `x:num->int32`; `b:num->byte`; `mf:int64`; `mc:int64`; `pc:num`];;

let AT65_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI65_ATT_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      TRY(SI_XMM_PRE_TAC THEN NO_TAC) THEN
      VM_PRE_TAC AT65_ALLOWED;
      LABEL_TAC name th]);;

let AT65_MID = parse_term(subst_tokens ["@SIGATT@",string_of_term AT65_SIGATT]
 "\\s. read RSP s = rsp0 /\\
      (word_zx (read RBX s) = (word 0:byte) <=> ~(r = 18)) /\\
      read R15 s = word 0 /\\
      (read DF s <=> false) /\\
      read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
      read (memory :> bytes(ea,el)) s = ev /\\
      read (memory :> bytes64 (word_add rsp0 (word 176))) s = word n /\\
      (r = 18
       ==> !t. t < 3309
               ==> read (memory :> bytes8 (word_add sig (word t))) s = (@SIGATT@) t)");;

(*** z_r fails, r < 5 ***)

let AT65_ZCASE_TAC =
  SUBGOAL_THEN `r <= 5 /\ ~(r = 18)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 5` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 5 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  AT65_CALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `5 * n`; AT65_CPH; `pc:num`] 2 THEN
  SI_PC_TAC THEN
  AT65_CALL_TAC "H_ZIT"
   [`F`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `5 * n`; `r:num`; AT65_CPH; `pc:num`] 3 THEN
  SI_PC_TAC THEN
  X86_STEPS_TAC SI65_ATT_EXEC (4--4) THEN
  SI_FIN_TAC 1471;;

let AT65_TEMPLATE =
 `\(sig:int64) (sk:int64) (rsp0:int64) (rho:num) (C:num) (r:num) (x:num->int32) (b:num->byte)
   (mf:int64) (mc:int64) (pc:num).
   APPEND (f_ev_cl sig sk rsp0 rho C r x b mf mc pc)
    (APPEND
      (if r < 5 then f_ev_pz sig sk rsp0 rho C r x b mf mc pc
       else if r < 17
       then if EVEN (r - 5) then f_ev_pw1 sig sk rsp0 rho C r x b mf mc pc
            else f_ev_pw2 sig sk rsp0 rho C r x b mf mc pc
       else f_ev_pt sig sk rsp0 rho C r x b mf mc pc)
      (f_ev_hd sig sk rsp0 rho C r x b mf mc pc))
   :(uarch_event)list`;;

let AT65_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> SI_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI65_HEAD) th,"H_HEAD"; MP (SPEC_ALL SI65_ZPRE) th,"H_ZPRE";
      MP (SPEC_ALL SI65_ZIT) th,"H_ZIT"; SI65_RPRE,"H_RPRE"; SI65_RIT,"H_RIT";
      SI65_TAIL,"H_TAIL"; MP (SPEC_ALL SI65_CLEAN) ms,"H_CLEAN"]) THEN
  CONCRETIZE_F_EVENTS_TAC AT65_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rho:num`; `mu:num`; `rhop:num`; `n:num`; `C:num`; `r:num`; `x:num->int32`;
    `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_ATT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
   `mld_sign_attempt_declass k l ctlen tau g1 bndz bndw bndh w1enc w1p dlo
     mkhint omega A s1hat s2hat t0hat mu rhoprime kappa = (C,r,x,b)`)
   (concl th))) THEN
  REWRITE_TAC[mld_sign_attempt_declass] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[mld_sign_cphat; th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIGN_REJ_CASES o check (fun th ->
    can (term_match []
     `mld_sign_rej k l bndz bndw bndh omega mkhint z r0 ct0 x w1 = r`)
     (concl th))) THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
  STRIP_TAC;;

(*** check r - 5 of the rows fails, 5 <= r < 17 ***)

let AT65_ROWSLICE_TAC m st =
  MP_TAC(SPECL [`rsp0:int64`; `5376`; `1536`; `mld_poly_decompose_lo_32`; AT65_W; m; st]
               SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [m; st]
             `!k. 256 * m <= k /\ k < 1536
                  ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) st = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

let AT65_WCASE_TAC =
  SUBGOAL_THEN `(r - 5) DIV 2 <= 6 /\ (r - 5) DIV 2 < 6 /\ ~(r = 18) /\
                2 * (r - 5) DIV 2 <= r - 5`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 17` THEN UNDISCH_TAC `5 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [AT65_R0; AT65_CT0; `261692`; `261888`; `r - 5`;
                `(r - 5) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 5` THEN UNDISCH_TAC `r < 17` THEN ARITH_TAC;
    DISCH_TAC] THEN
  AT65_CALL_TAC "H_ZPRE"
   [`5`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `5 * n`; AT65_CPH; `pc:num`] 2 THEN
  SI_PC_TAC THEN
  AT65_CALL_TAC "H_RPRE"
   [`(r - 5) DIV 2`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; AT65_W; AT65_CPH; `pc:num`] 3 THEN
  SI_PC_TAC THEN
  AT65_ROWSLICE_TAC `(r - 5) DIV 2` `s3:x86state` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `5 <= r /\ r < 17 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 5)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 5) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    AT65_CALL_TAC "H_RIT"
     [`F`; `F`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `(r - 5) DIV 2`; AT65_W; AT65_CPH;
      `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 5) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`5`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 6` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 17` THEN ARITH_TAC; DISCH_TAC] THEN
    AT65_CALL_TAC "H_RIT"
     [`T`; `F`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `(r - 5) DIV 2`; AT65_W; AT65_CPH;
      `pc:num`] 4] THEN
  SI_PC_TAC THEN
  X86_STEPS_TAC SI65_ATT_EXEC (5--7) THEN
  SI_FIN_TAC 1471;;

(*** the hints, r = 17 (too many) or 18 (success) ***)

let AT65_TCASE_TAC =
  SUBGOAL_THEN `17 <= r /\ 5 <= 5` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 17)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [AT65_R0; AT65_CT0; `261692`; `261888`; `12`; `6`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `17 <= r` THEN UNDISCH_TAC `j < 12` THEN ARITH_TAC;
    DISCH_TAC] THEN
  AT65_CALL_TAC "H_ZPRE"
   [`5`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `5 * n`; AT65_CPH; `pc:num`] 2 THEN
  SI_PC_TAC THEN
  AT65_CALL_TAC "H_RPRE"
   [`6`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; AT65_W; AT65_CPH; `pc:num`] 3 THEN
  SI_PC_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ARITH_RULE `0 < 6`] o
    check (fun th -> is_imp(concl th) && lhand(concl th) = `0 < 6`)) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 17 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 17 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add rsp0 (word (2848 + j)))) s3 =
            (b:num->byte) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "b"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_hint_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  AT65_CALL_TAC "H_TAIL"
   [`sig:int64`; `rsp0:int64`; `read RBX s`; `C:num`; `x:num->int32`; `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `17 <= r ==> (r = 18 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 18` THENL
   [SUBGOAL_THEN `mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 18`
                            then ACCEPT_TAC(EQ_MP th (ASSUME `r = 18`)) else NO_TAC); ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55`]) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`sig:int64`; `C:num`] `read (memory :> bytes (sig,48)) s = C`) (concl th)
      then FIRST_ASSUM(fun cth ->
             if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
             then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES (TRANS th (SYM cth)))
             else NO_TAC)
      else NO_TAC) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if concl th = `r = 18` then ASSUME_TAC(EQT_INTRO th)
                                   else NO_TAC)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[mld_sign_attempt_sig] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `3309 = (48 + 5 * 640) + 61` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> can (term_match []
          `!t. t < 640 * 5
               ==> read (memory :> bytes8 (word_add sig (word (48 + t)))) s =
                   P t`) (concl th))) THEN NO_TAC) THEN
    (SI_MAYCHANGE_TAC 1471 ORELSE SI_PATH_DISCHARGE_TAC 1471);
    SUBGOAL_THEN `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 18`
                            then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[ASSUME `~(r = 18)`]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55)`]) THEN
    X86_STEPS_TAC SI65_ATT_EXEC (5--5) THEN
    SI_FIN_TAC 1471];;

let AT65_PATHS_TAC =
  ASM_CASES_TAC `r < 5` THENL
   [AT65_ZCASE_TAC;
    SUBGOAL_THEN `5 <= r /\ 5 <= 5` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 5)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `5 <= r ==> (!i. i < 5 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r < 17` THENL [AT65_WCASE_TAC; AT65_TCASE_TAC]];;

let AT65_CLEAN_TAC =
  FULL_INIT_TAC THEN
  AT65_CALL_TAC "H_CLEAN" [`r = 18`; `rsp0:int64`; `read RBX s`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (SI_MAYCHANGE_TAC 1471 ORELSE SI_DISCHARGE_TAC 1471);;

let SI65_ATT = prove
 (SI65_ATT_STMT,
  AT65_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_signature_internal_join36` AT65_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    AT65_CALL_TAC "H_HEAD"
     [`rsp0:int64`; `n:num`; `rho:num`; `rhop:num`; `mu:num`; `C:num`; `pc:num`] 1 THEN
    AT65_PATHS_TAC;
    AT65_CLEAN_TAC]);;
