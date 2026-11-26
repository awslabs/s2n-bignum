(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The stages of an attempt of mldsa87_signature_internal (clang 23 -O3 mono *)
(* reduced-RAM), as FULL lemmas for segments of the code at the frame rsp0   *)
(* of the attempt, made from those of signature_internal_65_stages.ml for    *)
(* the parameters of ML-DSA-87 (K = 8, L = 7, eta = 2), with the region      *)
(* lemmas of signature_internal_87_inline.ml. The frame of the attempt is    *)
(* 14912 bytes at rsp0, and the callees use the 1471 bytes below it.         *)
(*                                                                           *)
(* Where 87 differs from 65: s1 and s2 are packed with eta = 2 (96 bytes per *)
(* polynomial, as in 44); the row loop keeps the row of w in RBX and its     *)
(* counter in the slot at rsp0 + 0x38; the result of the attempt is the     *)
(* 32-bit slot at rsp0 + 0x30 (zeroed before the rows, and on a failed       *)
(* check of z) rather than R15; the decomposition and the packing of w1 are *)
(* one rolled loop (DW1R) and c~ = H(mu || w1) is inlined (C2) instead of a  *)
(* call of mld_H87.                                                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_87_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_stage2.ml";;

let SI87_FRAME = 16383;;

(* ------------------------------------------------------------------------- *)
(* s2 and t0 in the NTT domain, from the secret key skb (as in the gcc       *)
(* proof, SIGN87_S2H and SIGN87_T0H).                                        *)
(* ------------------------------------------------------------------------- *)

let SI87_S2H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(800 + j)))`;;

let SI87_T0H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(1568 + j)))`;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over the rows of w0 (RIT), from loop55 with row *)
(* j in RAX (saved at rsp0 + 0x38), its address in RBX and the offsets of    *)
(* s2_j and t0_j in the key in R14 and R15 (saved at rsp0 + 0xb8 around the  *)
(* unpacking of t0_j): s2_j unpacked into the scratch polynomial at rsp0 +   *)
(* 0x340 and transformed, its product with the challenge, w0_j - c s2_j in   *)
(* place and reduced, its norm check; then t0_j likewise, c t0_j reduced and *)
(* checked, and the sum in place in row j. ok1 and ok2 are the results of    *)
(* the two checks (ok2 matters only when ok1 holds): if both pass, the code  *)
(* goes back to loop55 or, after the last row, to loop55_exit1, else to the  *)
(* rejection at join22. On success XMM4 is 0 and XMM5 holds the constant of  *)
(* the unpacking of w1 that follows the loop. The callees (NTT, inverse NTT) *)
(* use the stack below rsp0.                                                 *)
(* ------------------------------------------------------------------------- *)

let R87_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_32`; `w:num->int32`; SI87_S2H; `cphat:num->int32`; `j:num`]);;
let R87_CT0 = list_mk_comb(`mld_sign_ct0`, [SI87_T0H; `cphat:num->int32`; `j:num`]);;

let SI87_RIT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@R0@",string_of_term R87_R0; "@CT0@",string_of_term R87_CT0;
   "@FAIL@",string_of_int(layout "mldsa87_signature_internal_join22")]
 "exists f_events.
    forall e ok1 ok2 sk skb rsp0 j w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\ j < 8 /\\
      (ok1 <=> mld_poly_chknorm (@R0@) (word 261768) = word 0) /\\
      (ok1 ==> (ok2 <=> mld_poly_chknorm (@CT0@) (word 261888) = word 0)) /\\
      ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
          [(sk,4896); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_loop55) /\\
                read RSP s = rsp0 /\\ read RAX s = word j /\\ read R14 s = word (2 + 96 * j) /\\
                read R15 s = word (12 + 416 * j) /\\
                read RBX s = word_add rsp0 (word (6688 + 1024 * j)) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 800) /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 1568) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * i)))) s =
                                 cphat i) /\\
                (!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                (!i. i < 256 ==> read (memory :> bytes32
                                   (word_add rsp0 (word ((6688 + 1024 * j) + 4 * i)))) s =
                                 mld_poly_decompose_lo_32 (mld_poly_of w j) i) /\\
                read events s = e)
           (\\s. read RIP s =
                (if ok1 /\\ ok2
                 then (if j + 1 < 8 then word (pc + mldsa87_signature_internal_loop55)
                       else word (pc + mldsa87_signature_internal_loop55_exit1))
                 else word (pc + @FAIL@)) /\\
                read RSP s = rsp0 /\\
                (ok1 /\\ ok2
                 ==> read RAX s = word (j + 1) /\\ read R14 s = word (2 + 96 * (j + 1)) /\\
                     read R15 s = word (12 + 416 * (j + 1)) /\\
                     read RBX s = word_add rsp0 (word (6688 + 1024 * (j + 1))) /\\
                     read XMM4 s = word 0 /\\
                     read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
                     (!i. i < 256 ==> read (memory :> bytes32
                                        (word_add rsp0 (word ((6688 + 1024 * j) + 4 * i)))) s =
                                      mld_poly_add (@R0@) (@CT0@) i)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok1 ok2 sk rsp0 j pc /\\
                   memaccess_inbounds e2
                    [sk,4896; word_sub rsp0 (word 1471),16383;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 16),16);
                       memory :> bytes(word_add rsp0 (word 56),8);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word (6688 + 1024 * j)),1024)])");;

let SI87_RIT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_loop55", layout "mldsa87_signature_internal_loop55_exit1")];;

let R87_TEMPLATE =
 `\(ok1:bool) (ok2:bool) (sk:int64) (rsp0:int64) (j:num) (pc:num).
   if ok1 then
    (if ok2 then (if j + 1 < 8 then f_ev_mid sk rsp0 j pc else f_ev_last sk rsp0 j pc)
     else f_ev_f2 sk rsp0 j pc)
   else f_ev_f1 sk rsp0 j pc :(uarch_event)list`;;

let R87_ALLOWED = [`ok1:bool`; `ok2:bool`; `sk:int64`; `rsp0:int64`; `j:num`; `pc:num`];;

let R87_CALL_TAC = SI_GCALL_TAC SI87_RIT_EXEC R87_ALLOWED ALL_TAC;;
let R87_FCALL_TAC = SI_GFCALL_TAC SI87_RIT_EXEC R87_ALLOWED ALL_TAC;;

let R87_RCONST_TAC = SI_RCONST_TAC "mldsa87_signature_internal"
  ["mldsa87_signature_internal_const1"; "mldsa87_signature_internal_const2"] ["YMM5"; "YMM6"];;

let R87_B = `word_add rsp0 (word (6688 + 1024 * j)):int64`;;
let R87_S2I = mk_comb(mk_comb(`mld_poly_of`,SI87_S2H),`j:num`);;
let R87_T0I = mk_comb(mk_comb(`mld_poly_of`,SI87_T0H),`j:num`);;
let R87_PW1 = list_mk_comb(`mld_poly_pointwise_montgomery`,[R87_S2I; `cphat:num->int32`]);;
let R87_PW2 = list_mk_comb(`mld_poly_pointwise_montgomery`,[R87_T0I; `cphat:num->int32`]);;
let R87_W0J = `mld_poly_decompose_lo_32 (mld_poly_of (w:num->int32) j)`;;
let R87_CS2 = mk_comb(`mld_poly_invntt_tomont`,R87_PW1);;
let R87_SUBX = list_mk_comb(`mld_poly_sub`,[R87_W0J; R87_CS2]);;

(* bytes off .. off + n - 1 of the secret key at state st *)
let R87_SLICE_TAC off n st =
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `4896`; off; n; st] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `j < 8` THEN ARITH_TAC; DISCH_TAC];;

let R87_TEST = SI_TEST_RULE 8;;

(*** w0_j - c s2_j: steps 1 to 28 ***)

let R87_PART1_TAC =
  X86_STEPS_TAC SI87_RIT_EXEC (1--5) THEN
  R87_SLICE_TAC `800 + 96 * j` `96` `s5:x86state` THEN
  R87_CALL_TAC "H_ETA" [`word_add sk (word (800 + 96 * j)):int64`; `rsp0:int64`; `pc:num`;
                        `\i. (skb:num->byte)((800 + 96 * j) + i)`] 6 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_2` THEN
  X86_STEPS_TAC SI87_RIT_EXEC (7--8) THEN
  R87_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(800 + j))) j`] 9 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI87_RIT_EXEC (10--12) THEN
  R87_CALL_TAC "H_PWM1" [`rsp0:int64`; `pc:num`; R87_S2I; `cphat:num->int32`] 13 THEN
  X86_STEPS_TAC SI87_RIT_EXEC (14--15) THEN
  R87_FCALL_TAC "H_INV" [`read RDI s`; R87_PW1] 16 THEN
  X86_STEPS_TAC SI87_RIT_EXEC (17--18) THEN
  R87_CALL_TAC "H_SUB" [R87_B; `rsp0:int64`; `pc:num`; R87_W0J; R87_CS2] 19 THEN
  X86_STEPS_TAC SI87_RIT_EXEC (20--20) THEN R87_RCONST_TAC 20 0x2a4b THEN
  X86_STEPS_TAC SI87_RIT_EXEC (21--23) THEN
  R87_CALL_TAC "H_RED1" [R87_B; `pc:num`; R87_SUBX] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  X86_STEPS_TAC SI87_RIT_EXEC (25--27) THEN
  R87_CALL_TAC "H_CHK1" [R87_B; `pc:num`; R87_R0] 28;;

(*** c t0_j, once the first check passed: steps 31 to 59 ***)

let R87_PART2_TAC =
  SI_PASS_TAC `ok1:bool` THEN
  X86_STEPS_TAC SI87_RIT_EXEC (31--35) THEN
  R87_SLICE_TAC `1568 + 416 * j` `416` `s35:x86state` THEN
  R87_CALL_TAC "H_T0U" [`word_add sk (word (1568 + 416 * j)):int64`; `rsp0:int64`; `pc:num`;
                        `\i. (skb:num->byte)((1568 + 416 * j) + i)`] 36 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyt0_unpack` THEN
  X86_STEPS_TAC SI87_RIT_EXEC (37--38) THEN
  R87_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(1568 + j))) j`] 39 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI87_RIT_EXEC (40--41) THEN
  R87_CALL_TAC "H_PWM2" [`rsp0:int64`; `pc:num`; R87_T0I; `cphat:num->int32`] 42 THEN
  X86_STEPS_TAC SI87_RIT_EXEC (43--44) THEN
  R87_FCALL_TAC "H_INV" [`read RDI s`; R87_PW2] 45 THEN
  X86_STEPS_TAC SI87_RIT_EXEC (46--46) THEN R87_RCONST_TAC 46 0x2dcb THEN
  X86_STEPS_TAC SI87_RIT_EXEC (47--49) THEN
  R87_CALL_TAC "H_RED2" [`rsp0:int64`; `pc:num`; mk_comb(`mld_poly_invntt_tomont`,R87_PW2)] 50 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  X86_STEPS_TAC SI87_RIT_EXEC (51--52) THEN
  YMM_GHOST_TAC `s52:x86state` ["YMM4","ymm4_52"] THEN
  X86_STEPS_TAC SI87_RIT_EXEC (53--54) THEN
  R87_CALL_TAC "H_CHK2" [`rsp0:int64`; `pc:num`; R87_CT0] 55 THEN
  X86_STEPS_TAC SI87_RIT_EXEC (56--56) THEN
  SI_RCONST_TAC "mldsa87_signature_internal" ["mldsa87_signature_internal_const3"] ["YMM5"]
    56 0x2ebf THEN
  X86_STEPS_TAC SI87_RIT_EXEC (57--59);;

(*** the sum, once both checks passed, and the back edge: steps 60 to 69 ***)

let R87_PART3_TAC =
  SI_PASS_TAC `ok2:bool` THEN
  X86_STEPS_TAC SI87_RIT_EXEC (60--61) THEN
  R87_CALL_TAC "H_ADD" [R87_B; `rsp0:int64`; `pc:num`; R87_CT0; R87_R0] 62 THEN
  X86_STEPS_TAC SI87_RIT_EXEC (63--69) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP R87_TEST (ASSUME `j < 8`)]) THEN
  ASM_CASES_TAC `j + 1 < 8` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(SI_WORD_ADD_TAC THEN NO_TAC) THEN TRY(SI_XMM_PRE_TAC THEN NO_TAC) THEN
  SI_END_TAC 1471;;

let SI87_RIT = prove
 (SI87_RIT_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [SI87_ETA56,"H_ETA"; SI87_PWM57,"H_PWM1"; SI87_SUB58,"H_SUB"; SI87_RED59,"H_RED1";
    SI87_CHK60,"H_CHK1"; SI87_T0U61,"H_T0U"; SI87_PWM62,"H_PWM2"; SI87_RED63,"H_RED2";
    SI87_CHK64,"H_CHK2"; SI87_ADD65,"H_ADD";
    MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"] THEN
  CONCRETIZE_F_EVENTS_TAC R87_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok1:bool`; `ok2:bool`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `j:num`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst SI87_RIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ORIENT_TAC THEN SI_ALIGNED16_TAC [0x340; 0x740] THEN
  SI_ROW_ALIGNED_TAC 6688 THEN
  FULL_INIT_TAC THEN R87_PART1_TAC THEN
  X86_STEPS_TAC SI87_RIT_EXEC (29--30) THEN SI_DECIDE_TAC `ok1:bool` THEN
  ASM_CASES_TAC `ok1:bool` THENL [ALL_TAC; SI_FAIL_TAC 1471 `ok1:bool`] THEN
  R87_PART2_TAC THEN SI_DECIDE_TAC `ok2:bool` THEN
  ASM_CASES_TAC `ok2:bool` THENL [ALL_TAC; SI_FAIL_TAC 1471 `ok2:bool`] THEN
  R87_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass (RPRE), from the exit of the loop over z (+0x27ce), where the code   *)
(* zeroes the result slot at rsp0 + 0x30 and sets up row 0, as gcc's         *)
(* SIGN87_RPRE: row j of w holds w0_j - c s2_j + c t0_j afterwards          *)
(* (mld_sign_hint_x), the rows after the first m are unchanged. After a     *)
(* row, XMM4 and XMM5 are as RIT leaves them.                                *)
(* ------------------------------------------------------------------------- *)

let RP87_R0 = R87_R0;;
let RP87_CT0 = R87_CT0;;
let RP87_HX = list_mk_comb(`mld_sign_hint_x 8 mld_poly_decompose_lo_32`,
  [`w:num->int32`; SI87_S2H; SI87_T0H; `cphat:num->int32`]);;

let SI87_RSTART = layout "mldsa87_signature_internal" + 0x27ce;;

let SI87_RPRE_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@R0@",string_of_term RP87_R0; "@CT0@",string_of_term RP87_CT0;
   "@HX@",string_of_term RP87_HX; "@START@",string_of_int SI87_RSTART]
 "exists f_events.
    forall e m sk skb rsp0 w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\ m <= 8 /\\
      (!j. j < m ==> mld_poly_chknorm (@R0@) (word 261768) = word 0 /\\
                     mld_poly_chknorm (@CT0@) (word 261888) = word 0) /\\
      ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
          [(sk,4896); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @START@) /\\
                read RSP s = rsp0 /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 800) /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 1568) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * i)))) s =
                                 cphat i) /\\
                (!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                (!i. i < 2048 ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                read events s = e)
           (\\s. read RIP s =
                (if m < 8 then word (pc + mldsa87_signature_internal_loop55)
                 else word (pc + mldsa87_signature_internal_loop55_exit1)) /\\
                read RSP s = rsp0 /\\
                read RAX s = word m /\\ read R14 s = word (2 + 96 * m) /\\
                read R15 s = word (12 + 416 * m) /\\
                read RBX s = word_add rsp0 (word (6688 + 1024 * m)) /\\
                read (memory :> bytes32 (word_add rsp0 (word 48))) s = word 0 /\\
                (0 < m ==> read XMM4 s = word 0 /\\
                           read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f) /\\
                (!i. i < 256 * m ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * i)))) s =
                                     @HX@ i) /\\
                (!i. 256 * m <= i /\\ i < 2048
                     ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * i)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sk rsp0 pc /\\
                   memaccess_inbounds e2
                    [sk,4896; word_sub rsp0 (word 1471),16383;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 16),16);
                       memory :> bytes(word_add rsp0 (word 48),4);
                       memory :> bytes(word_add rsp0 (word 56),8);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word 6688),8192)])");;

let SI87_RPRE_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(SI87_RSTART, layout "mldsa87_signature_internal_loop55_exit1")];;

let RP87_INV = parse_term(subst_tokens ["@HX@",string_of_term RP87_HX]
 "\\i s. read RSP s = rsp0 /\\
       read RAX s = word i /\\ read R14 s = word (2 + 96 * i) /\\
       read R15 s = word (12 + 416 * i) /\\
       read RBX s = word_add rsp0 (word (6688 + 1024 * i)) /\\
       read (memory :> bytes32 (word_add rsp0 (word 48))) s = word 0 /\\
       (0 < i ==> read XMM4 s = word 0 /\\
                  read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f) /\\
       read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 800) /\\
       read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 1568) /\\
       (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * k)))) s =
                        cphat k) /\\
       (!k. k < 4896 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
       (!k. k < 256 * i ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * k)))) s =
                            @HX@ k) /\\
       (!k. 256 * i <= k /\\ k < 2048
            ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * k)))) s =
                mld_polyvec_map mld_poly_decompose_lo_32 w k)");;

let RP87_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 8` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`rsp0:int64`; `6688`; `2048`; `mld_poly_decompose_lo_32`;
                `w:num->int32`; `i:num`; `s0:x86state`] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; `s0:x86state`]
             `!k. 256 * i <= k /\ k < 2048
                  ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * k)))) s0 = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 8` THEN ARITH_TAC; STRIP_TAC] THEN
  REMOVE_THEN "H_RIT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI87_RPRE_EXEC,0x0,VM_MC,th)
      [`e:(uarch_event)list`; `T`; `T`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `i:num`;
       `w:num->int32`; `cphat:num->int32`; `pc:num`] 1 THENL
     [REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC [`sk:int64`; `rsp0:int64`; `i:num`; `pc:num`];
      LABEL_TAC "H_RIT" th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI_LOOP_PC (CONJ (ASSUME `i < m`) (ASSUME `m <= 8`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `0 < i + 1`] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let RP87_START_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC SI87_RPRE_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; LT_REFL];;

let SI87_RPRE = prove
 (SI87_RPRE_STMT,
  SI_ASSUME_CALLEE_TAILED_TAC SI87_RIT "H_RIT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sk:int64) (rsp0:int64) (pc:num).
     APPEND (f_ev_back m sk rsp0 pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit sk rsp0 pc i)) (f_ev_front sk rsp0 pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_RPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa87_signature_internal_loop55`
     `if m < 8 then pc + mldsa87_signature_internal_loop55
      else pc + mldsa87_signature_internal_loop55_exit1`
     RP87_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0; LT_REFL] THEN
      RP87_START_TAC THEN SI_DISCHARGE_TAC 1471;
      RP87_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN RP87_START_TAC THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI_DISCHARGE_TAC 1471]);;

(* ------------------------------------------------------------------------- *)
(* s1 in the NTT domain and y, as in the gcc proof (SIGN87_S1H, SIGN87_YK).   *)
(* ------------------------------------------------------------------------- *)

let SI87_S1H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j)))`;;

let SI87_YK = `mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa`;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over z (ZIT), from join13 with i in R12, the    *)
(* offset of s1_i in RCX, the output pointer of the packing (sig + 64 + 640  *)
(* i, plus 3) in R8 and the multiplier constant in R14 (the code saves RCX, *)
(* R8 and R12 at rsp0 + 0x30, 0x38 and 0xb8): s1_i unpacked into z at rsp0  *)
(* + 0xb40 and transformed, its product with the challenge, y_i sampled     *)
(* again (absorbing rho'' || kappa + i, squeezing, unpacking at rsp0 + 0x340 *)
(* and zeroing the state), z_i = c s1_i + y_i reduced, its norm check (ok),  *)
(* and, if it passes, z_i packed into the signature; then back to join13 or, *)
(* after the last, to the setup of the rows (+0x27ce); a failed check goes   *)
(* to join21, which zeroes the result slot before the rejection.             *)
(* ------------------------------------------------------------------------- *)

let Z87_ZI = list_mk_comb(`mld_sign_z`, [SI87_S1H; `cphat:num->int32`; SI87_YK; `i:num`]);;

let SI87_ZNEXT = SI87_RSTART;;

let SI87_ZIT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@ZI@",string_of_term Z87_ZI; "@NEXT@",string_of_int SI87_ZNEXT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e ok sig sk skb rsp0 rhop kappa i cphat pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ i < 7 /\\
          (mld_poly_chknorm (@ZI@) (word 524168) = word 0 <=> ok) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
              [(sig,4627); (sk,4896); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,4627))
              [(sk,4896); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_join13) /\\
                read RSP s = rsp0 /\\ read R12 s = word i /\\ read RCX s = word (2 + 96 * i) /\\
                read R8 s = word_add sig (word (67 + 640 * i)) /\\
                read R14 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 160))) s = word_add rsp0 (word 768) /\\
                read (memory :> bytes16 (word_add rsp0 (word 168))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 768),64)) s = rhop /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * k)))) s =
                                 cphat k) /\\
                (!k. k < 4896 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if ok then (if i + 1 < 7 then word (pc + mldsa87_signature_internal_join13)
                             else word (pc + @NEXT@))
                 else word (pc + mldsa87_signature_internal_join21)) /\\
                read RSP s = rsp0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (ok ==> read R12 s = word (i + 1) /\\ read RCX s = word (2 + 96 * (i + 1)) /\\
                        read R8 s = word_add sig (word (67 + 640 * (i + 1))) /\\
                        read R14 s = word 0x0380200100000000 /\\
                        (!j. j < 640 ==> read (memory :> bytes8 (word_add sig (word (64 + 640 * i + j)))) s =
                                         mld_polyz_pack_19 (@ZI@) j)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok sig sk rsp0 i mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,4627; sk,4896; word_sub rsp0 (word 1471),16383;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,4627; word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                       memory :> bytes(word_add rsp0 (word 48),8);
                       memory :> bytes(word_add rsp0 (word 56),8);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 192),208);
                       memory :> bytes(word_add rsp0 (word 416),66);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word 2880),1024);
                       memory :> bytes(word_add rsp0 (word 4960),680);
                       memory :> bytes(word_add sig (word (64 + 640 * i)),640)])");;

let SI87_ZIT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_join13", SI87_ZNEXT);
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let Z87_TEMPLATE =
 `\(ok:bool) (sig:int64) (sk:int64) (rsp0:int64) (i:num) (mf:int64) (mc:int64) (pc:num).
   if ok then (if i + 1 < 7 then f_ev_mid sig sk rsp0 i mf mc pc else f_ev_last sig sk rsp0 i mf mc pc)
   else f_ev_f sig sk rsp0 i mf mc pc :(uarch_event)list`;;

let Z87_ALLOWED = [`ok:bool`; `sig:int64`; `sk:int64`; `rsp0:int64`; `i:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let Z87_CALL_TAC = SI_GCALL_TAC SI87_ZIT_EXEC Z87_ALLOWED SI_XMM_PRE_TAC;;
let Z87_FCALL_TAC = SI_GFCALL_TAC SI87_ZIT_EXEC Z87_ALLOWED SI_XMM_PRE_TAC;;

let Z87_SLICE_TAC off n st =
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `4896`; off; n; st] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 7` THEN ARITH_TAC; DISCH_TAC];;

let Z87_RCONST_TAC = SI_RCONST_TAC "mldsa87_signature_internal"
  ["mldsa87_signature_internal_const1"; "mldsa87_signature_internal_const2"] ["YMM6"; "YMM7"];;

let Z87_S1I = mk_comb(mk_comb(`mld_poly_of`,SI87_S1H),`i:num`);;
let Z87_PW = list_mk_comb(`mld_poly_pointwise_montgomery`,[Z87_S1I; `cphat:num->int32`]);;
let Z87_CS1 = mk_comb(`mld_poly_invntt_tomont`,Z87_PW);;
let Z87_YI = mk_comb(mk_comb(`mld_poly_of`,SI87_YK),`i:num`);;
let Z87_M = `rhop + 2 EXP 512 * val(word(kappa + i):int16)`;;
let Z87_S = mk_comb(`mld_keccak_absorb_once 136 0x1F 66`,Z87_M);;

let Z87_TEST = SI_TEST_RULE 7;;

(*** steps 1 to 40: z_i and its norm check ***)

let Z87_PART1_TAC =
  X86_STEPS_TAC SI87_ZIT_EXEC (1--6) THEN
  Z87_SLICE_TAC `128 + 96 * i` `96` `s6:x86state` THEN
  Z87_CALL_TAC "H_ETA" [`word_add sk (word (128 + 96 * i)):int64`; `rsp0:int64`; `pc:num`;
                        `\j. (skb:num->byte)((128 + 96 * i) + j)`] 7 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_2` THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (8--9) THEN
  Z87_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))) i`] 10 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (11--12) THEN
  Z87_CALL_TAC "H_PWM" [`rsp0:int64`; `pc:num`; Z87_S1I; `cphat:num->int32`] 13 THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (14--15) THEN
  Z87_FCALL_TAC "H_INV" [`read RDI s`; Z87_PW] 16 THEN
  Z87_CALL_TAC "H_G1A" [`rsp0:int64`; `word_add rsp0 (word 768):int64`; `rhop:num`;
                        `kappa:num`; `i:num`; `pc:num`] 17 THEN
  Z87_CALL_TAC "H_SQZ" [Z87_S; `rsp0:int64`; `pc:num`] 18 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_stream]) THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (19--21) THEN
  Z87_CALL_TAC "H_UZ" [`word_add rsp0 (word 4960):int64`; `rsp0:int64`; `pc:num`;
                       mk_comb(`mld_shake256_stream 66`,Z87_M)] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_poly_uniform_gamma1_19]) THEN
  SIGN_GAMMA_POLY_OF_TAC `mld_poly_uniform_gamma1_19` THEN
  Z87_CALL_TAC "H_ZER" [`rsp0:int64`; `pc:num`] 23 THEN SI_RIP_NORM_TAC THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (24--28) THEN
  Z87_CALL_TAC "H_ADD" [`rsp0:int64`; `pc:num`; Z87_YI; Z87_CS1] 29 THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (30--30) THEN Z87_RCONST_TAC 30 0x2665 THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (31--34) THEN
  Z87_CALL_TAC "H_RED" [`rsp0:int64`; `pc:num`; list_mk_comb(`mld_poly_add`,[Z87_CS1; Z87_YI])] 35 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (36--37) THEN
  Z87_CALL_TAC "H_CHK" [`rsp0:int64`; `pc:num`; Z87_ZI] 38;;

(*** the packing of z_i and the back edge: steps 41 to 52 ***)

let Z87_PART2_TAC =
  SI_PASS_TAC `ok:bool` THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (41--43) THEN
  Z87_CALL_TAC "H_ZP" [`rsp0:int64`; `word_add sig (word (64 + 640 * i)):int64`;
                       `pc:num`; Z87_ZI] 44 THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (45--52) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP Z87_TEST (ASSUME `i < 7`)]) THEN
  ASM_CASES_TAC `i + 1 < 7` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(SI_WORD_ADD_TAC THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[GSYM ADD_ASSOC]) THEN NO_TAC) THEN
  SI_END_TAC 1471;;

let Z87_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI87_ETA48,"H_ETA"; SI87_PWM49,"H_PWM"; SI87_G1A_Z,"H_G1A";
      MP (SPEC_ALL SI87_SQZ_Z) mcs,"H_SQZ"; SI87_UZ_Z,"H_UZ";
      MP (SPEC_ALL SI87_ZER_Z) ms,"H_ZER"; SI87_ADD51,"H_ADD"; SI87_RED52,"H_RED";
      SI87_CHK53,"H_CHK"; SI87_ZP54,"H_ZP";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"]) THEN
  CONCRETIZE_F_EVENTS_TAC Z87_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `sig:int64`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `rhop:num`; `kappa:num`; `i:num`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst SI87_ZIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0; 0x340; 0xb40; 0x740] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `i < 65536` ASSUME_TAC THENL [UNDISCH_TAC `i < 7` THEN ARITH_TAC; ALL_TAC];;

let Z87_FAIL_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME `~ok`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI_END_TAC 1471;;

let SI87_ZIT = prove
 (SI87_ZIT_STMT,
  Z87_SETUP_TAC THEN FULL_INIT_TAC THEN Z87_PART1_TAC THEN
  X86_STEPS_TAC SI87_ZIT_EXEC (39--40) THEN SI_DECIDE_TAC `ok:bool` THEN
  ASM_CASES_TAC `ok:bool` THENL [Z87_PART2_TAC; Z87_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check (ZPRE), from after the NTT of the challenge, where the code    *)
(* sets up i = 0 (the packing pointer from the slot at rsp0 + 0x190), as     *)
(* gcc's SIGN87_ZPRE: z_0 .. z_(m-1) packed into the signature after c~.     *)
(* ------------------------------------------------------------------------- *)

let ZP87_ZV = list_mk_comb(`mld_sign_z`, [SI87_S1H; `cphat:num->int32`; SI87_YK]);;
let ZP87_ZI = mk_comb(ZP87_ZV,`i:num`);;
let ZP87_PACK = mk_comb(`mld_polyvec_pack 640 mld_polyz_pack_19`,
                        mk_comb(`mld_polyvec`,ZP87_ZV));;

let SI87_ZPRE_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@ZI@",string_of_term ZP87_ZI; "@PACK@",string_of_term ZP87_PACK;
   "@NEXT@",string_of_int SI87_ZNEXT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e m sig sk skb rsp0 rhop kappa cphat pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ m <= 7 /\\
          (!i. i < m ==> mld_poly_chknorm (@ZI@) (word 524168) = word 0) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
              [(sig,4627); (sk,4896); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,4627))
              [(sk,4896); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\
                read R14 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 400))) s = word_add sig (word 67) /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 160))) s = word_add rsp0 (word 768) /\\
                read (memory :> bytes16 (word_add rsp0 (word 168))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 768),64)) s = rhop /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * k)))) s =
                                 cphat k) /\\
                (!k. k < 4896 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if m < 7 then word (pc + mldsa87_signature_internal_join13)
                 else word (pc + @NEXT@)) /\\
                read RSP s = rsp0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read R12 s = word m /\\ read RCX s = word (2 + 96 * m) /\\
                read R8 s = word_add sig (word (67 + 640 * m)) /\\
                read R14 s = word 0x0380200100000000 /\\
                (!t. t < 640 * m ==> read (memory :> bytes8 (word_add sig (word (64 + t)))) s =
                                     @PACK@ t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sig sk rsp0 mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,4627; sk,4896; word_sub rsp0 (word 1471),16383;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,4627; word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                       memory :> bytes(word_add rsp0 (word 48),8);
                       memory :> bytes(word_add rsp0 (word 56),8);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 192),208);
                       memory :> bytes(word_add rsp0 (word 416),66);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word 2880),1024);
                       memory :> bytes(word_add rsp0 (word 4960),680);
                       memory :> bytes(word_add sig (word 64),4480)])");;

let SI87_ZPRE_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_after_mldsa_poly_ntt_2", SI87_ZNEXT);
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let ZP87_INV = parse_term(subst_tokens ["@PACK@",string_of_term ZP87_PACK]
 "\\i s. read RSP s = rsp0 /\\
       (read DF s <=> false) /\\
       read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
       read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
       read (memory :> bytes(ea,el)) s = ev /\\
       read R12 s = word i /\\ read RCX s = word (2 + 96 * i) /\\
       read R8 s = word_add sig (word (67 + 640 * i)) /\\
       read R14 s = word 0x0380200100000000 /\\
       read (memory :> bytes64 (word_add rsp0 (word 400))) s = word_add sig (word 67) /\\
       read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add sk (word 128) /\\
       read (memory :> bytes64 (word_add rsp0 (word 160))) s = word_add rsp0 (word 768) /\\
       read (memory :> bytes16 (word_add rsp0 (word 168))) s = word kappa /\\
       read (memory :> bytes (word_add rsp0 (word 768),64)) s = rhop /\\
       (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * k)))) s =
                        cphat k) /\\
       (!k. k < 4896 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
       (!t. t < 640 * i ==> read (memory :> bytes8 (word_add sig (word (64 + t)))) s =
                            @PACK@ t)");;

let ZP87_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 7` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!i. i < m ==> P i`) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FULL_INIT_TAC THEN
  REMOVE_THEN "H_ZIT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI87_ZPRE_EXEC,0x0,VM_MC,th)
      [`e:(uarch_event)list`; `T`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
       `rhop:num`; `kappa:num`; `i:num`; `cphat:num->int32`; `pc:num`] 1 THENL
     [REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC [`sig:int64`; `sk:int64`; `rsp0:int64`; `i:num`; `mf:int64`; `mc:int64`; `pc:num`];
      LABEL_TAC "H_ZIT" th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI_LOOP_PC (CONJ (ASSUME `i < m`) (ASSUME `m <= 7`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let ZP87_START_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC SI87_ZPRE_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0];;

let SI87_ZPRE = prove
 (SI87_ZPRE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SI_ASSUME_CALLEE_TAILED_TAC (MP (SPEC_ALL SI87_ZIT) th) "H_ZIT") THEN
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
              fst SI87_ZPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa87_signature_internal_join13`
     (mk_comb(mk_comb(mk_comb(`COND:bool->num->num->num`,`m < 7`),
        `pc + mldsa87_signature_internal_join13`),
        mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral SI87_ZNEXT)))
     ZP87_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      ZP87_START_TAC THEN SI_DISCHARGE_TAC 1471;
      ZP87_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN ZP87_START_TAC THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI_DISCHARGE_TAC 1471]);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt (CLEAN), from join23 with RBX whose low byte is *)
(* 1 on success and 0 otherwise: the memsets of z (0xb40), the challenge     *)
(* (0x740), w (0x1a20), the packed w1 (0x1620) and the polynomial of y       *)
(* (0x340), the zeroing of XMM4, of the structure of y (0xa0) and of c~      *)
(* (0x200), and the test of BL: to join45 on success, else to the update of  *)
(* the count of the attempts at +0x3166, with XMM4 = 0 for the next one.     *)
(* ------------------------------------------------------------------------- *)

let SI87_NX = layout "mldsa87_signature_internal" + 0x3166;;

let SI87_CLEAN_STMT = parse_term(subst_tokens ["@MC@",image_mc; "@NX@",string_of_int SI87_NX]
 "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ok rsp0 rb0 pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 (rsp0:int64) /\\
          (word_zx (rb0:int64) = (word 0:byte) <=> ~ok) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 8),14920))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + mldsa87_signature_internal_join23) /\\
                    read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read RIP s = (if ok then word (pc + mldsa87_signature_internal_join45)
                                  else word (pc + @NX@)) /\\
                    read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                    read XMM4 s = word 0 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (exists e2. read events s = APPEND e2 e /\\
                       e2 = f_events ok rsp0 mf pc /\\
                       memaccess_inbounds e2
                        [word_sub rsp0 (word 8),14920; word(pc + got_memset),8; ea,el]
                        [word_sub rsp0 (word 8),14920]))
               (MAYCHANGE [RSP; R14] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 8),8);
                           memory :> bytes(word_add rsp0 (word 0xa0),16);
                           memory :> bytes(word_add rsp0 (word 0x200),64);
                           memory :> bytes(word_add rsp0 (word 0x340),1024);
                           memory :> bytes(word_add rsp0 (word 0x740),1024);
                           memory :> bytes(word_add rsp0 (word 0xb40),1024);
                           memory :> bytes(word_add rsp0 (word 0x1620),1024);
                           memory :> bytes(word_add rsp0 (word 0x1a20),8192)])");;

let SI87_CLEAN_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_join23", SI87_NX);
   layout_range "plt_memset"];;

let SI87_CLEAN = prove
 (SI87_CLEAN_STMT,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (rsp0:int64) (mf:int64) (pc:num).
      if ok then f_ev_ok rsp0 mf pc else f_ev_nok rsp0 mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `rsp0:int64`; `rb0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_CLEAN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0xa0; 0x200; 0x210; 0x220; 0x230] THEN
  FULL_INIT_TAC THEN
  SI_RUN_TO_TAC SI87_CLEAN_EXEC "H_MEMSET"
    (ref [`ok:bool`; `rsp0:int64`; `mf:int64`; `pc:num`])
    (layout "mldsa87_signature_internal" + 0x311d) 1 THEN
  YMM_GHOST_TAC `s35:x86state` ["YMM4","ymm4_35"] THEN
  SI_RUN_TO_TAC SI87_CLEAN_EXEC "H_MEMSET"
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
(* The packing of c~ and of the hints (TAIL), from the exit of the loop over *)
(* the rows (loop55_exit1): c~ (64 bytes at rsp0 + 0x200) copied to sig, the *)
(* 83 bytes of the hints zeroed from XMM4 (five 16-byte stores and a 32-bit  *)
(* one that overlaps the last byte of the fifth), and for each row k the     *)
(* unpacking of its w1 (W1U, the nibble mask in XMM5) and its hints (HROW).  *)
(* If the hints fit, the code sets BL to 1 and goes to the cleanup at join23 *)
(* with the hints of mld_pack_hints at sig + 4544; otherwise to the          *)
(* rejection at join22.                                                      *)
(* ------------------------------------------------------------------------- *)

let SI_BYTES128_ZERO_PREFIX = prove
 (`!(a:int64) k (s:x86state).
     read (memory :> bytes128 a) s = word 0 /\ k <= 16
     ==> read (memory :> bytes (a,k)) s = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (a,16)) s = 0` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD_0;
                DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `16 = k + (16 - k)` SUBST1_TAC THENL
   [UNDISCH_TAC `k <= 16` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; ADD_EQ_0] THEN
  SIMP_TAC[]);;

let SI_BYTES32_ZERO = prove
 (`!(a:int64) (s:x86state).
     read (memory :> bytes32 a) s = word 0
     ==> read (memory :> bytes (a,4)) s = 0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD_0;
              DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let T87_MH = `mld_polyvec_make_hint_32 x b`;;

let T87_ZX_SUB = WORD_BLAST `!y:int256. word_zx y:int128 = word_subword y (0,128)`;;
let T87_Y4 = ASSUME `word_subword (ymm4_init:int256) (0,128):int128 = word 0`;;

let SI87_TAIL_STMT = parse_term(subst_tokens ["@MC@",image_mc]
 "exists f_events.
    forall e sig rsp0 rb0 (C:num) (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\
      nonoverlapping (sig,4627) (rsp0,14912) /\\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,4627); (rsp0,14912)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_loop55_exit1) /\\
                read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                read XMM4 s = word 0 /\\
                read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = sig /\\
                read (memory :> bytes64 (word_add rsp0 (word 40))) s = word_add sig (word 4544) /\\
                read (memory :> bytes (word_add rsp0 (word 512),64)) s = C /\\
                (!j. j < 2048 ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * j)))) s = x j) /\\
                (!j. j < 1024 ==> read (memory :> bytes8 (word_add rsp0 (word (5664 + j)))) s = b j) /\\
                read events s = e)
           (\\s. read RIP s =
                (if mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75
                 then word (pc + mldsa87_signature_internal_join23)
                 else word (pc + mldsa87_signature_internal_join22)) /\\
                read RSP s = rsp0 /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75
                 ==> ~(word_zx (read RBX s) = (word 0:byte))) /\\
                read (memory :> bytes (sig,64)) s = C /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75
                 ==> !t. t < 83
                         ==> read (memory :> bytes8 (word_add sig (word (4544 + t)))) s =
                             mld_pack_hints 75 8 (mld_polyvec_make_hint_32 x b) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig rsp0 pc x b /\\
                   memaccess_inbounds e2 [sig,4627; rsp0,14912] [sig,4627; rsp0,14912]))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; RDI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(sig,64);
                       memory :> bytes(word_add sig (word 4544),83);
                       memory :> bytes(word_add rsp0 (word 832),1024)])");;

let SI87_TAIL_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_loop55_exit1", layout "mldsa87_signature_internal" + 0x373e)];;

let T87_TEMPLATE =
 `\(sig:int64) (rsp0:int64) (pc:num) (x:num->int32) (b:num->byte).
   if mld_hint_count (mld_polyvec_make_hint_32 x b) 256 <= 75 then
    (if mld_hint_count (mld_polyvec_make_hint_32 x b) 512 <= 75 then
      (if mld_hint_count (mld_polyvec_make_hint_32 x b) 768 <= 75 then
        (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1024 <= 75 then
          (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1280 <= 75 then
            (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 75 then
              (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1792 <= 75 then
                (if mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75
                 then f_ev_ok sig rsp0 pc x b else f_ev_r7 sig rsp0 pc x b)
               else f_ev_r6 sig rsp0 pc x b)
             else f_ev_r5 sig rsp0 pc x b)
           else f_ev_r4 sig rsp0 pc x b)
         else f_ev_r3 sig rsp0 pc x b)
       else f_ev_r2 sig rsp0 pc x b)
     else f_ev_r1 sig rsp0 pc x b)
   else f_ev_r0 sig rsp0 pc x b :(uarch_event)list`;;

let T87_CALL_TAC = SI_GCALL_TAC SI87_TAIL_EXEC
  [`sig:int64`; `rsp0:int64`; `pc:num`; `x:num->int32`; `b:num->byte`] SI_XMM_PRE_TAC;;

let T87_B_SLICE_TAC k n =
  let ib = 5664 + 128 * k and wb = 128 * k in
  let st = mk_var("s"^string_of_int n,`:x86state`) in
  SUBGOAL_THEN (vsubst [st,`s:x86state`] (parse_term(Printf.sprintf
    "!j. j < 128 ==> read (memory :> bytes8 (word_add rsp0 (word (%d + j)))) s = b (%d + j)" ib wb)))
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" wb)) o check (fun th ->
      is_forall(concl th) && can (term_match [] `!j. j < 1024 ==> read (memory :> bytes8 (word_add rsp0 (word (5664 + j)))) s = b j`) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "5664 + %d + j = %d + j" wb ib))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `j < 128` THEN ARITH_TAC;
    ALL_TAC];;

let T87_X_SLICE_TAC k n =
  let w = 6688 + 1024 * k and p0 = 256 * k in
  let st = mk_var("s"^string_of_int n,`:x86state`) in
  SUBGOAL_THEN (vsubst [st,`s:x86state`] (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * i)))) s = x (%d + i)" w p0)))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" p0)) o check (fun th ->
      is_forall(concl th) && can (term_match [] `!j. j < 2048 ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * j)))) s = x j`) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "6688 + 4 * (%d + i) = %d + 4 * i" p0 w))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC];;

let T87_CNT_TM p = subst [mk_small_numeral p,`p:num`] `mld_hint_count (mld_polyvec_make_hint_32 x b) p <= 75`;;

let T87_SPLIT_TAC p =
  let c = T87_CNT_TM p in
  ASM_CASES_TAC c THEN
  FIRST_ASSUM(fun th -> if concl th = c || concl th = mk_neg c
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `RAX` (concl th)
                                then STRIP_ASSUME_TAC th else NO_TAC));;

let T87_FAIL_TAC p =
  SUBGOAL_THEN (mk_neg(T87_CNT_TM 2048)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; mk_small_numeral p; `2048`] MLD_HINT_COUNT_MONO) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(T87_CNT_TM p))) THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* row k > 0: xor ecx (and a nop for k > 1), W1U, xor ecx; jmp, HROW *)
let T87_ROW_TAC k n =
  let p1 = 256 * (k + 1) in
  let d = if k = 1 then 0 else 1 in
  X86_STEPS_TAC SI87_TAIL_EXEC (n--(n+d)) THEN T87_B_SLICE_TAC k (n+d) THEN
  T87_CALL_TAC ("H_W1U"^string_of_int k)
   [`rsp0:int64`; `pc:num`; parse_term(Printf.sprintf "\\t. (b:num->byte) (%d + t)" (128 * k))] (n+d+1) THEN
  X86_STEPS_TAC SI87_TAIL_EXEC ((n+d+2)--(n+d+3)) THEN T87_X_SLICE_TAC k (n+d+3) THEN
  T87_CALL_TAC ("H_HROW"^string_of_int k)
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `rsp0:int64`; `pc:num`] (n+d+4) THEN
  T87_SPLIT_TAC p1 THENL [ALL_TAC; T87_FAIL_TAC p1];;

let T87_PACK_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `t = 75 \/ t = 76 \/ t = 77 \/ t = 78 \/ t = 79 \/ t = 80 \/ t = 81 \/ t = 82`
      MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`t < 83`; `~(t < 75)`] THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]];;

let SI87_TAIL = prove
 (SI87_TAIL_STMT,
  (MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [SI87_W1U66,"H_W1U0"; SI87_W1U68,"H_W1U1"; SI87_W1U69,"H_W1U2"; SI87_W1U70,"H_W1U3";
    SI87_W1U71,"H_W1U4"; SI87_W1U72,"H_W1U5"; SI87_W1U73,"H_W1U6"; SI87_W1U74,"H_W1U7";
    SI87_HROW0,"H_HROW0"; SI87_HROW1,"H_HROW1"; SI87_HROW2,"H_HROW2"; SI87_HROW3,"H_HROW3";
    SI87_HROW4,"H_HROW4"; SI87_HROW5,"H_HROW5"; SI87_HROW6,"H_HROW6"; SI87_HROW7,"H_HROW7"] THEN
  CONCRETIZE_F_EVENTS_TAC T87_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `rsp0:int64`; `rb0:int64`; `C:num`;
                       `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES; fst SI87_TAIL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x200; 0x210; 0x220; 0x230; 0x340] THEN
  MAP_EVERY (fun r -> GHOST_INTRO_TAC (mk_var("ymm"^string_of_int r^"_init",`:int256`))
                       (mk_comb(`read:(x86state,int256)component->x86state->int256`,
                                mk_const("YMM"^string_of_int r,[]))))
    [0;1;2;3;4] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `word_subword (ymm4_init:int256) (0,128):int128 = word 0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `read XMM4 s0 = word 0`)) THEN
    REWRITE_TAC[XMM4; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[T87_ZX_SUB];
    ALL_TAC]) THEN
  (MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add rsp0 (word 512):int64`; `64`; `C:num`; mk_small_numeral n; `s0:x86state`]
             SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1;2;3]) THEN
  (X86_STEPS_TAC SI87_TAIL_EXEC (1--15) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; DIV_1; T87_Y4]) THEN
   FIRST_ASSUM(fun th ->
     if can (term_match [] `read (memory :> bytes128 (word_add sig (word 4608))) s15 = x`) (concl th)
     then MP_TAC(SPECL [`word_add sig (word 4608):int64`; `15`; `s15:x86state`] SI_BYTES128_ZERO_PREFIX)
     else NO_TAC) THEN
   ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN
   X86_STEPS_TAC SI87_TAIL_EXEC (16--18) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[T87_Y4])) THEN
  (SUBGOAL_THEN `C < 2 EXP (8 * 64)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (word_add rsp0 (word 512),64)) s0 = C`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sig:int64`; `C:num`; `4`; `s18:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 2 EXP (128 * 4) = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `C < 2 EXP (8 * 64)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC) THEN
  (MP_TAC(SPECL [`word_add sig (word 4544):int64`; `0`; `4`; `s18:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_0] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes32 (word_add sig (word 4623))) s18 = word 0`) (concl th)
    then ASSUME_TAC(MATCH_MP SI_BYTES32_ZERO th) else NO_TAC) THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add sig (word 4544),83)) s18 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `83 = 64 + (15 + 4)`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (sig:int64) (word 4544)) (word 79) =
                           word_add sig (word 4623)`;
                WORD_RULE `word_add (word_add (sig:int64) (word 4544)) (word 64) =
                           word_add sig (word 4608)`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word_add sig (word 4544),83)) s18 = 0`) (concl th)
    then ASSUME_TAC(GEN `t:num`
      (REWRITE_RULE[GSYM(INST [T87_MH,`h:num->bool`] (CONJUNCT1 mld_hint_index));
                    WORD_RULE `word_add (word_add sig (word 4544)) (word t) = word_add sig (word (4544 + t))`]
        (SPEC `t:num` (MATCH_MP SIGN_BYTES8_ZERO th))))
    else NO_TAC)) THEN
  (T87_B_SLICE_TAC 0 18 THEN
  T87_CALL_TAC "H_W1U0" [`rsp0:int64`; `pc:num`; `\t. (b:num->byte) (0 + t)`] 19) THEN
  (X86_STEPS_TAC SI87_TAIL_EXEC (20--22) THEN T87_X_SLICE_TAC 0 22 THEN
  ASSUME_TAC(INST [T87_MH,`h:num->bool`] (CONJUNCT1 mld_hint_count)) THEN
  ASSUME_TAC(ARITH_RULE `0 <= 75`) THEN
  T87_CALL_TAC "H_HROW0" [`x:num->int32`; `b:num->byte`; `sig:int64`; `rsp0:int64`; `pc:num`] 23) THEN
  (T87_SPLIT_TAC 256 THENL [ALL_TAC; T87_FAIL_TAC 256]) THEN
  (T87_ROW_TAC 1 24) THEN
  (T87_ROW_TAC 2 29) THEN
  (T87_ROW_TAC 3 35) THEN
  (T87_ROW_TAC 4 41) THEN
  (T87_ROW_TAC 5 47) THEN
  (T87_ROW_TAC 6 53) THEN
  (T87_ROW_TAC 7 59) THEN
  (X86_STEPS_TAC SI87_TAIL_EXEC (65--66) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SI_BL_NZ]) THEN
  (CONJ_TAC THENL [T87_PACK_TAC; DISCHARGE_SAFETY_PROPERTY_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Column j of the product of the matrix with y (YCOL j, j = 0 .. 6), from   *)
(* join4 to join3, with j in R15 (saved at rsp0 + 0x38): y_j sampled         *)
(* (absorbing rho'' || kappa + j, squeezing, unpacking at rsp0 + 0x340,      *)
(* zeroing) and transformed, then for each row r the entry A_rj sampled by   *)
(* mldsa_poly_uniform from rho || j || r at rsp0 + 0xc0 and multiplied by    *)
(* it: for j = 0 into row r of w at rsp0 + 0x1a20 + 1024 r, for j > 0 into   *)
(* the scratch polynomial at rsp0 + 0xf40 and added to row r. Row r is then  *)
(* mld_lazy_acc rho r YHAT j, YHAT being y in the NTT domain. The code       *)
(* zeroes XMM4 (which the sampling of the next y_j needs) and loads the      *)
(* constants of the reduction that follows the loop into XMM5 and XMM6       *)
(* before the last row. The lemma is made for each j, with j a numeral,      *)
(* from one generator.                                                       *)
(* ------------------------------------------------------------------------- *)

let SI87_YHAT = `mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa)`;;

let yc87_row r n =
  Printf.sprintf
   "(!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * k)))) s =
                     mld_lazy_acc rho %d (%s) %d k)"
   (6688 + 1024 * r) r (string_of_term SI87_YHAT) n;;

let yc87_rows n = String.concat " /\\\n " (map (fun r -> yc87_row r n) (0--7));;

let YC87_STMT j = parse_term(subst_tokens
  ["@MC@",image_mc;
   "@PRE@",(if j = 0 then "" else yc87_rows (j - 1) ^ " /\\");
   "@POST@",yc87_rows j;
   "@J@",string_of_int j]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 rho rhop kappa pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ mld_matrix_terminates 8 7 rho /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_join4) /\\
                read RSP s = rsp0 /\\ read R15 s = word @J@ /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 160))) s = word_add rsp0 (word 768) /\\
                read (memory :> bytes16 (word_add rsp0 (word 168))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 768),64)) s = rhop /\\
                read (memory :> bytes (word_add rsp0 (word 192),32)) s = rho /\\
                @PRE@
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa87_signature_internal_join3) /\\
                read RSP s = rsp0 /\\ read R15 s = word @J@ /\\
                read RBX s = word 0x0380200100000000 /\\
                read XMM4 s = word 0 /\\
                read XMM5 s = word 0x00400000004000000040000000400000 /\\
                read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 160))) s = word_add rsp0 (word 768) /\\
                read (memory :> bytes16 (word_add rsp0 (word 168))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 768),64)) s = rhop /\\
                read (memory :> bytes (word_add rsp0 (word 192),32)) s = rho /\\
                @POST@ /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rho mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),16383;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256]
                    [word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 56),4);
                       memory :> bytes(word_add rsp0 (word 224),2);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word 1856),680);
                       memory :> bytes(word_add rsp0 (word 2880),208);
                       memory :> bytes(word_add rsp0 (word 3904),1024);
                       memory :> bytes(word_add rsp0 (word 4960),66);
                       memory :> bytes(word_add rsp0 (word 6688),8192)])");;

let SI87_YCOL_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_join4", layout "mldsa87_signature_internal_join10");
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let YC87_ALLOWED = [`rsp0:int64`; `rho:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let YC87_CALL_TAC = SI_GCALL_TAC SI87_YCOL_EXEC YC87_ALLOWED SI_XMM_PRE_TAC;;
let YC87_FCALL_TAC = SI_GFCALL_TAC SI87_YCOL_EXEC YC87_ALLOWED SI_XMM_PRE_TAC;;

let YC87_RCONST_TAC = SI_RCONST_TAC "mldsa87_signature_internal"
  ["mldsa87_signature_internal_const1"; "mldsa87_signature_internal_const2"] ["YMM5"; "YMM6"];;

let YC87_Y = `mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa`;;

(*** y_j and its NTT: steps 1 to 16 ***)

let YC87_HEAD_TAC j =
  let jt = mk_small_numeral j in
  let m = subst [jt,`j:num`] `rhop + 2 EXP 512 * val(word(kappa + j):int16)` in
  YC87_CALL_TAC "H_G1A" [`rsp0:int64`; `word_add rsp0 (word 768):int64`; `rhop:num`;
                         `kappa:num`; jt; `pc:num`] 1 THEN
  YC87_CALL_TAC "H_SQZ" [mk_comb(`mld_keccak_absorb_once 136 0x1F 66`,m); `rsp0:int64`; `pc:num`] 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_stream]) THEN
  X86_STEPS_TAC SI87_YCOL_EXEC (3--6) THEN
  YC87_CALL_TAC "H_UZ" [`word_add rsp0 (word 1856):int64`; `rsp0:int64`; `pc:num`;
                        mk_comb(`mld_shake256_stream 66`,m)] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_poly_uniform_gamma1_19]) THEN
  SIGN_GAMMA_POLY_OF_TAC `mld_poly_uniform_gamma1_19` THEN
  YC87_CALL_TAC "H_ZER" [`rsp0:int64`; `pc:num`] 8 THEN SI_RIP_NORM_TAC THEN
  X86_STEPS_TAC SI87_YCOL_EXEC (9--11) THEN
  YC87_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,YC87_Y),jt)] 12 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI87_YCOL_EXEC (13--13) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R15 s = x`) (concl th)
                           then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
  X86_STEPS_TAC SI87_YCOL_EXEC (14--16);;

(*** row r of a column: the seed rho || j || r, the sampling of the entry   ***)
(*** (the CALL at step n), its product with y_j and, for j > 0, the sum     ***)

let YC87_SEED_TAC j r st =
  if j = 0 then
    MP_TAC(SPECL [`word_add rsp0 (word 192):int64`; `rho:num`; mk_small_numeral r; `0`; st]
                 SI_SEED16) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (x:int64) (word 192)) (word 32) =
                           word_add x (word 224)`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC
  else
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes8 a) s = x`) (concl th)
      then CONV_RULE(RAND_CONV(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV)) th
      else th) THEN
    MP_TAC(SPECL [`word_add rsp0 (word 192):int64`; `rho:num`; mk_small_numeral r;
                  mk_small_numeral j; st] LAZY_SEED) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (x:int64) (word 192)) (word 32) =
                           word_add x (word 224)`;
                WORD_RULE `word_add (word_add (x:int64) (word 192)) (word 33) =
                           word_add x (word 225)`] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let YC87_PU_TAC j r n =
  let jt = mk_small_numeral j and rt = mk_small_numeral r in
  let sd = list_mk_comb(`mld_matrix_seed`,[`rho:num`; rt; jt]) in
  let st = mk_var("s"^string_of_int (n - 1),`:x86state`) in
  YC87_SEED_TAC j r st THEN
  MLD_LAZY_TERM_TAC (mk_comb(`mld_rej_uniform_terminates`,mk_comb(`mld_shake128_stream 34`,sd))) THEN
  YC87_FCALL_TAC "H_PU" [`read RDI s`; `read RSI s`; sd] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]);;

(* the zeroing of XMM4 at step n, with its old value ghosted first *)
let YC87_PXOR_TAC n =
  YMM_GHOST_TAC (mk_var("s"^string_of_int (n - 1),`:x86state`))
    [("YMM4","ymm4_"^string_of_int (n - 1))] THEN
  X86_STEPS_TAC SI87_YCOL_EXEC (n--n);;

let YC87_TAC j =
  let jt = mk_small_numeral j in
  let yh = mk_comb(mk_comb(`mld_poly_of`,SI87_YHAT),jt) in
  let entry r = list_mk_comb(`mld_matrix_entry`,[`rho:num`; mk_small_numeral r; jt]) in
  let pwm r = list_mk_comb(`mld_poly_pointwise_montgomery`,[entry r; yh]) in
  let acc r n = list_mk_comb(`mld_lazy_acc rho`,[mk_small_numeral r; SI87_YHAT; mk_small_numeral n]) in
  let acc_eq r =
    if j = 0 then GSYM(CONJUNCT1 mld_lazy_acc)
    else SYM(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
              (SPECL [`rho:num`; mk_small_numeral r; SI87_YHAT; mk_small_numeral (j - 1)]
                     MLD_LAZY_ACC_ADD1)) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     ([SI87_G1A_Y,"H_G1A"; MP (SPEC_ALL SI87_SQZ_Y) mcs,"H_SQZ"; SI87_UZ_Y,"H_UZ";
       MP (SPEC_ALL SI87_ZER_Y) ms,"H_ZER";
       MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
       MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th,
       "H_PU"] @
      (if j = 0 then [SI87_PWM18,"H_PWM0"; SI87_PWM19,"H_PWM1"; SI87_PWM20,"H_PWM2";
                      SI87_PWM21,"H_PWM3"; SI87_PWM22,"H_PWM4"; SI87_PWM23,"H_PWM5";
                      SI87_PWM24,"H_PWM6"; SI87_PWM25,"H_PWM7"]
       else [SI87_PWM2,"H_PWM0"; SI87_PWM4,"H_PWM1"; SI87_PWM6,"H_PWM2"; SI87_PWM8,"H_PWM3";
             SI87_PWM10,"H_PWM4"; SI87_PWM12,"H_PWM5"; SI87_PWM14,"H_PWM6"; SI87_PWM16,"H_PWM7";
             SI87_ADD3,"H_ADD0"; SI87_ADD5,"H_ADD1"; SI87_ADD7,"H_ADD2"; SI87_ADD9,"H_ADD3";
             SI87_ADD11,"H_ADD4"; SI87_ADD13,"H_ADD5"; SI87_ADD15,"H_ADD6"; SI87_ADD17,"H_ADD7"]))) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rho:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_col rsp0 rho mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rho:num`; `rhop:num`;
                       `kappa:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mld_matrix_terminates]) THEN
  SI_ALIGNED16_TAC [0; 0x340; 0xf40; 0x1a20; 0x1e20; 0x2220; 0x2620; 0x2a20; 0x2e20;
                    0x3220; 0x3620] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  FULL_INIT_TAC THEN YC87_HEAD_TAC j THEN
  (if j = 0 then
    MAP_EVERY (fun r ->
      let n = 17 + 8 * r in
      X86_STEPS_TAC SI87_YCOL_EXEC (n--(n+3)) THEN YC87_PU_TAC j r (n+4) THEN
      (if r = 7 then
         X86_STEPS_TAC SI87_YCOL_EXEC ((n+5)--(n+5)) THEN YC87_PXOR_TAC (n+6) THEN
         YC87_RCONST_TAC (n+6) 0x1311 THEN
         X86_STEPS_TAC SI87_YCOL_EXEC ((n+7)--(n+9)) THEN
         YC87_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+10)
       else
         X86_STEPS_TAC SI87_YCOL_EXEC ((n+5)--(n+6)) THEN
         YC87_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+7)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[acc_eq r])) (0--7) THEN
    X86_STEPS_TAC SI87_YCOL_EXEC (84--84)
   else
    MAP_EVERY (fun r ->
      let n = 17 + 12 * r in
      X86_STEPS_TAC SI87_YCOL_EXEC (n--(n+4)) THEN YC87_PU_TAC j r (n+5) THEN
      X86_STEPS_TAC SI87_YCOL_EXEC ((n+6)--(n+7)) THEN
      YC87_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+8) THEN
      (if r = 7 then
         X86_STEPS_TAC SI87_YCOL_EXEC ((n+9)--(n+9)) THEN YC87_PXOR_TAC (n+10) THEN
         YC87_RCONST_TAC (n+10) 0xdf2 THEN
         X86_STEPS_TAC SI87_YCOL_EXEC ((n+11)--(n+13))
       else X86_STEPS_TAC SI87_YCOL_EXEC ((n+9)--(n+10))) THEN
      YC87_CALL_TAC ("H_ADD"^string_of_int r) [`rsp0:int64`; `pc:num`; pwm r; acc r (j - 1)]
        (if r = 7 then n+14 else n+11) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[acc_eq r])) (0--7) THEN
    X86_STEPS_TAC SI87_YCOL_EXEC (116--116)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(SI_XMM_PRE_TAC THEN NO_TAC) THEN
  SI_END_TAC 1471;;

let SI87_YCOL0 = prove(YC87_STMT 0, YC87_TAC 0);;
let SI87_YCOL1 = prove(YC87_STMT 1, YC87_TAC 1);;
let SI87_YCOL2 = prove(YC87_STMT 2, YC87_TAC 2);;
let SI87_YCOL3 = prove(YC87_STMT 3, YC87_TAC 3);;
let SI87_YCOL4 = prove(YC87_STMT 4, YC87_TAC 4);;
let SI87_YCOL5 = prove(YC87_STMT 5, YC87_TAC 5);;
let SI87_YCOL6 = prove(YC87_STMT 6, YC87_TAC 6);;

(* ------------------------------------------------------------------------- *)
(* After the product with the matrix (HPOST), from join10 to after the NTT  *)
(* of the challenge: the seed buffer zeroed (from XMM4), the rows of w      *)
(* reduced (XMM5 and XMM6 as YCOL 6 left them), transformed back and made   *)
(* nonnegative, which MLD_LAZY_SIGN_W turns into w = A y of the model; the  *)
(* rolled loop over the rows (DW1R, the mask in XMM6) decomposes w in place *)
(* into w0 and packs w1 at rsp0 + 0x1620; c~ = H(mu || w1) inlined (C2,     *)
(* the state at rsp0 + 0x740 zeroed from XMM5, which also leaves the        *)
(* multiplier constant of the loop over z in R14), c~ copied to rsp0 + 0x200 *)
(* and the state zeroed; the challenge at rsp0 + 0x740 and its NTT.         *)
(* ------------------------------------------------------------------------- *)

let SI87_A = `mld_polyvec_matrix_expand 7 rho`;;
let SI87_W = list_mk_comb(`mld_sign_w 7`,[SI87_A; YC87_Y]);;
let SI87_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128`,SI87_W);;
let SI87_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,[SI87_W1; `1024`]));;
let SI87_CT = mk_comb(`mld_sign_ctilde 8 128 mu`,SI87_W1);;
let SI87_C2P = mk_binop `(+):num->num->num` `mu:num`
  (mk_binop `( * ):num->num->num` `2 EXP 512` SI87_W1NUM);;
let SI87_C2NUM = subst [SI87_C2P,`p:num`]
  `num_of_bytelist (list_of_seq (mld_shake256_byte 1088 p) 64)`;;

let SI87_HPOST_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@PRE@",yc87_rows 6; "@W@",string_of_term SI87_W;
   "@W1@",string_of_term SI87_W1; "@CT@",string_of_term SI87_CT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 rho rhop kappa mu C pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ mld_matrix_terminates 8 7 rho /\\
          num_of_bytelist(list_of_seq (@CT@) 64) = C /\\
          mld_poly_challenge_terminates 60 64 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_join10) /\\
                read RSP s = rsp0 /\\ read RBX s = word 0x0380200100000000 /\\
                read XMM4 s = word 0 /\\
                read XMM5 s = word 0x00400000004000000040000000400000 /\\
                read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word 704),64)) s = mu /\\
                @PRE@ /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa87_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\ read R14 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (!i. i < 2048 ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 (@W@) i) /\\
                (!j. j < 1024 ==> read (memory :> bytes8 (word_add rsp0 (word (5664 + j)))) s =
                                  (@W1@) j) /\\
                read (memory :> bytes (word_add rsp0 (word 512),64)) s = C /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * k)))) s =
                                 mld_poly_ntt (mld_poly_challenge 60 64 C) k) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 C mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),16383;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 192),64);
                       memory :> bytes(word_add rsp0 (word 512),64);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word 1856),1024);
                       memory :> bytes(word_add rsp0 (word 5664),1024);
                       memory :> bytes(word_add rsp0 (word 6688),8192)])");;

let SI87_HPOST_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_join10", layout "mldsa87_signature_internal_after_mldsa_poly_ntt_2")];;

let HP87_ALLOWED = [`rsp0:int64`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let HP87_CALL_TAC = SI_GCALL_TAC SI87_HPOST_EXEC HP87_ALLOWED SI_XMM_PRE_TAC;;
let HP87_FCALL_TAC = SI_GFCALL_TAC SI87_HPOST_EXEC HP87_ALLOWED SI_XMM_PRE_TAC;;

let HP87_V = `mld_polyvec (\i. mld_lazy_acc rho i
                (mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa)) 6)`;;
let HP87_RV = mk_comb(`mld_polyvec_map mld_poly_reduce`,HP87_V);;
let HP87_IV = mk_comb(`mld_polyvec_map mld_poly_invntt_tomont`,HP87_RV);;
let HP87_CV = mk_comb(`mld_polyvec_map mld_poly_caddq`,HP87_IV);;
let HP87_ROW v r = mk_comb(mk_comb(`mld_poly_of`,v),mk_small_numeral r);;

(* row r of the lazy sums as row r of the vector HP87_V *)
let HP87_V_TAC r =
  let off = 6688 + 1024 * r in
  FIRST_X_ASSUM(fun th ->
    let pat = subst [mk_small_numeral off,`d:num`; mk_small_numeral r,`r:num`]
     `!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (d + 4 * k)))) s =
                      mld_lazy_acc rho r YH 6 k` in
    if can (term_match [] pat) (concl th) then
      ASSUME_TAC(MATCH_MP (BETA_RULE(ISPECL
        [`\i. mld_lazy_acc rho i (mld_polyvec_map mld_poly_ntt
                (mld_sign_y mld_poly_uniform_gamma1_19 rhop kappa)) 6`;
         mk_small_numeral r] SI_POLYVEC_POLY_OF)) th)
    else NO_TAC);;

let HP87_LAZY_W_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
   `!i. i < 2048
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * i)))) s =
            mld_polyvec_map mld_poly_caddq x i`) (concl th))) THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
   (SPECL [`8`; `7`; `rho:num`; YC87_Y] MLD_LAZY_SIGN_W)) THEN
  REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND; ASSUME `mld_matrix_terminates 8 7 rho`] THEN
  DISCH_THEN(fun th -> SIMP_TAC[th]) THEN DISCH_TAC;;

let HP87_YVEC = prove
 (mk_eq(list_mk_comb(`mld_polyvec_matrix_yvec_lazy 7 rho`,[YC87_Y]),HP87_IV),
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy] THEN CONV_TAC NUM_REDUCE_CONV);;

let HP87_ROWS_PAT32 =
 `!r. r < 8 ==> !k. k < 256
      ==> read (memory :> bytes32 (word_add B (word ((off + 1024 * r) + 4 * k)))) s =
          mld_poly_of V r k`;;

(*** the rows of w: steps 1 to 80 ***)

let HP87_PART1_TAC =
  X86_STEPS_TAC SI87_HPOST_EXEC (1--7) THEN
  MAP_EVERY HP87_V_TAC (0--7) THEN
  MAP_EVERY (fun r ->
    let n = if r = 0 then 8 else 9 + 3 * r in
    (if r = 1 then X86_STEPS_TAC SI87_HPOST_EXEC (9--11)
     else if r > 1 then X86_STEPS_TAC SI87_HPOST_EXEC ((n-2)--(n-1)) else ALL_TAC) THEN
    HP87_CALL_TAC ("H_RED"^string_of_int r) [`rsp0:int64`; `pc:num`; HP87_ROW HP87_V r] n THEN
    SI_MAP_POLY_OF_TAC `mld_poly_reduce`) (0--7) THEN
  MAP_EVERY (fun r ->
    X86_STEPS_TAC SI87_HPOST_EXEC ((31 + 3 * r)--(32 + 3 * r)) THEN
    HP87_FCALL_TAC "H_INV" [`read RDI s`; HP87_ROW HP87_RV r] (33 + 3 * r) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_invntt_tomont`) (0--7) THEN
  X86_STEPS_TAC SI87_HPOST_EXEC (55--56) THEN
  HP87_CALL_TAC "H_CQ0" [`rsp0:int64`; `pc:num`; HP87_ROW HP87_IV 0] 57 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq` THEN
  X86_STEPS_TAC SI87_HPOST_EXEC (58--58) THEN
  YMM_GHOST_TAC `s58:x86state` ["YMM5","ymm5_58"] THEN
  X86_STEPS_TAC SI87_HPOST_EXEC (59--59) THEN
  SI_RCONST_TAC "mldsa87_signature_internal" ["mldsa87_signature_internal_const4"] ["YMM6"]
    59 0x197e THEN
  X86_STEPS_TAC SI87_HPOST_EXEC (60--61) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_REFL]) THEN
  MAP_EVERY (fun r ->
    let n = 59 + 3 * r in
    (if r > 1 then X86_STEPS_TAC SI87_HPOST_EXEC ((n-2)--(n-1)) else ALL_TAC) THEN
    HP87_CALL_TAC ("H_CQ"^string_of_int r) [`rsp0:int64`; `pc:num`; HP87_ROW HP87_IV r] n THEN
    SI_MAP_POLY_OF_TAC `mld_poly_caddq`) (1--7);;

(*** w as w = A y, its decomposition and the packing of w1 (DW1R): step 81 ***)

let HP87_PART2_TAC =
  SI_ROWS_TAC `rsp0:int64` 6688 `s80:x86state` (subst [HP87_CV,`V:num->int32`] HP87_ROWS_PAT32) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
           (MATCH_MP SI_JOIN_VECN32 (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] th)))
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM HP87_YVEC]) THEN
  HP87_LAZY_W_TAC THEN
  HP87_CALL_TAC "H_DW1R" [`rsp0:int64`; `pc:num`; SI87_W] 81;;

(*** c~ = H(mu || w1), its copy, the zeroing of the state, the challenge  ***)
(*** and its NTT: steps 82 to 124                                          ***)

let HP87_PART3_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!t. t < 1024 ==> read (memory :> bytes8
         (word_add rsp0 (word (5664 + t)))) s = f t`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX] (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  HP87_CALL_TAC "H_C2" [`rsp0:int64`; `pc:num`; `mu:num`; SI87_W1NUM] 82 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> wbytes (word_add rsp0 (word 1856))) s = x`)
           (concl th)
    then MAP_EVERY (fun k ->
           MP_TAC(SPECL [`word_add rsp0 (word 1856):int64`; rhs(concl th);
                         mk_small_numeral k; `s82:x86state`] READ_MEMORY_BYTES128_OF_WBYTES) THEN
           ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC th; ARITH_TAC]; ALL_TAC] THEN
           MP_TAC(SPECL [`1088`; SI87_C2P; mk_small_numeral k] VM_TR_CHUNK) THEN
           ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
           CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
           REWRITE_TAC[WORD_ADD_0; EXP; DIV_1] THEN DISCH_TAC) [0;1;2;3]
    else NO_TAC) THEN
  YMM_GHOST_TAC `s82:x86state`
   ["YMM0","ymm0_82"; "YMM1","ymm1_82"; "YMM2","ymm2_82"; "YMM3","ymm3_82"] THEN
  X86_STEPS_TAC SI87_HPOST_EXEC (83--90) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  MP_TAC(SPECL [`word_add rsp0 (word 512):int64`; SI87_C2NUM; `4`; `s90:x86state`]
               VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(word_add rsp0 (word 512),64)) s = x MOD n`)
           (concl th)
    then ASSUME_TAC(REWRITE_RULE[MATCH_MP MOD_LT
              (REWRITE_RULE[LENGTH_LIST_OF_SEQ; ARITH_RULE `256 EXP 64 = 2 EXP 512`]
                 (ISPEC (rand(lhand(rhs(concl th)))) NUM_OF_BYTELIST_BOUND))] th)
    else NO_TAC) THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add rsp0 (word 512),64)) s90 = C` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; ARITH_RULE `64 + 8 * 128 = 1088`; ARITH_RULE `8 * 128 = 1024`] THEN
    FIRST_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add rsp0 (word 512),64)) s90 = num_of_bytelist l`) (concl th)
       then ACCEPT_TAC th else NO_TAC);
    ALL_TAC] THEN
  (* only the form C, else the precondition of the challenge is rewritten *)
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `read (memory :> bytes (word_add rsp0 (word 512),64)) s90 = num_of_bytelist l`) (concl th))) THEN
  X86_STEPS_TAC SI87_HPOST_EXEC (91--120) THEN
  HP87_FCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; `C:num`] 121 THEN
  X86_STEPS_TAC SI87_HPOST_EXEC (122--123) THEN
  HP87_FCALL_TAC "H_NTT" [`read RDI s`; `mld_poly_challenge 60 64 C`] 124 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI_END_TAC 1471;;

let HP87_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI87_RED26,"H_RED0"; SI87_RED27,"H_RED1"; SI87_RED28,"H_RED2"; SI87_RED29,"H_RED3";
      SI87_RED30,"H_RED4"; SI87_RED31,"H_RED5"; SI87_RED32,"H_RED6"; SI87_RED33,"H_RED7";
      SI87_CQ34,"H_CQ0"; SI87_CQ35,"H_CQ1"; SI87_CQ36,"H_CQ2"; SI87_CQ37,"H_CQ3";
      SI87_CQ38,"H_CQ4"; SI87_CQ39,"H_CQ5"; SI87_CQ40,"H_CQ6"; SI87_CQ41,"H_CQ7";
      SI87_DW1R42,"H_DW1R"; SI87_C2,"H_C2";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th,
      "H_CHAL"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (C:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_hp rsp0 C mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rho:num`; `rhop:num`;
                       `kappa:num`; `mu:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_HPOST_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC ([0xc0; 0xd0; 0xe0; 0xf0; 0x200; 0x210; 0x220; 0x230; 0x340] @
                    map (fun k -> 0x740 + 16 * k) (0--12) @
                    [0x1a20; 0x1e20; 0x2220; 0x2620; 0x2a20; 0x2e20; 0x3220; 0x3620]);;

let SI87_HPOST = prove
 (SI87_HPOST_STMT,
  HP87_SETUP_TAC THEN
  FULL_INIT_TAC THEN HP87_PART1_TAC THEN HP87_PART2_TAC THEN HP87_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt (HEAD), from join2 with the number n of the       *)
(* attempt in RCX and XMM4 = 0: n saved at rsp0 + 0x198, the pointer to rho''*)
(* and kappa = 7 n (16 bits) at rsp0 + 0xa0 and + 0xa8, rho copied from rsp0 *)
(* + 0x1340 to the seed buffer at rsp0 + 0xc0, the seven columns of the      *)
(* product with the matrix (YCOL 0 .. 6) and HPOST, to after the NTT of the  *)
(* challenge, as gcc's SIGN87_HEAD.                                          *)
(* ------------------------------------------------------------------------- *)

let HD87_Y = `mld_sign_y mld_poly_uniform_gamma1_19 rhop (7 * n)`;;
let HD87_W = list_mk_comb(`mld_sign_w 7`,[SI87_A; HD87_Y]);;
let HD87_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128`,HD87_W);;
let HD87_CT = mk_comb(`mld_sign_ctilde 8 128 mu`,HD87_W1);;

let SI87_HEAD_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@W@",string_of_term HD87_W; "@W1@",string_of_term HD87_W1;
   "@CT@",string_of_term HD87_CT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 n rho rhop mu C pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ n < 9361 /\\ mld_matrix_terminates 8 7 rho /\\
          num_of_bytelist(list_of_seq (@CT@) 64) = C /\\
          mld_poly_challenge_terminates 60 64 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_join2) /\\
                read RSP s = rsp0 /\\ read RCX s = word n /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word 4928),32)) s = rho /\\
                read (memory :> bytes (word_add rsp0 (word 704),64)) s = mu /\\
                read (memory :> bytes (word_add rsp0 (word 768),64)) s = rhop /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa87_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\ read R14 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 408))) s = word n /\\
                read (memory :> bytes64 (word_add rsp0 (word 160))) s = word_add rsp0 (word 768) /\\
                read (memory :> bytes16 (word_add rsp0 (word 168))) s = word (7 * n) /\\
                (!i. i < 2048 ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 (@W@) i) /\\
                (!j. j < 1024 ==> read (memory :> bytes8 (word_add rsp0 (word (5664 + j)))) s =
                                  (@W1@) j) /\\
                read (memory :> bytes (word_add rsp0 (word 512),64)) s = C /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1856 + 4 * k)))) s =
                                 mld_poly_ntt (mld_poly_challenge 60 64 C) k) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rho C mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),16383;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 56),4);
                       memory :> bytes(word_add rsp0 (word 160),16);
                       memory :> bytes(word_add rsp0 (word 192),64);
                       memory :> bytes(word_add rsp0 (word 408),8);
                       memory :> bytes(word_add rsp0 (word 512),64);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word 1856),1024);
                       memory :> bytes(word_add rsp0 (word 2880),208);
                       memory :> bytes(word_add rsp0 (word 3904),1024);
                       memory :> bytes(word_add rsp0 (word 4960),66);
                       memory :> bytes(word_add rsp0 (word 5664),1024);
                       memory :> bytes(word_add rsp0 (word 6688),8192)])");;

let SI87_HEAD_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_join2", layout "mldsa87_signature_internal_after_mldsa_poly_ntt_2")];;

let HD87_ALLOWED = [`rsp0:int64`; `rho:num`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let HD87_CALL_TAC = SI_GCALL_TAC SI87_HEAD_EXEC HD87_ALLOWED SI_XMM_PRE_TAC;;

(* the 16-bit store of 7 n (lea 0(,rcx,8), sub ecx) *)
let HD87_KAPPA = prove
 (`!n. n < 9361
       ==> word (val (word_zx (word_sub
                  (word_zx (word_zx (word_sx (word (0 + 8 * val (word n:int64)):int64):int32):int64):int32)
                  (word_zx (word n:int64):int32)):int64) MOD 65536):int16 =
           word (7 * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 64 /\ 8 * n < 2 EXP 64 /\ 8 * n < 2 EXP 32 /\ n < 2 EXP 32 /\
                7 * n < 2 EXP 32 /\ 7 * n < 2 EXP 64 /\ 7 * n < 65536`
    STRIP_ASSUME_TAC THENL [UNDISCH_TAC `n < 9361` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SI_SX_ZX; ADD_CLAUSES; word_zx; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE `8 * n = 7 * n + n`; WORD_ADD;
              WORD_RULE `word_sub (word_add (x:int32) y) y = x`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN ASM_SIMP_TAC[MOD_LT]);;

let HD87_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    MAP_EVERY (fun (th,n) -> SI_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI87_YCOL0) th,"H_YC0"; MP (SPEC_ALL SI87_YCOL1) th,"H_YC1";
      MP (SPEC_ALL SI87_YCOL2) th,"H_YC2"; MP (SPEC_ALL SI87_YCOL3) th,"H_YC3";
      MP (SPEC_ALL SI87_YCOL4) th,"H_YC4"; MP (SPEC_ALL SI87_YCOL5) th,"H_YC5";
      MP (SPEC_ALL SI87_YCOL6) th,"H_YC6";
      MP (SPEC_ALL SI87_HPOST) th,"H_HP"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rho:num) (C:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_head rsp0 rho C mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `n:num`; `rho:num`; `rhop:num`;
                       `mu:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_HEAD_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x1340; 0x1350; 0xc0; 0xd0] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`word_add rsp0 (word 4928):int64`; `32`; `rho:num`; mk_small_numeral i; `s0:x86state`]
             SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1] THEN
  X86_STEPS_TAC SI87_HEAD_EXEC (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; DIV_1]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HD87_KAPPA (ASSUME `n < 9361`)]) THEN
  SUBGOAL_THEN `rho < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (word_add rsp0 (word 4928),32)) s0 = rho`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add rsp0 (word 192):int64`; `rho:num`; `2`; `s13:x86state`] SIGN_BYTES_OF_BYTES128) THEN
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
  HD87_CALL_TAC "H_YC0" [`rsp0:int64`; `rho:num`; `rhop:num`; `7 * n`; `pc:num`] 14 THEN
  MAP_EVERY (fun j ->
    let n0 = 15 + 4 * (j - 1) in
    X86_STEPS_TAC SI87_HEAD_EXEC (n0--n0) THEN
    RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R15 s = x`) (concl th)
                             then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
    X86_STEPS_TAC SI87_HEAD_EXEC ((n0+1)--(n0+2)) THEN
    HD87_CALL_TAC ("H_YC"^string_of_int j) [`rsp0:int64`; `rho:num`; `rhop:num`; `7 * n`; `pc:num`]
      (n0+3)) (1--6) THEN
  X86_STEPS_TAC SI87_HEAD_EXEC (39--39) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R15 s = x`) (concl th)
                           then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
  X86_STEPS_TAC SI87_HEAD_EXEC (40--41) THEN
  HD87_CALL_TAC "H_HP" [`rsp0:int64`; `rho:num`; `rhop:num`; `7 * n`; `mu:num`; `C:num`; `pc:num`] 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI_END_TAC 1471;;

let SI87_HEAD = prove(SI87_HEAD_STMT, HD87_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt (ATT), from join2 to the decision after the cleanup: to   *)
(* join45 on success (r = 24) and to the count of the attempts at +0x3166    *)
(* otherwise, by cases on the result r of mld_sign_attempt_declass, as       *)
(* gcc's SIGN87_ATT: r < 7 (z_r fails, ZPRE then ZIT, and the zeroing of the *)
(* result slot at join21), 7 <= r < 23 (check r - 7 of the rows fails, ZPRE, *)
(* RPRE then RIT), 23 (too many hints) and 24 (success), both through TAIL;  *)
(* then CLEAN, which leaves XMM4 = 0 for the next attempt. On every path the *)
(* result slot at rsp0 + 0x30 is 0.                                          *)
(* ------------------------------------------------------------------------- *)

let AT87_W = HD87_W;;
let AT87_W1 = HD87_W1;;
let AT87_CPH = `mld_poly_ntt (mld_poly_challenge 60 64 C)`;;
let AT87_R0 = list_mk_comb(`mld_sign_r0`,[`mld_poly_decompose_lo_32`; AT87_W; SI87_S2H; AT87_CPH]);;
let AT87_CT0 = list_mk_comb(`mld_sign_ct0`,[SI87_T0H; AT87_CPH]);;
let AT87_SIGATT = list_mk_comb(
 `mld_sign_attempt_sig 8 7 64 60 mld_poly_uniform_gamma1_19 mld_polyz_pack_19
   640 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75`,
  [SI87_A; SI87_S1H; SI87_S2H; SI87_T0H; `mu:num`; `rhop:num`; `7 * n`]);;

let SI87_ATT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@SIGATT@",string_of_term AT87_SIGATT;
   "@S1H@",string_of_term SI87_S1H; "@S2H@",string_of_term SI87_S2H; "@T0H@",string_of_term SI87_T0H;
   "@NX@",string_of_int SI87_NX]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig sk skb rsp0 rho mu rhop n C r x b pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ n < 9361 /\\ mld_matrix_terminates 8 7 rho /\\
          mld_sign_attempt_declass 8 7 64 60 mld_poly_uniform_gamma1_19
           524168 261768 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
           128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75
           (mld_polyvec_matrix_expand 7 rho) (@S1H@) (@S2H@) (@T0H@)
           mu rhop (7 * n) = (C,r,x,b) /\\
          mld_poly_challenge_terminates 60 64 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),16383))
              [(sig,4627); (sk,4896); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,4627))
              [(sk,4896); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa87_signature_internal_join2) /\\
                read RSP s = rsp0 /\\ read RCX s = word n /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = sig /\\
                read (memory :> bytes64 (word_add rsp0 (word 40))) s = word_add sig (word 4544) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 800) /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 1568) /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 400))) s = word_add sig (word 67) /\\
                read (memory :> bytes (word_add rsp0 (word 4928),32)) s = rho /\\
                read (memory :> bytes (word_add rsp0 (word 704),64)) s = mu /\\
                read (memory :> bytes (word_add rsp0 (word 768),64)) s = rhop /\\
                (!k. k < 4896 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if r = 24 then word (pc + mldsa87_signature_internal_join45)
                 else word (pc + @NX@)) /\\
                read RSP s = rsp0 /\\
                read (memory :> bytes32 (word_add rsp0 (word 48))) s = word 0 /\\
                read XMM4 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 408))) s = word n /\\
                (r = 24
                 ==> !t. t < 4627
                         ==> read (memory :> bytes8 (word_add sig (word t))) s = (@SIGATT@) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig sk rsp0 rho C r x b mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,4627; sk,4896; word_sub rsp0 (word 1471),16383;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),784;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,4627; word_sub rsp0 (word 1471),16383]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(sig,4627);
                       memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 48),8);
                       memory :> bytes(word_add rsp0 (word 56),8);
                       memory :> bytes(word_add rsp0 (word 160),16);
                       memory :> bytes(word_add rsp0 (word 184),8);
                       memory :> bytes(word_add rsp0 (word 192),208);
                       memory :> bytes(word_add rsp0 (word 408),8);
                       memory :> bytes(word_add rsp0 (word 416),66);
                       memory :> bytes(word_add rsp0 (word 512),64);
                       memory :> bytes(word_add rsp0 (word 832),1024);
                       memory :> bytes(word_add rsp0 (word 1856),1024);
                       memory :> bytes(word_add rsp0 (word 2880),1024);
                       memory :> bytes(word_add rsp0 (word 3904),1024);
                       memory :> bytes(word_add rsp0 (word 4960),680);
                       memory :> bytes(word_add rsp0 (word 5664),1024);
                       memory :> bytes(word_add rsp0 (word 6688),8192)])");;

let SI87_ATT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa87_signature_internal_join2", SI87_NX);
   layout_range "plt_memset"];;

let AT87_ALLOWED =
  [`sig:int64`; `sk:int64`; `rsp0:int64`; `rho:num`; `C:num`; `r:num`;
   `x:num->int32`; `b:num->byte`; `mf:int64`; `mc:int64`; `pc:num`];;

let AT87_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI87_ATT_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      TRY(SI_XMM_PRE_TAC THEN NO_TAC) THEN
      VM_PRE_TAC AT87_ALLOWED;
      LABEL_TAC name th]);;

let AT87_MID = parse_term(subst_tokens ["@SIGATT@",string_of_term AT87_SIGATT]
 "\\s. read RSP s = rsp0 /\\
      (word_zx (read RBX s) = (word 0:byte) <=> ~(r = 24)) /\\
      read (memory :> bytes32 (word_add rsp0 (word 48))) s = word 0 /\\
      (read DF s <=> false) /\\
      read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
      read (memory :> bytes(ea,el)) s = ev /\\
      read (memory :> bytes64 (word_add rsp0 (word 408))) s = word n /\\
      (r = 24
       ==> !t. t < 4627
               ==> read (memory :> bytes8 (word_add sig (word t))) s = (@SIGATT@) t)");;

(*** z_r fails, r < 7 ***)

let AT87_ZCASE_TAC =
  SUBGOAL_THEN `r <= 7 /\ ~(r = 24)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 7` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 7 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  AT87_CALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `7 * n`; AT87_CPH; `pc:num`] 2 THEN
  SI_PC_TAC THEN
  AT87_CALL_TAC "H_ZIT"
   [`F`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `7 * n`; `r:num`; AT87_CPH; `pc:num`] 3 THEN
  SI_PC_TAC THEN
  X86_STEPS_TAC SI87_ATT_EXEC (4--5) THEN
  SI_FIN_TAC 1471;;

let AT87_TEMPLATE =
 `\(sig:int64) (sk:int64) (rsp0:int64) (rho:num) (C:num) (r:num) (x:num->int32) (b:num->byte)
   (mf:int64) (mc:int64) (pc:num).
   APPEND (f_ev_cl sig sk rsp0 rho C r x b mf mc pc)
    (APPEND
      (if r < 7 then f_ev_pz sig sk rsp0 rho C r x b mf mc pc
       else if r < 23
       then if EVEN (r - 7) then f_ev_pw1 sig sk rsp0 rho C r x b mf mc pc
            else f_ev_pw2 sig sk rsp0 rho C r x b mf mc pc
       else f_ev_pt sig sk rsp0 rho C r x b mf mc pc)
      (f_ev_hd sig sk rsp0 rho C r x b mf mc pc))
   :(uarch_event)list`;;

let AT87_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> SI_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI87_HEAD) th,"H_HEAD"; MP (SPEC_ALL SI87_ZPRE) th,"H_ZPRE";
      MP (SPEC_ALL SI87_ZIT) th,"H_ZIT"; SI87_RPRE,"H_RPRE"; SI87_RIT,"H_RIT";
      SI87_TAIL,"H_TAIL"; MP (SPEC_ALL SI87_CLEAN) ms,"H_CLEAN"]) THEN
  CONCRETIZE_F_EVENTS_TAC AT87_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rho:num`; `mu:num`; `rhop:num`; `n:num`; `C:num`; `r:num`; `x:num->int32`;
    `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_ATT_EXEC] THEN
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

(*** check r - 7 of the rows fails, 7 <= r < 23 ***)

let AT87_ROWSLICE_TAC m st =
  MP_TAC(SPECL [`rsp0:int64`; `6688`; `2048`; `mld_poly_decompose_lo_32`; AT87_W; m; st]
               SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [m; st]
             `!k. 256 * m <= k /\ k < 2048
                  ==> read (memory :> bytes32 (word_add rsp0 (word (6688 + 4 * k)))) st = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

let AT87_WCASE_TAC =
  SUBGOAL_THEN `(r - 7) DIV 2 <= 8 /\ (r - 7) DIV 2 < 8 /\ ~(r = 24) /\
                2 * (r - 7) DIV 2 <= r - 7`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 23` THEN UNDISCH_TAC `7 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [AT87_R0; AT87_CT0; `261768`; `261888`; `r - 7`;
                `(r - 7) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 7` THEN UNDISCH_TAC `r < 23` THEN ARITH_TAC;
    DISCH_TAC] THEN
  AT87_CALL_TAC "H_ZPRE"
   [`7`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `7 * n`; AT87_CPH; `pc:num`] 2 THEN
  SI_PC_TAC THEN
  AT87_CALL_TAC "H_RPRE"
   [`(r - 7) DIV 2`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; AT87_W; AT87_CPH; `pc:num`] 3 THEN
  SI_PC_TAC THEN
  AT87_ROWSLICE_TAC `(r - 7) DIV 2` `s3:x86state` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `7 <= r /\ r < 23 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 7)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 7) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    AT87_CALL_TAC "H_RIT"
     [`F`; `F`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `(r - 7) DIV 2`; AT87_W; AT87_CPH;
      `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 7) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`7`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 8` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 23` THEN ARITH_TAC; DISCH_TAC] THEN
    AT87_CALL_TAC "H_RIT"
     [`T`; `F`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `(r - 7) DIV 2`; AT87_W; AT87_CPH;
      `pc:num`] 4] THEN
  SI_PC_TAC THEN
  X86_STEPS_TAC SI87_ATT_EXEC (5--5) THEN
  SI_FIN_TAC 1471;;

(*** the hints, r = 23 (too many) or 24 (success) ***)

let AT87_TCASE_TAC =
  SUBGOAL_THEN `23 <= r /\ 7 <= 7` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 23)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [AT87_R0; AT87_CT0; `261768`; `261888`; `16`; `8`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `23 <= r` THEN UNDISCH_TAC `j < 16` THEN ARITH_TAC;
    DISCH_TAC] THEN
  AT87_CALL_TAC "H_ZPRE"
   [`7`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `7 * n`; AT87_CPH; `pc:num`] 2 THEN
  SI_PC_TAC THEN
  AT87_CALL_TAC "H_RPRE"
   [`8`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; AT87_W; AT87_CPH; `pc:num`] 3 THEN
  SI_PC_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ARITH_RULE `0 < 8`] o
    check (fun th -> is_imp(concl th) && lhand(concl th) = `0 < 8`)) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 23 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 23 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 1024
        ==> read (memory :> bytes8 (word_add rsp0 (word (5664 + j)))) s3 =
            (b:num->byte) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "b"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_hint_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  AT87_CALL_TAC "H_TAIL"
   [`sig:int64`; `rsp0:int64`; `read RBX s`; `C:num`; `x:num->int32`; `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `23 <= r ==> (r = 24 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 24` THENL
   [SUBGOAL_THEN `mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 24`
                            then ACCEPT_TAC(EQ_MP th (ASSUME `r = 24`)) else NO_TAC); ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75`]) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`sig:int64`; `C:num`] `read (memory :> bytes (sig,64)) s = C`) (concl th)
      then FIRST_ASSUM(fun cth ->
             if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
             then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES (TRANS th (SYM cth)))
             else NO_TAC)
      else NO_TAC) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if concl th = `r = 24` then ASSUME_TAC(EQT_INTRO th)
                                   else NO_TAC)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[mld_sign_attempt_sig] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `4627 = (64 + 7 * 640) + 83` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> can (term_match []
          `!t. t < 640 * 7
               ==> read (memory :> bytes8 (word_add sig (word (64 + t)))) s =
                   P t`) (concl th))) THEN NO_TAC) THEN
    (SI_MAYCHANGE_TAC 1471 ORELSE SI_PATH_DISCHARGE_TAC 1471);
    SUBGOAL_THEN `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 24`
                            then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[ASSUME `~(r = 24)`]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75)`]) THEN
    X86_STEPS_TAC SI87_ATT_EXEC (5--5) THEN
    SI_FIN_TAC 1471];;

let AT87_PATHS_TAC =
  ASM_CASES_TAC `r < 7` THENL
   [AT87_ZCASE_TAC;
    SUBGOAL_THEN `7 <= r /\ 7 <= 7` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 7)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `7 <= r ==> (!i. i < 7 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r < 23` THENL [AT87_WCASE_TAC; AT87_TCASE_TAC]];;

let AT87_CLEAN_TAC =
  FULL_INIT_TAC THEN
  AT87_CALL_TAC "H_CLEAN" [`r = 24`; `rsp0:int64`; `read RBX s`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (SI_MAYCHANGE_TAC 1471 ORELSE SI_DISCHARGE_TAC 1471);;

let SI87_ATT = prove
 (SI87_ATT_STMT,
  AT87_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa87_signature_internal_join23` AT87_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    AT87_CALL_TAC "H_HEAD"
     [`rsp0:int64`; `n:num`; `rho:num`; `rhop:num`; `mu:num`; `C:num`; `pc:num`] 1 THEN
    AT87_PATHS_TAC;
    AT87_CLEAN_TAC]);;
