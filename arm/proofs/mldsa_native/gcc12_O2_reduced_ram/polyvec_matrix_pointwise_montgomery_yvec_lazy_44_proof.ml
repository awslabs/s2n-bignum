(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = A y of signing, with A sampled on demand and y sampled    *)
(* polynomial by polynomial: the proof (see                                  *)
(* polyvec_matrix_pointwise_montgomery_yvec_lazy_44_spec.ml).                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let YVL44_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_EXEC;;

let YVL44_G = `mld_poly_uniform_gamma1_17`;;

(* ------------------------------------------------------------------------- *)
(* The frame of 176 bytes is at stackpointer + 1392 (the 1392 bytes below it *)
(* are those of mldsa_poly_uniform), with the saved registers at             *)
(* stackpointer + 1392, the canary at stackpointer + 1560 and the buffer of  *)
(* the seed, aligned to 32 bytes, at stackpointer + 1472 or + 1488. The code *)
(* is simulated with both loops unrolled, in each case of the stack          *)
(* alignment, with the calls at the steps of the schedule given by the code: *)
(* for each column j, the sampling of polynomial j of y and its transform,   *)
(* and for each row i the seed and the termination hypothesis of entry (i,j) *)
(* before its sampling, its product with polynomial j of the transform of y, *)
(* and for j > 0 its addition to polynomial i of w; then the reduction and   *)
(* the inverse transform of w.                                               *)
(* ------------------------------------------------------------------------- *)

let YVL44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1503 1472 1488;;

let YVL44_ALLOWED =
  [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`; `r:num`;
   `rp:int64`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let YVL44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc YVL44_EXEC name
   ilist YVL44_ALLOWED n;;

let YVL44_CASE_TAC bf =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
      `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add mat (word 1024)) (word 16):int64 =
                          word_add mat (word 1040)`] THEN
  STRIP_TAC THEN MLD_LAZY_RBOUND_TAC "s0" THEN
  ARM_STEPS_TAC YVL44_EXEC (1--6) THEN
  MEXP_BUFFER_TAC YVL44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC YVL44_EXEC (7--13) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL44_EXEC (14--27) THEN
  YVL44_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 28 THEN
  MLD_LAZY_YVEC_Y_TAC YVL44_G 0 THEN
  ARM_STEPS_TAC YVL44_EXEC (29--30) THEN
  YVL44_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL44_G 0;
    `pc:num`; `read X30 s`] 31 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL44_G 0 THEN
  ARM_STEPS_TAC YVL44_EXEC (32--36) THEN
  MEXP_INPUT_TAC bf 0 0 `s36:armstate` THEN
  MEXP_HYP_TAC 0 0 THEN
  ARM_STEPS_TAC YVL44_EXEC [37] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 38 THEN
  ARM_STEPS_TAC YVL44_EXEC (39--41) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 0;
    MLD_LAZY_YVEC_YHAT YVL44_G 0;
    `pc:num`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC YVL44_EXEC (43--52) THEN
  MEXP_INPUT_TAC bf 1 0 `s52:armstate` THEN
  MEXP_HYP_TAC 1 0 THEN
  ARM_STEPS_TAC YVL44_EXEC [53] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 54 THEN
  ARM_STEPS_TAC YVL44_EXEC (55--57) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 0;
    MLD_LAZY_YVEC_YHAT YVL44_G 0;
    `pc:num`; `read X30 s`] 58 THEN
  ARM_STEPS_TAC YVL44_EXEC (59--68) THEN
  MEXP_INPUT_TAC bf 2 0 `s68:armstate` THEN
  MEXP_HYP_TAC 2 0 THEN
  ARM_STEPS_TAC YVL44_EXEC [69] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 70 THEN
  ARM_STEPS_TAC YVL44_EXEC (71--73) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 0;
    MLD_LAZY_YVEC_YHAT YVL44_G 0;
    `pc:num`; `read X30 s`] 74 THEN
  ARM_STEPS_TAC YVL44_EXEC (75--84) THEN
  MEXP_INPUT_TAC bf 3 0 `s84:armstate` THEN
  MEXP_HYP_TAC 3 0 THEN
  ARM_STEPS_TAC YVL44_EXEC [85] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 86 THEN
  ARM_STEPS_TAC YVL44_EXEC (87--89) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 0;
    MLD_LAZY_YVEC_YHAT YVL44_G 0;
    `pc:num`; `read X30 s`] 90 THEN
  ARM_STEPS_TAC YVL44_EXEC (91--105) THEN
  YVL44_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 106 THEN
  MLD_LAZY_YVEC_Y_TAC YVL44_G 1 THEN
  ARM_STEPS_TAC YVL44_EXEC (107--108) THEN
  YVL44_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL44_G 1;
    `pc:num`; `read X30 s`] 109 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL44_G 1 THEN
  ARM_STEPS_TAC YVL44_EXEC (110--114) THEN
  MEXP_INPUT_TAC bf 0 1 `s114:armstate` THEN
  MEXP_HYP_TAC 0 1 THEN
  ARM_STEPS_TAC YVL44_EXEC [115] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 116 THEN
  ARM_STEPS_TAC YVL44_EXEC (117--119) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 1;
    MLD_LAZY_YVEC_YHAT YVL44_G 1;
    `pc:num`; `read X30 s`] 120 THEN
  ARM_STEPS_TAC YVL44_EXEC (121--123) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 0 0;
    MLD_LAZY_YVEC_PW YVL44_G 0 1; `pc:num`; `read X30 s`]
   124 THEN
  ARM_STEPS_TAC YVL44_EXEC (125--133) THEN
  MEXP_INPUT_TAC bf 1 1 `s133:armstate` THEN
  MEXP_HYP_TAC 1 1 THEN
  ARM_STEPS_TAC YVL44_EXEC [134] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 135 THEN
  ARM_STEPS_TAC YVL44_EXEC (136--138) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 1;
    MLD_LAZY_YVEC_YHAT YVL44_G 1;
    `pc:num`; `read X30 s`] 139 THEN
  ARM_STEPS_TAC YVL44_EXEC (140--142) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 1 0;
    MLD_LAZY_YVEC_PW YVL44_G 1 1; `pc:num`; `read X30 s`]
   143 THEN
  ARM_STEPS_TAC YVL44_EXEC (144--152) THEN
  MEXP_INPUT_TAC bf 2 1 `s152:armstate` THEN
  MEXP_HYP_TAC 2 1 THEN
  ARM_STEPS_TAC YVL44_EXEC [153] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 154 THEN
  ARM_STEPS_TAC YVL44_EXEC (155--157) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 1;
    MLD_LAZY_YVEC_YHAT YVL44_G 1;
    `pc:num`; `read X30 s`] 158 THEN
  ARM_STEPS_TAC YVL44_EXEC (159--161) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 2 0;
    MLD_LAZY_YVEC_PW YVL44_G 2 1; `pc:num`; `read X30 s`]
   162 THEN
  ARM_STEPS_TAC YVL44_EXEC (163--171) THEN
  MEXP_INPUT_TAC bf 3 1 `s171:armstate` THEN
  MEXP_HYP_TAC 3 1 THEN
  ARM_STEPS_TAC YVL44_EXEC [172] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 173 THEN
  ARM_STEPS_TAC YVL44_EXEC (174--176) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 1;
    MLD_LAZY_YVEC_YHAT YVL44_G 1;
    `pc:num`; `read X30 s`] 177 THEN
  ARM_STEPS_TAC YVL44_EXEC (178--180) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 3 0;
    MLD_LAZY_YVEC_PW YVL44_G 3 1; `pc:num`; `read X30 s`]
   181 THEN
  ARM_STEPS_TAC YVL44_EXEC (182--195) THEN
  YVL44_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 196 THEN
  MLD_LAZY_YVEC_Y_TAC YVL44_G 2 THEN
  ARM_STEPS_TAC YVL44_EXEC (197--198) THEN
  YVL44_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL44_G 2;
    `pc:num`; `read X30 s`] 199 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL44_G 2 THEN
  ARM_STEPS_TAC YVL44_EXEC (200--204) THEN
  MEXP_INPUT_TAC bf 0 2 `s204:armstate` THEN
  MEXP_HYP_TAC 0 2 THEN
  ARM_STEPS_TAC YVL44_EXEC [205] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 206 THEN
  ARM_STEPS_TAC YVL44_EXEC (207--209) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 2;
    MLD_LAZY_YVEC_YHAT YVL44_G 2;
    `pc:num`; `read X30 s`] 210 THEN
  ARM_STEPS_TAC YVL44_EXEC (211--213) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 0 1;
    MLD_LAZY_YVEC_PW YVL44_G 0 2; `pc:num`; `read X30 s`]
   214 THEN
  ARM_STEPS_TAC YVL44_EXEC (215--223) THEN
  MEXP_INPUT_TAC bf 1 2 `s223:armstate` THEN
  MEXP_HYP_TAC 1 2 THEN
  ARM_STEPS_TAC YVL44_EXEC [224] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 225 THEN
  ARM_STEPS_TAC YVL44_EXEC (226--228) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 2;
    MLD_LAZY_YVEC_YHAT YVL44_G 2;
    `pc:num`; `read X30 s`] 229 THEN
  ARM_STEPS_TAC YVL44_EXEC (230--232) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 1 1;
    MLD_LAZY_YVEC_PW YVL44_G 1 2; `pc:num`; `read X30 s`]
   233 THEN
  ARM_STEPS_TAC YVL44_EXEC (234--242) THEN
  MEXP_INPUT_TAC bf 2 2 `s242:armstate` THEN
  MEXP_HYP_TAC 2 2 THEN
  ARM_STEPS_TAC YVL44_EXEC [243] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 244 THEN
  ARM_STEPS_TAC YVL44_EXEC (245--247) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 2;
    MLD_LAZY_YVEC_YHAT YVL44_G 2;
    `pc:num`; `read X30 s`] 248 THEN
  ARM_STEPS_TAC YVL44_EXEC (249--251) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 2 1;
    MLD_LAZY_YVEC_PW YVL44_G 2 2; `pc:num`; `read X30 s`]
   252 THEN
  ARM_STEPS_TAC YVL44_EXEC (253--261) THEN
  MEXP_INPUT_TAC bf 3 2 `s261:armstate` THEN
  MEXP_HYP_TAC 3 2 THEN
  ARM_STEPS_TAC YVL44_EXEC [262] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 263 THEN
  ARM_STEPS_TAC YVL44_EXEC (264--266) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 2;
    MLD_LAZY_YVEC_YHAT YVL44_G 2;
    `pc:num`; `read X30 s`] 267 THEN
  ARM_STEPS_TAC YVL44_EXEC (268--270) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 3 1;
    MLD_LAZY_YVEC_PW YVL44_G 3 2; `pc:num`; `read X30 s`]
   271 THEN
  ARM_STEPS_TAC YVL44_EXEC (272--285) THEN
  YVL44_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 286 THEN
  MLD_LAZY_YVEC_Y_TAC YVL44_G 3 THEN
  ARM_STEPS_TAC YVL44_EXEC (287--288) THEN
  YVL44_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL44_G 3;
    `pc:num`; `read X30 s`] 289 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL44_G 3 THEN
  ARM_STEPS_TAC YVL44_EXEC (290--294) THEN
  MEXP_INPUT_TAC bf 0 3 `s294:armstate` THEN
  MEXP_HYP_TAC 0 3 THEN
  ARM_STEPS_TAC YVL44_EXEC [295] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 296 THEN
  ARM_STEPS_TAC YVL44_EXEC (297--299) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 3;
    MLD_LAZY_YVEC_YHAT YVL44_G 3;
    `pc:num`; `read X30 s`] 300 THEN
  ARM_STEPS_TAC YVL44_EXEC (301--303) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 0 2;
    MLD_LAZY_YVEC_PW YVL44_G 0 3; `pc:num`; `read X30 s`]
   304 THEN
  ARM_STEPS_TAC YVL44_EXEC (305--313) THEN
  MEXP_INPUT_TAC bf 1 3 `s313:armstate` THEN
  MEXP_HYP_TAC 1 3 THEN
  ARM_STEPS_TAC YVL44_EXEC [314] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 315 THEN
  ARM_STEPS_TAC YVL44_EXEC (316--318) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 3;
    MLD_LAZY_YVEC_YHAT YVL44_G 3;
    `pc:num`; `read X30 s`] 319 THEN
  ARM_STEPS_TAC YVL44_EXEC (320--322) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 1 2;
    MLD_LAZY_YVEC_PW YVL44_G 1 3; `pc:num`; `read X30 s`]
   323 THEN
  ARM_STEPS_TAC YVL44_EXEC (324--332) THEN
  MEXP_INPUT_TAC bf 2 3 `s332:armstate` THEN
  MEXP_HYP_TAC 2 3 THEN
  ARM_STEPS_TAC YVL44_EXEC [333] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 334 THEN
  ARM_STEPS_TAC YVL44_EXEC (335--337) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 3;
    MLD_LAZY_YVEC_YHAT YVL44_G 3;
    `pc:num`; `read X30 s`] 338 THEN
  ARM_STEPS_TAC YVL44_EXEC (339--341) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 2 2;
    MLD_LAZY_YVEC_PW YVL44_G 2 3; `pc:num`; `read X30 s`]
   342 THEN
  ARM_STEPS_TAC YVL44_EXEC (343--351) THEN
  MEXP_INPUT_TAC bf 3 3 `s351:armstate` THEN
  MEXP_HYP_TAC 3 3 THEN
  ARM_STEPS_TAC YVL44_EXEC [352] THEN
  YVL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 353 THEN
  ARM_STEPS_TAC YVL44_EXEC (354--356) THEN
  YVL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 3;
    MLD_LAZY_YVEC_YHAT YVL44_G 3;
    `pc:num`; `read X30 s`] 357 THEN
  ARM_STEPS_TAC YVL44_EXEC (358--360) THEN
  YVL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL44_G 3 2;
    MLD_LAZY_YVEC_PW YVL44_G 3 3; `pc:num`; `read X30 s`]
   361 THEN
  ARM_STEPS_TAC YVL44_EXEC (362--373) THEN
  MLD_LAZY_YVEC_JOIN_TAC YVL44_G 4 4 "s373" THEN
  YVL44_CALL_TAC "H_VRED"
   [`read X0 s`; MLD_LAZY_YVEC_W YVL44_G 4; `pc:num`; `read SP s`;
    `read X30 s`] 374 THEN
  ARM_STEPS_TAC YVL44_EXEC (375--376) THEN
  YVL44_CALL_TAC "H_VINV"
   [`read X0 s`; mk_comb(`mld_polyvec_map mld_poly_reduce`,
                         MLD_LAZY_YVEC_W YVL44_G 4);
    `pc:num`; `read SP s`; `read X30 s`] 377 THEN
  ARM_STEPS_TAC YVL44_EXEC [378] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL44_EXEC (379--390) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MLD_LAZY_YVEC_POST_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
     "H_G1") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
     "H_UNIF") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VRED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VINV" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(w:int64) (mat:int64) (y:int64) (scratch:int64) (r:num) (rp:int64)
     (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if aligned 32 stackpointer
     then f_ev_a w mat y scratch r rp guard mf pc stackpointer returnaddress
     else f_ev_u w mat y scratch r rp guard mf pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst YVL44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1568):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--26) THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    YVL44_CASE_TAC 1472;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    YVL44_CASE_TAC 1488]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
