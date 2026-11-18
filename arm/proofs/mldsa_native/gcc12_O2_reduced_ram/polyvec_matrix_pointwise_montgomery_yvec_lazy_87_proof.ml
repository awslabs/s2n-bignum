(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = A y of signing, with A sampled on demand and y sampled    *)
(* polynomial by polynomial: the proof (see                                  *)
(* polyvec_matrix_pointwise_montgomery_yvec_lazy_87_spec.ml).                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let YVL87_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_EXEC;;

let YVL87_G = `mld_poly_uniform_gamma1_19`;;

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

let YVL87_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1503 1472 1488;;

let YVL87_ALLOWED =
  [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`; `r:num`;
   `rp:int64`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let YVL87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc YVL87_EXEC name
   ilist YVL87_ALLOWED n;;

let YVL87_CASE_TAC bf =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
      `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add mat (word 1024)) (word 16):int64 =
                          word_add mat (word 1040)`] THEN
  STRIP_TAC THEN MLD_LAZY_RBOUND_TAC "s0" THEN
  ARM_STEPS_TAC YVL87_EXEC (1--7) THEN
  MEXP_BUFFER_TAC YVL87_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC YVL87_EXEC (8--13) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL87_EXEC (14--28) THEN
  YVL87_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  MLD_LAZY_YVEC_Y_TAC YVL87_G 0 THEN
  ARM_STEPS_TAC YVL87_EXEC (30--31) THEN
  YVL87_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL87_G 0;
    `pc:num`; `read X30 s`] 32 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL87_G 0 THEN
  ARM_STEPS_TAC YVL87_EXEC (33--38) THEN
  MEXP_INPUT_TAC bf 0 0 `s38:armstate` THEN
  MEXP_HYP_TAC 0 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [39] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 40 THEN
  ARM_STEPS_TAC YVL87_EXEC (41--44) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC YVL87_EXEC (46--53) THEN
  MEXP_INPUT_TAC bf 1 0 `s53:armstate` THEN
  MEXP_HYP_TAC 1 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [54] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 55 THEN
  ARM_STEPS_TAC YVL87_EXEC (56--59) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 60 THEN
  ARM_STEPS_TAC YVL87_EXEC (61--68) THEN
  MEXP_INPUT_TAC bf 2 0 `s68:armstate` THEN
  MEXP_HYP_TAC 2 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [69] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 70 THEN
  ARM_STEPS_TAC YVL87_EXEC (71--74) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 75 THEN
  ARM_STEPS_TAC YVL87_EXEC (76--83) THEN
  MEXP_INPUT_TAC bf 3 0 `s83:armstate` THEN
  MEXP_HYP_TAC 3 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [84] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 85 THEN
  ARM_STEPS_TAC YVL87_EXEC (86--89) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 90 THEN
  ARM_STEPS_TAC YVL87_EXEC (91--98) THEN
  MEXP_INPUT_TAC bf 4 0 `s98:armstate` THEN
  MEXP_HYP_TAC 4 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [99] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 100 THEN
  ARM_STEPS_TAC YVL87_EXEC (101--104) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 105 THEN
  ARM_STEPS_TAC YVL87_EXEC (106--113) THEN
  MEXP_INPUT_TAC bf 5 0 `s113:armstate` THEN
  MEXP_HYP_TAC 5 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [114] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 115 THEN
  ARM_STEPS_TAC YVL87_EXEC (116--119) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 120 THEN
  ARM_STEPS_TAC YVL87_EXEC (121--128) THEN
  MEXP_INPUT_TAC bf 6 0 `s128:armstate` THEN
  MEXP_HYP_TAC 6 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [129] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 6 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 130 THEN
  ARM_STEPS_TAC YVL87_EXEC (131--134) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 6 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 135 THEN
  ARM_STEPS_TAC YVL87_EXEC (136--143) THEN
  MEXP_INPUT_TAC bf 7 0 `s143:armstate` THEN
  MEXP_HYP_TAC 7 0 THEN
  ARM_STEPS_TAC YVL87_EXEC [144] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 7 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 145 THEN
  ARM_STEPS_TAC YVL87_EXEC (146--149) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 7 0;
    MLD_LAZY_YVEC_YHAT YVL87_G 0;
    `pc:num`; `read X30 s`] 150 THEN
  ARM_STEPS_TAC YVL87_EXEC (151--163) THEN
  YVL87_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 164 THEN
  MLD_LAZY_YVEC_Y_TAC YVL87_G 1 THEN
  ARM_STEPS_TAC YVL87_EXEC (165--166) THEN
  YVL87_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL87_G 1;
    `pc:num`; `read X30 s`] 167 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL87_G 1 THEN
  ARM_STEPS_TAC YVL87_EXEC (168--173) THEN
  MEXP_INPUT_TAC bf 0 1 `s173:armstate` THEN
  MEXP_HYP_TAC 0 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [174] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 175 THEN
  ARM_STEPS_TAC YVL87_EXEC (176--178) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 179 THEN
  ARM_STEPS_TAC YVL87_EXEC (180--183) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 0 0;
    MLD_LAZY_YVEC_PW YVL87_G 0 1; `pc:num`; `read X30 s`]
   184 THEN
  ARM_STEPS_TAC YVL87_EXEC (185--192) THEN
  MEXP_INPUT_TAC bf 1 1 `s192:armstate` THEN
  MEXP_HYP_TAC 1 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [193] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 194 THEN
  ARM_STEPS_TAC YVL87_EXEC (195--197) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 198 THEN
  ARM_STEPS_TAC YVL87_EXEC (199--202) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 1 0;
    MLD_LAZY_YVEC_PW YVL87_G 1 1; `pc:num`; `read X30 s`]
   203 THEN
  ARM_STEPS_TAC YVL87_EXEC (204--211) THEN
  MEXP_INPUT_TAC bf 2 1 `s211:armstate` THEN
  MEXP_HYP_TAC 2 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [212] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 213 THEN
  ARM_STEPS_TAC YVL87_EXEC (214--216) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 217 THEN
  ARM_STEPS_TAC YVL87_EXEC (218--221) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 2 0;
    MLD_LAZY_YVEC_PW YVL87_G 2 1; `pc:num`; `read X30 s`]
   222 THEN
  ARM_STEPS_TAC YVL87_EXEC (223--230) THEN
  MEXP_INPUT_TAC bf 3 1 `s230:armstate` THEN
  MEXP_HYP_TAC 3 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [231] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 232 THEN
  ARM_STEPS_TAC YVL87_EXEC (233--235) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 236 THEN
  ARM_STEPS_TAC YVL87_EXEC (237--240) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 3 0;
    MLD_LAZY_YVEC_PW YVL87_G 3 1; `pc:num`; `read X30 s`]
   241 THEN
  ARM_STEPS_TAC YVL87_EXEC (242--249) THEN
  MEXP_INPUT_TAC bf 4 1 `s249:armstate` THEN
  MEXP_HYP_TAC 4 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [250] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 251 THEN
  ARM_STEPS_TAC YVL87_EXEC (252--254) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 255 THEN
  ARM_STEPS_TAC YVL87_EXEC (256--259) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 4 0;
    MLD_LAZY_YVEC_PW YVL87_G 4 1; `pc:num`; `read X30 s`]
   260 THEN
  ARM_STEPS_TAC YVL87_EXEC (261--268) THEN
  MEXP_INPUT_TAC bf 5 1 `s268:armstate` THEN
  MEXP_HYP_TAC 5 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [269] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 270 THEN
  ARM_STEPS_TAC YVL87_EXEC (271--273) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 274 THEN
  ARM_STEPS_TAC YVL87_EXEC (275--278) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 5 0;
    MLD_LAZY_YVEC_PW YVL87_G 5 1; `pc:num`; `read X30 s`]
   279 THEN
  ARM_STEPS_TAC YVL87_EXEC (280--287) THEN
  MEXP_INPUT_TAC bf 6 1 `s287:armstate` THEN
  MEXP_HYP_TAC 6 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [288] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 6 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 289 THEN
  ARM_STEPS_TAC YVL87_EXEC (290--292) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 6 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 293 THEN
  ARM_STEPS_TAC YVL87_EXEC (294--297) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 6 0;
    MLD_LAZY_YVEC_PW YVL87_G 6 1; `pc:num`; `read X30 s`]
   298 THEN
  ARM_STEPS_TAC YVL87_EXEC (299--306) THEN
  MEXP_INPUT_TAC bf 7 1 `s306:armstate` THEN
  MEXP_HYP_TAC 7 1 THEN
  ARM_STEPS_TAC YVL87_EXEC [307] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 7 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 308 THEN
  ARM_STEPS_TAC YVL87_EXEC (309--311) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 7 1;
    MLD_LAZY_YVEC_YHAT YVL87_G 1;
    `pc:num`; `read X30 s`] 312 THEN
  ARM_STEPS_TAC YVL87_EXEC (313--316) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 7 0;
    MLD_LAZY_YVEC_PW YVL87_G 7 1; `pc:num`; `read X30 s`]
   317 THEN
  ARM_STEPS_TAC YVL87_EXEC (318--330) THEN
  YVL87_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 331 THEN
  MLD_LAZY_YVEC_Y_TAC YVL87_G 2 THEN
  ARM_STEPS_TAC YVL87_EXEC (332--333) THEN
  YVL87_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL87_G 2;
    `pc:num`; `read X30 s`] 334 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL87_G 2 THEN
  ARM_STEPS_TAC YVL87_EXEC (335--340) THEN
  MEXP_INPUT_TAC bf 0 2 `s340:armstate` THEN
  MEXP_HYP_TAC 0 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [341] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 342 THEN
  ARM_STEPS_TAC YVL87_EXEC (343--345) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 346 THEN
  ARM_STEPS_TAC YVL87_EXEC (347--350) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 0 1;
    MLD_LAZY_YVEC_PW YVL87_G 0 2; `pc:num`; `read X30 s`]
   351 THEN
  ARM_STEPS_TAC YVL87_EXEC (352--359) THEN
  MEXP_INPUT_TAC bf 1 2 `s359:armstate` THEN
  MEXP_HYP_TAC 1 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [360] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 361 THEN
  ARM_STEPS_TAC YVL87_EXEC (362--364) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 365 THEN
  ARM_STEPS_TAC YVL87_EXEC (366--369) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 1 1;
    MLD_LAZY_YVEC_PW YVL87_G 1 2; `pc:num`; `read X30 s`]
   370 THEN
  ARM_STEPS_TAC YVL87_EXEC (371--378) THEN
  MEXP_INPUT_TAC bf 2 2 `s378:armstate` THEN
  MEXP_HYP_TAC 2 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [379] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 380 THEN
  ARM_STEPS_TAC YVL87_EXEC (381--383) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 384 THEN
  ARM_STEPS_TAC YVL87_EXEC (385--388) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 2 1;
    MLD_LAZY_YVEC_PW YVL87_G 2 2; `pc:num`; `read X30 s`]
   389 THEN
  ARM_STEPS_TAC YVL87_EXEC (390--397) THEN
  MEXP_INPUT_TAC bf 3 2 `s397:armstate` THEN
  MEXP_HYP_TAC 3 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [398] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 399 THEN
  ARM_STEPS_TAC YVL87_EXEC (400--402) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 403 THEN
  ARM_STEPS_TAC YVL87_EXEC (404--407) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 3 1;
    MLD_LAZY_YVEC_PW YVL87_G 3 2; `pc:num`; `read X30 s`]
   408 THEN
  ARM_STEPS_TAC YVL87_EXEC (409--416) THEN
  MEXP_INPUT_TAC bf 4 2 `s416:armstate` THEN
  MEXP_HYP_TAC 4 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [417] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 418 THEN
  ARM_STEPS_TAC YVL87_EXEC (419--421) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 422 THEN
  ARM_STEPS_TAC YVL87_EXEC (423--426) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 4 1;
    MLD_LAZY_YVEC_PW YVL87_G 4 2; `pc:num`; `read X30 s`]
   427 THEN
  ARM_STEPS_TAC YVL87_EXEC (428--435) THEN
  MEXP_INPUT_TAC bf 5 2 `s435:armstate` THEN
  MEXP_HYP_TAC 5 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [436] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 437 THEN
  ARM_STEPS_TAC YVL87_EXEC (438--440) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 441 THEN
  ARM_STEPS_TAC YVL87_EXEC (442--445) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 5 1;
    MLD_LAZY_YVEC_PW YVL87_G 5 2; `pc:num`; `read X30 s`]
   446 THEN
  ARM_STEPS_TAC YVL87_EXEC (447--454) THEN
  MEXP_INPUT_TAC bf 6 2 `s454:armstate` THEN
  MEXP_HYP_TAC 6 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [455] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 6 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 456 THEN
  ARM_STEPS_TAC YVL87_EXEC (457--459) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 6 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 460 THEN
  ARM_STEPS_TAC YVL87_EXEC (461--464) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 6 1;
    MLD_LAZY_YVEC_PW YVL87_G 6 2; `pc:num`; `read X30 s`]
   465 THEN
  ARM_STEPS_TAC YVL87_EXEC (466--473) THEN
  MEXP_INPUT_TAC bf 7 2 `s473:armstate` THEN
  MEXP_HYP_TAC 7 2 THEN
  ARM_STEPS_TAC YVL87_EXEC [474] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 7 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 475 THEN
  ARM_STEPS_TAC YVL87_EXEC (476--478) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 7 2;
    MLD_LAZY_YVEC_YHAT YVL87_G 2;
    `pc:num`; `read X30 s`] 479 THEN
  ARM_STEPS_TAC YVL87_EXEC (480--483) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 7 1;
    MLD_LAZY_YVEC_PW YVL87_G 7 2; `pc:num`; `read X30 s`]
   484 THEN
  ARM_STEPS_TAC YVL87_EXEC (485--497) THEN
  YVL87_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 498 THEN
  MLD_LAZY_YVEC_Y_TAC YVL87_G 3 THEN
  ARM_STEPS_TAC YVL87_EXEC (499--500) THEN
  YVL87_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL87_G 3;
    `pc:num`; `read X30 s`] 501 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL87_G 3 THEN
  ARM_STEPS_TAC YVL87_EXEC (502--507) THEN
  MEXP_INPUT_TAC bf 0 3 `s507:armstate` THEN
  MEXP_HYP_TAC 0 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [508] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 509 THEN
  ARM_STEPS_TAC YVL87_EXEC (510--512) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 513 THEN
  ARM_STEPS_TAC YVL87_EXEC (514--517) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 0 2;
    MLD_LAZY_YVEC_PW YVL87_G 0 3; `pc:num`; `read X30 s`]
   518 THEN
  ARM_STEPS_TAC YVL87_EXEC (519--526) THEN
  MEXP_INPUT_TAC bf 1 3 `s526:armstate` THEN
  MEXP_HYP_TAC 1 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [527] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 528 THEN
  ARM_STEPS_TAC YVL87_EXEC (529--531) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 532 THEN
  ARM_STEPS_TAC YVL87_EXEC (533--536) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 1 2;
    MLD_LAZY_YVEC_PW YVL87_G 1 3; `pc:num`; `read X30 s`]
   537 THEN
  ARM_STEPS_TAC YVL87_EXEC (538--545) THEN
  MEXP_INPUT_TAC bf 2 3 `s545:armstate` THEN
  MEXP_HYP_TAC 2 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [546] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 547 THEN
  ARM_STEPS_TAC YVL87_EXEC (548--550) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 551 THEN
  ARM_STEPS_TAC YVL87_EXEC (552--555) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 2 2;
    MLD_LAZY_YVEC_PW YVL87_G 2 3; `pc:num`; `read X30 s`]
   556 THEN
  ARM_STEPS_TAC YVL87_EXEC (557--564) THEN
  MEXP_INPUT_TAC bf 3 3 `s564:armstate` THEN
  MEXP_HYP_TAC 3 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [565] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 566 THEN
  ARM_STEPS_TAC YVL87_EXEC (567--569) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 570 THEN
  ARM_STEPS_TAC YVL87_EXEC (571--574) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 3 2;
    MLD_LAZY_YVEC_PW YVL87_G 3 3; `pc:num`; `read X30 s`]
   575 THEN
  ARM_STEPS_TAC YVL87_EXEC (576--583) THEN
  MEXP_INPUT_TAC bf 4 3 `s583:armstate` THEN
  MEXP_HYP_TAC 4 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [584] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 585 THEN
  ARM_STEPS_TAC YVL87_EXEC (586--588) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 589 THEN
  ARM_STEPS_TAC YVL87_EXEC (590--593) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 4 2;
    MLD_LAZY_YVEC_PW YVL87_G 4 3; `pc:num`; `read X30 s`]
   594 THEN
  ARM_STEPS_TAC YVL87_EXEC (595--602) THEN
  MEXP_INPUT_TAC bf 5 3 `s602:armstate` THEN
  MEXP_HYP_TAC 5 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [603] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 604 THEN
  ARM_STEPS_TAC YVL87_EXEC (605--607) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 608 THEN
  ARM_STEPS_TAC YVL87_EXEC (609--612) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 5 2;
    MLD_LAZY_YVEC_PW YVL87_G 5 3; `pc:num`; `read X30 s`]
   613 THEN
  ARM_STEPS_TAC YVL87_EXEC (614--621) THEN
  MEXP_INPUT_TAC bf 6 3 `s621:armstate` THEN
  MEXP_HYP_TAC 6 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [622] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 6 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 623 THEN
  ARM_STEPS_TAC YVL87_EXEC (624--626) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 6 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 627 THEN
  ARM_STEPS_TAC YVL87_EXEC (628--631) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 6 2;
    MLD_LAZY_YVEC_PW YVL87_G 6 3; `pc:num`; `read X30 s`]
   632 THEN
  ARM_STEPS_TAC YVL87_EXEC (633--640) THEN
  MEXP_INPUT_TAC bf 7 3 `s640:armstate` THEN
  MEXP_HYP_TAC 7 3 THEN
  ARM_STEPS_TAC YVL87_EXEC [641] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 7 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 642 THEN
  ARM_STEPS_TAC YVL87_EXEC (643--645) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 7 3;
    MLD_LAZY_YVEC_YHAT YVL87_G 3;
    `pc:num`; `read X30 s`] 646 THEN
  ARM_STEPS_TAC YVL87_EXEC (647--650) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 7 2;
    MLD_LAZY_YVEC_PW YVL87_G 7 3; `pc:num`; `read X30 s`]
   651 THEN
  ARM_STEPS_TAC YVL87_EXEC (652--664) THEN
  YVL87_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 665 THEN
  MLD_LAZY_YVEC_Y_TAC YVL87_G 4 THEN
  ARM_STEPS_TAC YVL87_EXEC (666--667) THEN
  YVL87_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL87_G 4;
    `pc:num`; `read X30 s`] 668 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL87_G 4 THEN
  ARM_STEPS_TAC YVL87_EXEC (669--674) THEN
  MEXP_INPUT_TAC bf 0 4 `s674:armstate` THEN
  MEXP_HYP_TAC 0 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [675] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 676 THEN
  ARM_STEPS_TAC YVL87_EXEC (677--679) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 680 THEN
  ARM_STEPS_TAC YVL87_EXEC (681--684) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 0 3;
    MLD_LAZY_YVEC_PW YVL87_G 0 4; `pc:num`; `read X30 s`]
   685 THEN
  ARM_STEPS_TAC YVL87_EXEC (686--693) THEN
  MEXP_INPUT_TAC bf 1 4 `s693:armstate` THEN
  MEXP_HYP_TAC 1 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [694] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 695 THEN
  ARM_STEPS_TAC YVL87_EXEC (696--698) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 699 THEN
  ARM_STEPS_TAC YVL87_EXEC (700--703) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 1 3;
    MLD_LAZY_YVEC_PW YVL87_G 1 4; `pc:num`; `read X30 s`]
   704 THEN
  ARM_STEPS_TAC YVL87_EXEC (705--712) THEN
  MEXP_INPUT_TAC bf 2 4 `s712:armstate` THEN
  MEXP_HYP_TAC 2 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [713] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 714 THEN
  ARM_STEPS_TAC YVL87_EXEC (715--717) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 718 THEN
  ARM_STEPS_TAC YVL87_EXEC (719--722) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 2 3;
    MLD_LAZY_YVEC_PW YVL87_G 2 4; `pc:num`; `read X30 s`]
   723 THEN
  ARM_STEPS_TAC YVL87_EXEC (724--731) THEN
  MEXP_INPUT_TAC bf 3 4 `s731:armstate` THEN
  MEXP_HYP_TAC 3 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [732] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 733 THEN
  ARM_STEPS_TAC YVL87_EXEC (734--736) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 737 THEN
  ARM_STEPS_TAC YVL87_EXEC (738--741) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 3 3;
    MLD_LAZY_YVEC_PW YVL87_G 3 4; `pc:num`; `read X30 s`]
   742 THEN
  ARM_STEPS_TAC YVL87_EXEC (743--750) THEN
  MEXP_INPUT_TAC bf 4 4 `s750:armstate` THEN
  MEXP_HYP_TAC 4 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [751] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 752 THEN
  ARM_STEPS_TAC YVL87_EXEC (753--755) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 756 THEN
  ARM_STEPS_TAC YVL87_EXEC (757--760) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 4 3;
    MLD_LAZY_YVEC_PW YVL87_G 4 4; `pc:num`; `read X30 s`]
   761 THEN
  ARM_STEPS_TAC YVL87_EXEC (762--769) THEN
  MEXP_INPUT_TAC bf 5 4 `s769:armstate` THEN
  MEXP_HYP_TAC 5 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [770] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 771 THEN
  ARM_STEPS_TAC YVL87_EXEC (772--774) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 775 THEN
  ARM_STEPS_TAC YVL87_EXEC (776--779) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 5 3;
    MLD_LAZY_YVEC_PW YVL87_G 5 4; `pc:num`; `read X30 s`]
   780 THEN
  ARM_STEPS_TAC YVL87_EXEC (781--788) THEN
  MEXP_INPUT_TAC bf 6 4 `s788:armstate` THEN
  MEXP_HYP_TAC 6 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [789] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 6 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 790 THEN
  ARM_STEPS_TAC YVL87_EXEC (791--793) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 6 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 794 THEN
  ARM_STEPS_TAC YVL87_EXEC (795--798) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 6 3;
    MLD_LAZY_YVEC_PW YVL87_G 6 4; `pc:num`; `read X30 s`]
   799 THEN
  ARM_STEPS_TAC YVL87_EXEC (800--807) THEN
  MEXP_INPUT_TAC bf 7 4 `s807:armstate` THEN
  MEXP_HYP_TAC 7 4 THEN
  ARM_STEPS_TAC YVL87_EXEC [808] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 7 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 809 THEN
  ARM_STEPS_TAC YVL87_EXEC (810--812) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 7 4;
    MLD_LAZY_YVEC_YHAT YVL87_G 4;
    `pc:num`; `read X30 s`] 813 THEN
  ARM_STEPS_TAC YVL87_EXEC (814--817) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 7 3;
    MLD_LAZY_YVEC_PW YVL87_G 7 4; `pc:num`; `read X30 s`]
   818 THEN
  ARM_STEPS_TAC YVL87_EXEC (819--831) THEN
  YVL87_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 832 THEN
  MLD_LAZY_YVEC_Y_TAC YVL87_G 5 THEN
  ARM_STEPS_TAC YVL87_EXEC (833--834) THEN
  YVL87_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL87_G 5;
    `pc:num`; `read X30 s`] 835 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL87_G 5 THEN
  ARM_STEPS_TAC YVL87_EXEC (836--841) THEN
  MEXP_INPUT_TAC bf 0 5 `s841:armstate` THEN
  MEXP_HYP_TAC 0 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [842] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 843 THEN
  ARM_STEPS_TAC YVL87_EXEC (844--846) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 847 THEN
  ARM_STEPS_TAC YVL87_EXEC (848--851) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 0 4;
    MLD_LAZY_YVEC_PW YVL87_G 0 5; `pc:num`; `read X30 s`]
   852 THEN
  ARM_STEPS_TAC YVL87_EXEC (853--860) THEN
  MEXP_INPUT_TAC bf 1 5 `s860:armstate` THEN
  MEXP_HYP_TAC 1 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [861] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 862 THEN
  ARM_STEPS_TAC YVL87_EXEC (863--865) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 866 THEN
  ARM_STEPS_TAC YVL87_EXEC (867--870) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 1 4;
    MLD_LAZY_YVEC_PW YVL87_G 1 5; `pc:num`; `read X30 s`]
   871 THEN
  ARM_STEPS_TAC YVL87_EXEC (872--879) THEN
  MEXP_INPUT_TAC bf 2 5 `s879:armstate` THEN
  MEXP_HYP_TAC 2 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [880] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 881 THEN
  ARM_STEPS_TAC YVL87_EXEC (882--884) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 885 THEN
  ARM_STEPS_TAC YVL87_EXEC (886--889) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 2 4;
    MLD_LAZY_YVEC_PW YVL87_G 2 5; `pc:num`; `read X30 s`]
   890 THEN
  ARM_STEPS_TAC YVL87_EXEC (891--898) THEN
  MEXP_INPUT_TAC bf 3 5 `s898:armstate` THEN
  MEXP_HYP_TAC 3 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [899] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 900 THEN
  ARM_STEPS_TAC YVL87_EXEC (901--903) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 904 THEN
  ARM_STEPS_TAC YVL87_EXEC (905--908) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 3 4;
    MLD_LAZY_YVEC_PW YVL87_G 3 5; `pc:num`; `read X30 s`]
   909 THEN
  ARM_STEPS_TAC YVL87_EXEC (910--917) THEN
  MEXP_INPUT_TAC bf 4 5 `s917:armstate` THEN
  MEXP_HYP_TAC 4 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [918] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 919 THEN
  ARM_STEPS_TAC YVL87_EXEC (920--922) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 923 THEN
  ARM_STEPS_TAC YVL87_EXEC (924--927) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 4 4;
    MLD_LAZY_YVEC_PW YVL87_G 4 5; `pc:num`; `read X30 s`]
   928 THEN
  ARM_STEPS_TAC YVL87_EXEC (929--936) THEN
  MEXP_INPUT_TAC bf 5 5 `s936:armstate` THEN
  MEXP_HYP_TAC 5 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [937] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 938 THEN
  ARM_STEPS_TAC YVL87_EXEC (939--941) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 942 THEN
  ARM_STEPS_TAC YVL87_EXEC (943--946) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 5 4;
    MLD_LAZY_YVEC_PW YVL87_G 5 5; `pc:num`; `read X30 s`]
   947 THEN
  ARM_STEPS_TAC YVL87_EXEC (948--955) THEN
  MEXP_INPUT_TAC bf 6 5 `s955:armstate` THEN
  MEXP_HYP_TAC 6 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [956] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 6 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 957 THEN
  ARM_STEPS_TAC YVL87_EXEC (958--960) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 6 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 961 THEN
  ARM_STEPS_TAC YVL87_EXEC (962--965) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 6 4;
    MLD_LAZY_YVEC_PW YVL87_G 6 5; `pc:num`; `read X30 s`]
   966 THEN
  ARM_STEPS_TAC YVL87_EXEC (967--974) THEN
  MEXP_INPUT_TAC bf 7 5 `s974:armstate` THEN
  MEXP_HYP_TAC 7 5 THEN
  ARM_STEPS_TAC YVL87_EXEC [975] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 7 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 976 THEN
  ARM_STEPS_TAC YVL87_EXEC (977--979) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 7 5;
    MLD_LAZY_YVEC_YHAT YVL87_G 5;
    `pc:num`; `read X30 s`] 980 THEN
  ARM_STEPS_TAC YVL87_EXEC (981--984) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 7 4;
    MLD_LAZY_YVEC_PW YVL87_G 7 5; `pc:num`; `read X30 s`]
   985 THEN
  ARM_STEPS_TAC YVL87_EXEC (986--998) THEN
  YVL87_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 999 THEN
  MLD_LAZY_YVEC_Y_TAC YVL87_G 6 THEN
  ARM_STEPS_TAC YVL87_EXEC (1000--1001) THEN
  YVL87_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL87_G 6;
    `pc:num`; `read X30 s`] 1002 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL87_G 6 THEN
  ARM_STEPS_TAC YVL87_EXEC (1003--1008) THEN
  MEXP_INPUT_TAC bf 0 6 `s1008:armstate` THEN
  MEXP_HYP_TAC 0 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1009] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1010 THEN
  ARM_STEPS_TAC YVL87_EXEC (1011--1013) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1014 THEN
  ARM_STEPS_TAC YVL87_EXEC (1015--1018) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 0 5;
    MLD_LAZY_YVEC_PW YVL87_G 0 6; `pc:num`; `read X30 s`]
   1019 THEN
  ARM_STEPS_TAC YVL87_EXEC (1020--1027) THEN
  MEXP_INPUT_TAC bf 1 6 `s1027:armstate` THEN
  MEXP_HYP_TAC 1 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1028] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1029 THEN
  ARM_STEPS_TAC YVL87_EXEC (1030--1032) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1033 THEN
  ARM_STEPS_TAC YVL87_EXEC (1034--1037) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 1 5;
    MLD_LAZY_YVEC_PW YVL87_G 1 6; `pc:num`; `read X30 s`]
   1038 THEN
  ARM_STEPS_TAC YVL87_EXEC (1039--1046) THEN
  MEXP_INPUT_TAC bf 2 6 `s1046:armstate` THEN
  MEXP_HYP_TAC 2 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1047] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1048 THEN
  ARM_STEPS_TAC YVL87_EXEC (1049--1051) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1052 THEN
  ARM_STEPS_TAC YVL87_EXEC (1053--1056) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 2 5;
    MLD_LAZY_YVEC_PW YVL87_G 2 6; `pc:num`; `read X30 s`]
   1057 THEN
  ARM_STEPS_TAC YVL87_EXEC (1058--1065) THEN
  MEXP_INPUT_TAC bf 3 6 `s1065:armstate` THEN
  MEXP_HYP_TAC 3 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1066] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1067 THEN
  ARM_STEPS_TAC YVL87_EXEC (1068--1070) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1071 THEN
  ARM_STEPS_TAC YVL87_EXEC (1072--1075) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 3 5;
    MLD_LAZY_YVEC_PW YVL87_G 3 6; `pc:num`; `read X30 s`]
   1076 THEN
  ARM_STEPS_TAC YVL87_EXEC (1077--1084) THEN
  MEXP_INPUT_TAC bf 4 6 `s1084:armstate` THEN
  MEXP_HYP_TAC 4 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1085] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1086 THEN
  ARM_STEPS_TAC YVL87_EXEC (1087--1089) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1090 THEN
  ARM_STEPS_TAC YVL87_EXEC (1091--1094) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 4 5;
    MLD_LAZY_YVEC_PW YVL87_G 4 6; `pc:num`; `read X30 s`]
   1095 THEN
  ARM_STEPS_TAC YVL87_EXEC (1096--1103) THEN
  MEXP_INPUT_TAC bf 5 6 `s1103:armstate` THEN
  MEXP_HYP_TAC 5 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1104] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1105 THEN
  ARM_STEPS_TAC YVL87_EXEC (1106--1108) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1109 THEN
  ARM_STEPS_TAC YVL87_EXEC (1110--1113) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 5 5;
    MLD_LAZY_YVEC_PW YVL87_G 5 6; `pc:num`; `read X30 s`]
   1114 THEN
  ARM_STEPS_TAC YVL87_EXEC (1115--1122) THEN
  MEXP_INPUT_TAC bf 6 6 `s1122:armstate` THEN
  MEXP_HYP_TAC 6 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1123] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 6 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1124 THEN
  ARM_STEPS_TAC YVL87_EXEC (1125--1127) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 6 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1128 THEN
  ARM_STEPS_TAC YVL87_EXEC (1129--1132) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 6 5;
    MLD_LAZY_YVEC_PW YVL87_G 6 6; `pc:num`; `read X30 s`]
   1133 THEN
  ARM_STEPS_TAC YVL87_EXEC (1134--1141) THEN
  MEXP_INPUT_TAC bf 7 6 `s1141:armstate` THEN
  MEXP_HYP_TAC 7 6 THEN
  ARM_STEPS_TAC YVL87_EXEC [1142] THEN
  YVL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 7 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 1143 THEN
  ARM_STEPS_TAC YVL87_EXEC (1144--1146) THEN
  YVL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 7 6;
    MLD_LAZY_YVEC_YHAT YVL87_G 6;
    `pc:num`; `read X30 s`] 1147 THEN
  ARM_STEPS_TAC YVL87_EXEC (1148--1151) THEN
  YVL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL87_G 7 5;
    MLD_LAZY_YVEC_PW YVL87_G 7 6; `pc:num`; `read X30 s`]
   1152 THEN
  ARM_STEPS_TAC YVL87_EXEC (1153--1163) THEN
  MLD_LAZY_YVEC_JOIN_TAC YVL87_G 8 7 "s1163" THEN
  YVL87_CALL_TAC "H_VRED"
   [`read X0 s`; MLD_LAZY_YVEC_W YVL87_G 7; `pc:num`; `read SP s`;
    `read X30 s`] 1164 THEN
  ARM_STEPS_TAC YVL87_EXEC (1165--1166) THEN
  YVL87_CALL_TAC "H_VINV"
   [`read X0 s`; mk_comb(`mld_polyvec_map mld_poly_reduce`,
                         MLD_LAZY_YVEC_W YVL87_G 7);
    `pc:num`; `read SP s`; `read X30 s`] 1167 THEN
  ARM_STEPS_TAC YVL87_EXEC [1168] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL87_EXEC (1169--1180) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MLD_LAZY_YVEC_POST_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
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
   MLDSA_NATIVE_POLYVECK_REDUCE_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VRED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VINV" THEN
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
              fst YVL87_EXEC] THEN
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
    YVL87_CASE_TAC 1472;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    YVL87_CASE_TAC 1488]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
