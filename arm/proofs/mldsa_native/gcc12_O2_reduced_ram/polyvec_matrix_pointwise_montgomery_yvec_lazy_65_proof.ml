(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = A y of signing, with A sampled on demand and y sampled    *)
(* polynomial by polynomial: the proof (see                                  *)
(* polyvec_matrix_pointwise_montgomery_yvec_lazy_65_spec.ml).                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let YVL65_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_EXEC;;

let YVL65_G = `mld_poly_uniform_gamma1_19`;;

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

let YVL65_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1503 1472 1488;;

let YVL65_ALLOWED =
  [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`; `r:num`;
   `rp:int64`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let YVL65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc YVL65_EXEC name
   ilist YVL65_ALLOWED n;;

let YVL65_CASE_TAC bf =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
      `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add mat (word 1024)) (word 16):int64 =
                          word_add mat (word 1040)`] THEN
  STRIP_TAC THEN MLD_LAZY_RBOUND_TAC "s0" THEN
  ARM_STEPS_TAC YVL65_EXEC (1--7) THEN
  MEXP_BUFFER_TAC YVL65_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC YVL65_EXEC (8--13) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL65_EXEC (14--27) THEN
  YVL65_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 28 THEN
  MLD_LAZY_YVEC_Y_TAC YVL65_G 0 THEN
  ARM_STEPS_TAC YVL65_EXEC (29--30) THEN
  YVL65_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL65_G 0;
    `pc:num`; `read X30 s`] 31 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL65_G 0 THEN
  ARM_STEPS_TAC YVL65_EXEC (32--37) THEN
  MEXP_INPUT_TAC bf 0 0 `s37:armstate` THEN
  MEXP_HYP_TAC 0 0 THEN
  ARM_STEPS_TAC YVL65_EXEC [38] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC YVL65_EXEC (40--43) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 0;
    MLD_LAZY_YVEC_YHAT YVL65_G 0;
    `pc:num`; `read X30 s`] 44 THEN
  ARM_STEPS_TAC YVL65_EXEC (45--52) THEN
  MEXP_INPUT_TAC bf 1 0 `s52:armstate` THEN
  MEXP_HYP_TAC 1 0 THEN
  ARM_STEPS_TAC YVL65_EXEC [53] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 54 THEN
  ARM_STEPS_TAC YVL65_EXEC (55--58) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 0;
    MLD_LAZY_YVEC_YHAT YVL65_G 0;
    `pc:num`; `read X30 s`] 59 THEN
  ARM_STEPS_TAC YVL65_EXEC (60--67) THEN
  MEXP_INPUT_TAC bf 2 0 `s67:armstate` THEN
  MEXP_HYP_TAC 2 0 THEN
  ARM_STEPS_TAC YVL65_EXEC [68] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 69 THEN
  ARM_STEPS_TAC YVL65_EXEC (70--73) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 0;
    MLD_LAZY_YVEC_YHAT YVL65_G 0;
    `pc:num`; `read X30 s`] 74 THEN
  ARM_STEPS_TAC YVL65_EXEC (75--82) THEN
  MEXP_INPUT_TAC bf 3 0 `s82:armstate` THEN
  MEXP_HYP_TAC 3 0 THEN
  ARM_STEPS_TAC YVL65_EXEC [83] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 84 THEN
  ARM_STEPS_TAC YVL65_EXEC (85--88) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 0;
    MLD_LAZY_YVEC_YHAT YVL65_G 0;
    `pc:num`; `read X30 s`] 89 THEN
  ARM_STEPS_TAC YVL65_EXEC (90--97) THEN
  MEXP_INPUT_TAC bf 4 0 `s97:armstate` THEN
  MEXP_HYP_TAC 4 0 THEN
  ARM_STEPS_TAC YVL65_EXEC [98] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 99 THEN
  ARM_STEPS_TAC YVL65_EXEC (100--103) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 0;
    MLD_LAZY_YVEC_YHAT YVL65_G 0;
    `pc:num`; `read X30 s`] 104 THEN
  ARM_STEPS_TAC YVL65_EXEC (105--112) THEN
  MEXP_INPUT_TAC bf 5 0 `s112:armstate` THEN
  MEXP_HYP_TAC 5 0 THEN
  ARM_STEPS_TAC YVL65_EXEC [113] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 114 THEN
  ARM_STEPS_TAC YVL65_EXEC (115--118) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 0;
    MLD_LAZY_YVEC_YHAT YVL65_G 0;
    `pc:num`; `read X30 s`] 119 THEN
  ARM_STEPS_TAC YVL65_EXEC (120--132) THEN
  YVL65_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 133 THEN
  MLD_LAZY_YVEC_Y_TAC YVL65_G 1 THEN
  ARM_STEPS_TAC YVL65_EXEC (134--135) THEN
  YVL65_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL65_G 1;
    `pc:num`; `read X30 s`] 136 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL65_G 1 THEN
  ARM_STEPS_TAC YVL65_EXEC (137--142) THEN
  MEXP_INPUT_TAC bf 0 1 `s142:armstate` THEN
  MEXP_HYP_TAC 0 1 THEN
  ARM_STEPS_TAC YVL65_EXEC [143] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 144 THEN
  ARM_STEPS_TAC YVL65_EXEC (145--147) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 1;
    MLD_LAZY_YVEC_YHAT YVL65_G 1;
    `pc:num`; `read X30 s`] 148 THEN
  ARM_STEPS_TAC YVL65_EXEC (149--152) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 0 0;
    MLD_LAZY_YVEC_PW YVL65_G 0 1; `pc:num`; `read X30 s`]
   153 THEN
  ARM_STEPS_TAC YVL65_EXEC (154--161) THEN
  MEXP_INPUT_TAC bf 1 1 `s161:armstate` THEN
  MEXP_HYP_TAC 1 1 THEN
  ARM_STEPS_TAC YVL65_EXEC [162] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 163 THEN
  ARM_STEPS_TAC YVL65_EXEC (164--166) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 1;
    MLD_LAZY_YVEC_YHAT YVL65_G 1;
    `pc:num`; `read X30 s`] 167 THEN
  ARM_STEPS_TAC YVL65_EXEC (168--171) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 1 0;
    MLD_LAZY_YVEC_PW YVL65_G 1 1; `pc:num`; `read X30 s`]
   172 THEN
  ARM_STEPS_TAC YVL65_EXEC (173--180) THEN
  MEXP_INPUT_TAC bf 2 1 `s180:armstate` THEN
  MEXP_HYP_TAC 2 1 THEN
  ARM_STEPS_TAC YVL65_EXEC [181] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 182 THEN
  ARM_STEPS_TAC YVL65_EXEC (183--185) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 1;
    MLD_LAZY_YVEC_YHAT YVL65_G 1;
    `pc:num`; `read X30 s`] 186 THEN
  ARM_STEPS_TAC YVL65_EXEC (187--190) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 2 0;
    MLD_LAZY_YVEC_PW YVL65_G 2 1; `pc:num`; `read X30 s`]
   191 THEN
  ARM_STEPS_TAC YVL65_EXEC (192--199) THEN
  MEXP_INPUT_TAC bf 3 1 `s199:armstate` THEN
  MEXP_HYP_TAC 3 1 THEN
  ARM_STEPS_TAC YVL65_EXEC [200] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 201 THEN
  ARM_STEPS_TAC YVL65_EXEC (202--204) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 1;
    MLD_LAZY_YVEC_YHAT YVL65_G 1;
    `pc:num`; `read X30 s`] 205 THEN
  ARM_STEPS_TAC YVL65_EXEC (206--209) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 3 0;
    MLD_LAZY_YVEC_PW YVL65_G 3 1; `pc:num`; `read X30 s`]
   210 THEN
  ARM_STEPS_TAC YVL65_EXEC (211--218) THEN
  MEXP_INPUT_TAC bf 4 1 `s218:armstate` THEN
  MEXP_HYP_TAC 4 1 THEN
  ARM_STEPS_TAC YVL65_EXEC [219] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 220 THEN
  ARM_STEPS_TAC YVL65_EXEC (221--223) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 1;
    MLD_LAZY_YVEC_YHAT YVL65_G 1;
    `pc:num`; `read X30 s`] 224 THEN
  ARM_STEPS_TAC YVL65_EXEC (225--228) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 4 0;
    MLD_LAZY_YVEC_PW YVL65_G 4 1; `pc:num`; `read X30 s`]
   229 THEN
  ARM_STEPS_TAC YVL65_EXEC (230--237) THEN
  MEXP_INPUT_TAC bf 5 1 `s237:armstate` THEN
  MEXP_HYP_TAC 5 1 THEN
  ARM_STEPS_TAC YVL65_EXEC [238] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 239 THEN
  ARM_STEPS_TAC YVL65_EXEC (240--242) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 1;
    MLD_LAZY_YVEC_YHAT YVL65_G 1;
    `pc:num`; `read X30 s`] 243 THEN
  ARM_STEPS_TAC YVL65_EXEC (244--247) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 5 0;
    MLD_LAZY_YVEC_PW YVL65_G 5 1; `pc:num`; `read X30 s`]
   248 THEN
  ARM_STEPS_TAC YVL65_EXEC (249--261) THEN
  YVL65_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 262 THEN
  MLD_LAZY_YVEC_Y_TAC YVL65_G 2 THEN
  ARM_STEPS_TAC YVL65_EXEC (263--264) THEN
  YVL65_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL65_G 2;
    `pc:num`; `read X30 s`] 265 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL65_G 2 THEN
  ARM_STEPS_TAC YVL65_EXEC (266--271) THEN
  MEXP_INPUT_TAC bf 0 2 `s271:armstate` THEN
  MEXP_HYP_TAC 0 2 THEN
  ARM_STEPS_TAC YVL65_EXEC [272] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 273 THEN
  ARM_STEPS_TAC YVL65_EXEC (274--276) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 2;
    MLD_LAZY_YVEC_YHAT YVL65_G 2;
    `pc:num`; `read X30 s`] 277 THEN
  ARM_STEPS_TAC YVL65_EXEC (278--281) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 0 1;
    MLD_LAZY_YVEC_PW YVL65_G 0 2; `pc:num`; `read X30 s`]
   282 THEN
  ARM_STEPS_TAC YVL65_EXEC (283--290) THEN
  MEXP_INPUT_TAC bf 1 2 `s290:armstate` THEN
  MEXP_HYP_TAC 1 2 THEN
  ARM_STEPS_TAC YVL65_EXEC [291] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 292 THEN
  ARM_STEPS_TAC YVL65_EXEC (293--295) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 2;
    MLD_LAZY_YVEC_YHAT YVL65_G 2;
    `pc:num`; `read X30 s`] 296 THEN
  ARM_STEPS_TAC YVL65_EXEC (297--300) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 1 1;
    MLD_LAZY_YVEC_PW YVL65_G 1 2; `pc:num`; `read X30 s`]
   301 THEN
  ARM_STEPS_TAC YVL65_EXEC (302--309) THEN
  MEXP_INPUT_TAC bf 2 2 `s309:armstate` THEN
  MEXP_HYP_TAC 2 2 THEN
  ARM_STEPS_TAC YVL65_EXEC [310] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 311 THEN
  ARM_STEPS_TAC YVL65_EXEC (312--314) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 2;
    MLD_LAZY_YVEC_YHAT YVL65_G 2;
    `pc:num`; `read X30 s`] 315 THEN
  ARM_STEPS_TAC YVL65_EXEC (316--319) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 2 1;
    MLD_LAZY_YVEC_PW YVL65_G 2 2; `pc:num`; `read X30 s`]
   320 THEN
  ARM_STEPS_TAC YVL65_EXEC (321--328) THEN
  MEXP_INPUT_TAC bf 3 2 `s328:armstate` THEN
  MEXP_HYP_TAC 3 2 THEN
  ARM_STEPS_TAC YVL65_EXEC [329] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 330 THEN
  ARM_STEPS_TAC YVL65_EXEC (331--333) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 2;
    MLD_LAZY_YVEC_YHAT YVL65_G 2;
    `pc:num`; `read X30 s`] 334 THEN
  ARM_STEPS_TAC YVL65_EXEC (335--338) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 3 1;
    MLD_LAZY_YVEC_PW YVL65_G 3 2; `pc:num`; `read X30 s`]
   339 THEN
  ARM_STEPS_TAC YVL65_EXEC (340--347) THEN
  MEXP_INPUT_TAC bf 4 2 `s347:armstate` THEN
  MEXP_HYP_TAC 4 2 THEN
  ARM_STEPS_TAC YVL65_EXEC [348] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 349 THEN
  ARM_STEPS_TAC YVL65_EXEC (350--352) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 2;
    MLD_LAZY_YVEC_YHAT YVL65_G 2;
    `pc:num`; `read X30 s`] 353 THEN
  ARM_STEPS_TAC YVL65_EXEC (354--357) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 4 1;
    MLD_LAZY_YVEC_PW YVL65_G 4 2; `pc:num`; `read X30 s`]
   358 THEN
  ARM_STEPS_TAC YVL65_EXEC (359--366) THEN
  MEXP_INPUT_TAC bf 5 2 `s366:armstate` THEN
  MEXP_HYP_TAC 5 2 THEN
  ARM_STEPS_TAC YVL65_EXEC [367] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 368 THEN
  ARM_STEPS_TAC YVL65_EXEC (369--371) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 2;
    MLD_LAZY_YVEC_YHAT YVL65_G 2;
    `pc:num`; `read X30 s`] 372 THEN
  ARM_STEPS_TAC YVL65_EXEC (373--376) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 5 1;
    MLD_LAZY_YVEC_PW YVL65_G 5 2; `pc:num`; `read X30 s`]
   377 THEN
  ARM_STEPS_TAC YVL65_EXEC (378--390) THEN
  YVL65_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 391 THEN
  MLD_LAZY_YVEC_Y_TAC YVL65_G 3 THEN
  ARM_STEPS_TAC YVL65_EXEC (392--393) THEN
  YVL65_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL65_G 3;
    `pc:num`; `read X30 s`] 394 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL65_G 3 THEN
  ARM_STEPS_TAC YVL65_EXEC (395--400) THEN
  MEXP_INPUT_TAC bf 0 3 `s400:armstate` THEN
  MEXP_HYP_TAC 0 3 THEN
  ARM_STEPS_TAC YVL65_EXEC [401] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 402 THEN
  ARM_STEPS_TAC YVL65_EXEC (403--405) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 3;
    MLD_LAZY_YVEC_YHAT YVL65_G 3;
    `pc:num`; `read X30 s`] 406 THEN
  ARM_STEPS_TAC YVL65_EXEC (407--410) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 0 2;
    MLD_LAZY_YVEC_PW YVL65_G 0 3; `pc:num`; `read X30 s`]
   411 THEN
  ARM_STEPS_TAC YVL65_EXEC (412--419) THEN
  MEXP_INPUT_TAC bf 1 3 `s419:armstate` THEN
  MEXP_HYP_TAC 1 3 THEN
  ARM_STEPS_TAC YVL65_EXEC [420] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 421 THEN
  ARM_STEPS_TAC YVL65_EXEC (422--424) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 3;
    MLD_LAZY_YVEC_YHAT YVL65_G 3;
    `pc:num`; `read X30 s`] 425 THEN
  ARM_STEPS_TAC YVL65_EXEC (426--429) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 1 2;
    MLD_LAZY_YVEC_PW YVL65_G 1 3; `pc:num`; `read X30 s`]
   430 THEN
  ARM_STEPS_TAC YVL65_EXEC (431--438) THEN
  MEXP_INPUT_TAC bf 2 3 `s438:armstate` THEN
  MEXP_HYP_TAC 2 3 THEN
  ARM_STEPS_TAC YVL65_EXEC [439] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 440 THEN
  ARM_STEPS_TAC YVL65_EXEC (441--443) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 3;
    MLD_LAZY_YVEC_YHAT YVL65_G 3;
    `pc:num`; `read X30 s`] 444 THEN
  ARM_STEPS_TAC YVL65_EXEC (445--448) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 2 2;
    MLD_LAZY_YVEC_PW YVL65_G 2 3; `pc:num`; `read X30 s`]
   449 THEN
  ARM_STEPS_TAC YVL65_EXEC (450--457) THEN
  MEXP_INPUT_TAC bf 3 3 `s457:armstate` THEN
  MEXP_HYP_TAC 3 3 THEN
  ARM_STEPS_TAC YVL65_EXEC [458] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 459 THEN
  ARM_STEPS_TAC YVL65_EXEC (460--462) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 3;
    MLD_LAZY_YVEC_YHAT YVL65_G 3;
    `pc:num`; `read X30 s`] 463 THEN
  ARM_STEPS_TAC YVL65_EXEC (464--467) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 3 2;
    MLD_LAZY_YVEC_PW YVL65_G 3 3; `pc:num`; `read X30 s`]
   468 THEN
  ARM_STEPS_TAC YVL65_EXEC (469--476) THEN
  MEXP_INPUT_TAC bf 4 3 `s476:armstate` THEN
  MEXP_HYP_TAC 4 3 THEN
  ARM_STEPS_TAC YVL65_EXEC [477] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 478 THEN
  ARM_STEPS_TAC YVL65_EXEC (479--481) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 3;
    MLD_LAZY_YVEC_YHAT YVL65_G 3;
    `pc:num`; `read X30 s`] 482 THEN
  ARM_STEPS_TAC YVL65_EXEC (483--486) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 4 2;
    MLD_LAZY_YVEC_PW YVL65_G 4 3; `pc:num`; `read X30 s`]
   487 THEN
  ARM_STEPS_TAC YVL65_EXEC (488--495) THEN
  MEXP_INPUT_TAC bf 5 3 `s495:armstate` THEN
  MEXP_HYP_TAC 5 3 THEN
  ARM_STEPS_TAC YVL65_EXEC [496] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 497 THEN
  ARM_STEPS_TAC YVL65_EXEC (498--500) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 3;
    MLD_LAZY_YVEC_YHAT YVL65_G 3;
    `pc:num`; `read X30 s`] 501 THEN
  ARM_STEPS_TAC YVL65_EXEC (502--505) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 5 2;
    MLD_LAZY_YVEC_PW YVL65_G 5 3; `pc:num`; `read X30 s`]
   506 THEN
  ARM_STEPS_TAC YVL65_EXEC (507--519) THEN
  YVL65_CALL_TAC "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 520 THEN
  MLD_LAZY_YVEC_Y_TAC YVL65_G 4 THEN
  ARM_STEPS_TAC YVL65_EXEC (521--522) THEN
  YVL65_CALL_TAC "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL65_G 4;
    `pc:num`; `read X30 s`] 523 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL65_G 4 THEN
  ARM_STEPS_TAC YVL65_EXEC (524--529) THEN
  MEXP_INPUT_TAC bf 0 4 `s529:armstate` THEN
  MEXP_HYP_TAC 0 4 THEN
  ARM_STEPS_TAC YVL65_EXEC [530] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 0 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 531 THEN
  ARM_STEPS_TAC YVL65_EXEC (532--534) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 0 4;
    MLD_LAZY_YVEC_YHAT YVL65_G 4;
    `pc:num`; `read X30 s`] 535 THEN
  ARM_STEPS_TAC YVL65_EXEC (536--539) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 0 3;
    MLD_LAZY_YVEC_PW YVL65_G 0 4; `pc:num`; `read X30 s`]
   540 THEN
  ARM_STEPS_TAC YVL65_EXEC (541--548) THEN
  MEXP_INPUT_TAC bf 1 4 `s548:armstate` THEN
  MEXP_HYP_TAC 1 4 THEN
  ARM_STEPS_TAC YVL65_EXEC [549] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 1 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 550 THEN
  ARM_STEPS_TAC YVL65_EXEC (551--553) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 1 4;
    MLD_LAZY_YVEC_YHAT YVL65_G 4;
    `pc:num`; `read X30 s`] 554 THEN
  ARM_STEPS_TAC YVL65_EXEC (555--558) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 1 3;
    MLD_LAZY_YVEC_PW YVL65_G 1 4; `pc:num`; `read X30 s`]
   559 THEN
  ARM_STEPS_TAC YVL65_EXEC (560--567) THEN
  MEXP_INPUT_TAC bf 2 4 `s567:armstate` THEN
  MEXP_HYP_TAC 2 4 THEN
  ARM_STEPS_TAC YVL65_EXEC [568] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 2 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 569 THEN
  ARM_STEPS_TAC YVL65_EXEC (570--572) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 2 4;
    MLD_LAZY_YVEC_YHAT YVL65_G 4;
    `pc:num`; `read X30 s`] 573 THEN
  ARM_STEPS_TAC YVL65_EXEC (574--577) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 2 3;
    MLD_LAZY_YVEC_PW YVL65_G 2 4; `pc:num`; `read X30 s`]
   578 THEN
  ARM_STEPS_TAC YVL65_EXEC (579--586) THEN
  MEXP_INPUT_TAC bf 3 4 `s586:armstate` THEN
  MEXP_HYP_TAC 3 4 THEN
  ARM_STEPS_TAC YVL65_EXEC [587] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 3 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 588 THEN
  ARM_STEPS_TAC YVL65_EXEC (589--591) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 3 4;
    MLD_LAZY_YVEC_YHAT YVL65_G 4;
    `pc:num`; `read X30 s`] 592 THEN
  ARM_STEPS_TAC YVL65_EXEC (593--596) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 3 3;
    MLD_LAZY_YVEC_PW YVL65_G 3 4; `pc:num`; `read X30 s`]
   597 THEN
  ARM_STEPS_TAC YVL65_EXEC (598--605) THEN
  MEXP_INPUT_TAC bf 4 4 `s605:armstate` THEN
  MEXP_HYP_TAC 4 4 THEN
  ARM_STEPS_TAC YVL65_EXEC [606] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 4 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 607 THEN
  ARM_STEPS_TAC YVL65_EXEC (608--610) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 4 4;
    MLD_LAZY_YVEC_YHAT YVL65_G 4;
    `pc:num`; `read X30 s`] 611 THEN
  ARM_STEPS_TAC YVL65_EXEC (612--615) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 4 3;
    MLD_LAZY_YVEC_PW YVL65_G 4 4; `pc:num`; `read X30 s`]
   616 THEN
  ARM_STEPS_TAC YVL65_EXEC (617--624) THEN
  MEXP_INPUT_TAC bf 5 4 `s624:armstate` THEN
  MEXP_HYP_TAC 5 4 THEN
  ARM_STEPS_TAC YVL65_EXEC [625] THEN
  YVL65_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r 5 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 626 THEN
  ARM_STEPS_TAC YVL65_EXEC (627--629) THEN
  YVL65_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ENTRY 5 4;
    MLD_LAZY_YVEC_YHAT YVL65_G 4;
    `pc:num`; `read X30 s`] 630 THEN
  ARM_STEPS_TAC YVL65_EXEC (631--634) THEN
  YVL65_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_YVEC_ACC YVL65_G 5 3;
    MLD_LAZY_YVEC_PW YVL65_G 5 4; `pc:num`; `read X30 s`]
   635 THEN
  ARM_STEPS_TAC YVL65_EXEC (636--646) THEN
  MLD_LAZY_YVEC_JOIN_TAC YVL65_G 6 5 "s646" THEN
  YVL65_CALL_TAC "H_VRED"
   [`read X0 s`; MLD_LAZY_YVEC_W YVL65_G 5; `pc:num`; `read SP s`;
    `read X30 s`] 647 THEN
  ARM_STEPS_TAC YVL65_EXEC (648--649) THEN
  YVL65_CALL_TAC "H_VINV"
   [`read X0 s`; mk_comb(`mld_polyvec_map mld_poly_reduce`,
                         MLD_LAZY_YVEC_W YVL65_G 5);
    `pc:num`; `read SP s`; `read X30 s`] 650 THEN
  ARM_STEPS_TAC YVL65_EXEC [651] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL65_EXEC (652--663) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MLD_LAZY_YVEC_POST_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
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
   MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VRED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VINV" THEN
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
              fst YVL65_EXEC] THEN
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
    YVL65_CASE_TAC 1472;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    YVL65_CASE_TAC 1488]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
