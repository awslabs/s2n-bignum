(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of the inlined code of mldsa44_signature_internal       *)
(* (clang 23 -O3 monolithic reduced-RAM build): the instances of the         *)
(* generators of inline_sign*.ml at the loops and straight-line blocks of    *)
(* this function, for its proof (see signature_internal_44_spec.ml for the   *)
(* code): the two inlined poly_uniform_gamma1, the loops of the existing    *)
(* generators, polyveck_caddq, the sums of A y and of z, the subtraction and *)
(* the sum of the row loop, the four w1 pack blocks, the two polyeta_unpack  *)
(* regions, and the four w1 unpack loops and the four hint loops of          *)
(* pack_sig_h. Loading this file takes about half an hour natively (the two  *)
(* polyz_unpack loops and the polyeta regions take most of it).              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpackz.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_map.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_chknorm.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_gamma1.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_sig.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack_tac.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_polyeta.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hints_tac.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpackz.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack_sig.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_eta.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1unpack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hrow.ml";;

let SI44_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;
let SI44_L s = "mldsa44_signature_internal_" ^ s;;
let SI44_AT k = string_of_int (layout "mldsa44_signature_internal" + k);;

(* ------------------------------------------------------------------------- *)
(* The two inlined poly_uniform_gamma1 (y in A y with the index in x27, y in *)
(* z with the index in x21).                                                 *)
(* ------------------------------------------------------------------------- *)

let SI44_Z17_MODS =
  ["X0";"X1";"X2";"X3";"X4";"X5";"X6";"X7";"X8";"X9";"X10";"X11";"X12";"X13";
   "X14";"X15";"X16";"X17";"X18";"X19";
   "Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q16";"Q17";"Q18";"Q19"];;

let SI44_G1 (k,start,stop,jreg,sqz,sqzx,zl) =
  let tha = G1_A_PROVE SI44_MC (SI44_L start) (SI44_L sqz) jreg in
  let thsqz = G1_SQZ_PROVE SI44_MC
    (G1_EXEC_PLT (SI44_AT sqzx) (SI44_L (sqz ^ "_exit")))
    (SI44_L sqz) (SI44_L (sqz ^ "_exit")) ("X22","X26","X19","X20","X21")
    10192 10496 in
  let thz = INLINE_POLYZ17_GEN_LOOP SI44_MC
    (INLINE_LOOP_EXEC (SI44_L zl) (SI44_L (zl ^ "_exit")))
    (SI44_L zl) (SI44_L (zl ^ "_exit")) 17 0 133 ("X9","X23","X8")
    ("Q20","Q22","Q23","Q21") SI44_Z17_MODS ["Q5";"Q6";"Q7";"Q16"] in
  G1_MAIN_PROVE SI44_MC (SI44_L start) (SI44_L stop) jreg (tha,thsqz,thz);;

let SI44_G1_Y = SI44_G1 (1,"in_poly_uniform_gamma1_1","after_memset_1","X27",
                         "loop4",0x370,"loop5");;

let SI44_G1_Z = SI44_G1 (2,"in_poly_uniform_gamma1_2","after_memset_2","X21",
                         "loop30",0x34e0,"loop31");;

(* ------------------------------------------------------------------------- *)
(* The loops of the generators of inline_sign_arith.ml and inline_sign_pwm.ml *)
(* (reduce, chknorm, decompose, pointwise products), by their instance lists *)
(* there, as (label of the head, theorem).                                   *)
(* ------------------------------------------------------------------------- *)

let SI44_IS fn = fn = "mldsa44_signature_internal";;

let SI44_RED = map (fun ((_,_,hl,_,_,_) as x) -> hl, INLINE_REDUCE_OF_INSTANCE x)
  (filter (fun (_,fn,_,_,_,_) -> SI44_IS fn) INLINE_REDUCE_INSTANCES);;

let SI44_CHK = map (fun ((_,_,hl,_,_,_) as x) -> hl, INLINE_CHKNORM_OF_INSTANCE x)
  (filter (fun (_,fn,_,_,_,_) -> SI44_IS fn) INLINE_CHKNORM_INSTANCES);;

let SI44_DEC = map (fun ((_,hl,_,_,_,_) as x) -> hl, INLINE_DECOMPOSE_OF_INSTANCE x)
  (filter (fun (fn,_,_,_,_,_) -> SI44_IS fn) INLINE_DECOMPOSE_88_INSTANCES);;

let SI44_PWM =
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM4_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI44_IS fn) INLINE_PWM4_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM7_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI44_IS fn) INLINE_PWM7_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM6_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI44_IS fn) INLINE_PWM6_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM16_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI44_IS fn) INLINE_PWM16_INSTANCES);;

(*** polyveck_caddq: one loop per polynomial, the offset running on ***)

let SI44_CADDQ = map (fun (hl,k0) -> hl,
   INLINE_CADDQK_LOOP SI44_MC (INLINE_LOOP_EXEC (SI44_L hl) (SI44_L (hl ^ "_exit")))
    (SI44_L hl) (SI44_L (hl ^ "_exit")) k0 ["X9";"X19";"X8";"X10";"X11";"X12"])
  ["loop18",0; "loop19",1024; "loop20",2048; "loop21",3072];;

(*** The sums of A y (rows 0 to 3) ***)

let SI44_ADDS = map SI44_ADD_PROVE (0--3);;

(*** The sum z_i = (c s1)_i + y_i of the z loop ***)

let SI44_ZADD = SI44_ZADD_PROVE ();;

(*** The row loop: w0_j -= c s2_j ***)

let SI44_RSUB = SI44_RSUB_PROVE ();;

(*** The row loop: w0_j += c t0_j, with the counters of the loop ***)

let SI44_RADD = SI44_RADD_PROVE ();;

(*** polyw1_pack_88 of the four rows (after the decompose loops 22 to 25): ***)
(*** w1 at F + 9056 through x23, x21 = F + 9312 and x27 = F + 9568, the    ***)
(*** rows packed at F + 8288 + 192 i through x20 (row 0) and the pointer   ***)
(*** slots (the setup of the function stores F + 8288 + 48 m there). Each  ***)
(*** takes about 2 minutes.                                                 ***)

let SI44_W1IN =
  "read X23 s = word_add fp (word 9056) /\\ read X21 s = word_add fp (word 9312) /\\
   read X27 s = word_add fp (word 9568)";;

let SI44_SLOTS l = String.concat "" (map (fun (a,v) ->
  Printf.sprintf " /\\ read (memory :> bytes64 (word_add fp (word %d))) s = word_add fp (word %d)"
    a v) l);;

let SI44_W1PS_INSTS =
 [{ws_start = SI44_L "loop22_exit"; ws_stop = SI44_L "loop23"; ws_steps = 216;
   ws_in = 9056; ws_out = 8288;
   ws_pre = SI44_W1IN ^ " /\\ read X20 s = word_add fp (word 8288)" ^
            SI44_SLOTS [144,8336; 136,8384; 128,8432];
   ws_post = "read X8 s = word 0 /\\"; ws_spill = (640,96);
   ws_mods = ["X8";"X9";"X10";"X11"]};
  {ws_start = SI44_L "loop23_exit"; ws_stop = SI44_L "loop24"; ws_steps = 218;
   ws_in = 9056; ws_out = 8480;
   ws_pre = SI44_W1IN ^ SI44_SLOTS [184,8480; 120,8528; 112,8576; 104,8624];
   ws_post = "read X8 s = word 0 /\\ read X20 s = word_add fp (word 2144) /\\";
   ws_spill = (640,96); ws_mods = ["X8";"X9";"X10";"X11";"X20"]};
  {ws_start = SI44_L "loop24_exit"; ws_stop = SI44_L "loop25"; ws_steps = 217;
   ws_in = 9056; ws_out = 8672;
   ws_pre = SI44_W1IN ^ SI44_SLOTS [176,8672; 96,8720; 88,8768; 80,8816];
   ws_post = "read X8 s = word 0 /\\"; ws_spill = (640,96);
   ws_mods = ["X8";"X9";"X10";"X11"]};
  {ws_start = SI44_L "loop25_exit"; ws_stop = SI44_L "in_polyw1_pack_end";
   ws_steps = 238; ws_in = 9056; ws_out = 8864;
   ws_pre = SI44_W1IN ^ SI44_SLOTS [168,8864; 72,8912; 64,8960; 56,9008];
   ws_post = "read X0 s = word_add fp (word 10112) /\\ read X1 s = word 32 /\\
              read X3 s = word 64 /\\ read X4 s = word_add fp (word 8288) /\\
              read X5 s = word 768 /\\ read X6 s = word 0 /\\ read X7 s = word 0 /\\";
   ws_spill = (528,208);
   ws_mods = ["X0";"X1";"X3";"X4";"X5";"X6";"X7";"X8";"X9";"X10"]}];;

let SI44_W1PS = map (SI_W1PS_PROVE SI44_MC) SI44_W1PS_INSTS;;

(*** polyw1_unpack_88 of the four rows in pack_sig_h (loops 45, 47, 49, 51): ***)
(*** row 0 loads the TBL indices q0, q1 itself (shape A), the others use    ***)
(*** them (shape B); about a minute each.                                   ***)

let SI44_W1U_Q =
  ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";"Q10";"Q11";"Q16";"Q17";
   "Q18";"Q19";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q27";"Q28";"Q29";
   "Q30";"Q31"];;

let SI44_W1U_QB = filter (fun q -> q <> "Q0" && q <> "Q1") SI44_W1U_Q;;

let SI44_W1U_INSTS =
 [{wu_loop = SI44_L "loop45"; wu_exit = SI44_L "loop45_exit"; wu_shape = "A";
   wu_in = "X21"; wu_off = "X8"; wu_out = "X9";
   wu_mods = ["X8";"X9";"X10"] @ SI44_W1U_Q}, 68;
  {wu_loop = SI44_L "loop47"; wu_exit = SI44_L "loop47_exit"; wu_shape = "B";
   wu_in = "X12"; wu_off = "X9"; wu_out = "X10";
   wu_mods = ["X9";"X10";"X11"] @ SI44_W1U_QB}, 66;
  {wu_loop = SI44_L "loop49"; wu_exit = SI44_L "loop49_exit"; wu_shape = "B";
   wu_in = "X0"; wu_off = "X9"; wu_out = "X10";
   wu_mods = ["X9";"X10";"X11"] @ SI44_W1U_QB}, 66;
  {wu_loop = SI44_L "loop51"; wu_exit = SI44_L "loop51_exit"; wu_shape = "B";
   wu_in = "X1"; wu_off = "X9"; wu_out = "X10";
   wu_mods = ["X9";"X10";"X11"] @ SI44_W1U_QB}, 66];;

let SI44_W1U = map (fun (p,n) -> SI_W1U_PROVE SI44_MC p n) SI44_W1U_INSTS;;

(*** polyeta_unpack of s1_i in the z loop (from loop26 to the end of loop28, ***)
(*** a = [F + 800], r = F + 2144) and of s2_j in the row loop (from loop35   ***)
(*** to the end of loop37, a = [F + 736], r = F + 9056), each with its two   ***)
(*** scalar loop lemmas (groups 16 to 31 and 0 to 31). About 10 minutes each. ***)

let SI44_ETA_MODS =
  ["X0";"X8";"X9";"X10";"X11";"X12";"X13";"X14";"X15";"X16";"X17";"X18"];;

let SI44_ETA_Z =
  {et_start = SI44_L "loop26"; et_stop = SI44_L "in_polyeta_unpack_1_end";
   et_loop = SI44_L "loop28"; et_ireg = "X21"; et_kreg = "X27"; et_rreg = "X20";
   et_roff = 2144; et_aslot = 800; et_l = 4;
   et_pre = "read (memory :> bytes64 (word_add fp (word 232))) s =
               word_add fp (word 3168) /\\ read X1 s = zp /\\";
   et_post = "read (memory :> bytes64 (word_add fp (word 704))) s = zp /\\";
   et_bind = "(zp:int64)"; et_spill = [320,416]; et_mods = SI44_ETA_MODS};;

let SI44_ETA_R =
  {et_start = SI44_L "loop35"; et_stop = SI44_L "in_polyeta_unpack_2_end";
   et_loop = SI44_L "loop37"; et_ireg = "X21"; et_kreg = "X20"; et_rreg = "X23";
   et_roff = 9056; et_aslot = 736; et_l = 4;
   et_pre = String.concat "" (map (fun r ->
     "read " ^ r ^ " s = word_add (word pc) (word 245760) /\\ ")
     ["X14";"X15";"X16";"X17";"X18";"X0"]);
   et_post = ""; et_bind = "";
   et_spill = [272,16; 320,416]; et_mods = SI44_ETA_MODS};;

let SI44_ETA_Z_ST = {es_adrp = [5;6;7;8;9;10]; es_madd = 4; es_branch = 15;
                     es_ap = 16; es_block_end = 356; es_call_v = 363;
                     es_call_s = 21};;

let SI44_ETA_R_ST = {es_adrp = []; es_madd = 4; es_branch = 9; es_ap = 10;
                     es_block_end = 349; es_call_v = 355; es_call_s = 14};;

let SI44_ETA_ZL = map (fun g0 ->
  SI_ETA_L2_PROVE SI44_MC (SI44_L "loop28") (SI44_L "loop28_exit") g0
   ("X27","X20")) [16; 0];;

let SI44_ETA_RL = map (fun g0 ->
  SI_ETA_L2_PROVE SI44_MC (SI44_L "loop37") (SI44_L "loop37_exit") g0
   ("X20","X23")) [16; 0];;

let SI44_ETA_ZTH = SI_ETA_PROVE SI44_MC SI44_ETA_Z SI44_ETA_Z_ST
  (el 0 SI44_ETA_ZL, el 1 SI44_ETA_ZL);;

let SI44_ETA_RTH = SI_ETA_PROVE SI44_MC SI44_ETA_R SI44_ETA_R_ST
  (el 0 SI44_ETA_RL, el 1 SI44_ETA_RL);;

(*** The hint loops of pack_sig_h (loops 46, 48, 50 and 52), from the head ***)
(*** with j = 0 to the exit of the loop or to join9; seconds each.         ***)

let SI44_HROW = map SI_HROW_PROVE SI_HROW_INSTS;;

(*** polyt0_unpack of t0_j in the row loop (loop41) and polyz_pack of z_i ***)
(*** in the z loop (loop34), by the generators of inline_sign_pack.ml      ***)

let SI44_T0UNP = INLINE_POLYT0_LOOP SI44_MC
  (INLINE_LOOP_EXEC (SI44_L "loop41") (SI44_L "loop41_exit"))
  (SI44_L "loop41") (SI44_L "loop41_exit")
  ["X11";"X9";"X10";"X23";"X8";"X12";"X1";"X13";"X14";"X15";"X16";"X17";"X18";"X0"];;

let SI44_ZPACK = INLINE_POLYZ_PACK_17_LOOP SI44_MC
  (INLINE_LOOP_EXEC (SI44_L "loop34") (SI44_L "loop34_exit"))
  (SI44_L "loop34") (SI44_L "loop34_exit")
  ["X11";"X12";"X9";"X13";"X14";"X10";"X0";"X16";"X18";"X15";"X8";"X17"];;
