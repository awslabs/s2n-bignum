(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of the inlined code of mldsa65_signature_internal       *)
(* (clang 23 -O3 monolithic reduced-RAM build), for its proof as that of     *)
(* mldsa44_signature_internal (signature_internal_44_inline.ml): the loops   *)
(* whose instances the generators of inline_sign_pwm.ml, inline_sign_arith.ml *)
(* and inline_sign_pack.ml already list (the pointwise products, reduce, the *)
(* norm checks, the unpacking of t0), as (label of the head, theorem), and   *)
(* the instances of the generators of inline_sign6587.ml (the shapes of 65   *)
(* and 87) and of inline_sign_sig.ml / inline_sign_map.ml.                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pwm.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_gamma1.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_sig.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign6587.ml";;

let SI65_IS fn = fn = "mldsa65_signature_internal";;

let SI65_PWM =
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM4_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI65_IS fn) INLINE_PWM4_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM7_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI65_IS fn) INLINE_PWM7_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM6_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI65_IS fn) INLINE_PWM6_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM16_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI65_IS fn) INLINE_PWM16_INSTANCES);;

let SI65_RED = map (fun ((_,_,hl,_,_,_) as x) -> hl, INLINE_REDUCE_OF_INSTANCE x)
  (filter (fun (_,fn,_,_,_,_) -> SI65_IS fn) INLINE_REDUCE_INSTANCES);;

let SI65_CHK = map (fun ((_,_,hl,_,_,_) as x) -> hl, INLINE_CHKNORM_OF_INSTANCE x)
  (filter (fun (_,fn,_,_,_,_) -> SI65_IS fn) INLINE_CHKNORM_INSTANCES);;

let SI65_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let SI65_LOOP prover (_,hl,ex,rs) = hl, prover SI65_MC (INLINE_LOOP_EXEC hl ex) hl ex rs;;

let SI65_T0UNP = map (SI65_LOOP INLINE_POLYT0_LOOP)
  (filter (fun (fn,_,_,_) -> SI65_IS fn) INLINE_POLYT0_INSTANCES);;

(* ------------------------------------------------------------------------- *)
(* The lemmas from the generators of inline_sign6587.ml (the shapes that 65  *)
(* and 87 share). The frame offsets are from fp = SP of the attempt loop:    *)
(* the rows of w at fp + 3904 + 1024 k (x24 = fp + 3904), w1 (the high      *)
(* parts) at fp + 10816 (x20), w1 packed at fp + 10048 + 128 k, the y of a  *)
(* column at fp + 10816, the SHAKE256 state at fp + 12256 (y) and fp + 11936 *)
(* (z), the squeeze buffer at fp + 10048 (y) and fp + 12256 (z).             *)
(* ------------------------------------------------------------------------- *)

let SI65_L s = "mldsa65_signature_internal_" ^ s;;
let SI65_AT k = string_of_int (layout "mldsa65_signature_internal" + k);;

(*** polyveck_caddq: rows 0 to 3 with the byte offset in x8, rows 4 and 5 ***)
(*** with the coefficient index                                          ***)

let SI65_CADDQ = map (fun (hl,k0) -> hl,
   INLINE_CADDQK_LOOP SI65_MC (INLINE_LOOP_EXEC (SI65_L hl) (SI65_L (hl ^ "_exit")))
    (SI65_L hl) (SI65_L (hl ^ "_exit")) k0 ["X9";"X24";"X8";"X10";"X11";"X12"])
  ["loop24",0; "loop25",1024; "loop26",2048; "loop27",3072] @
  map (fun (hl,k0) -> hl,
   SG_CADDQI_LOOP SI65_MC (INLINE_LOOP_EXEC (SI65_L hl) (SI65_L (hl ^ "_exit")))
    (SI65_L hl) (SI65_L (hl ^ "_exit")) k0 ["X9";"X24";"X8";"X10";"X11";"X12"])
  ["loop28",4096; "loop29",5120];;

(*** poly_decompose of row k (loops 30 to 35), w at x24, w1 at x20 ***)

let SI65_DEC = map (fun k ->
  let hl = SI65_L ("loop" ^ string_of_int (30 + k)) in
  let el = hl ^ "_exit" in
  hl, if k = 0 then
    SG_DEC32_LOOP "62" SI65_MC (INLINE_LOOP_EXEC hl el) hl el 0
      ["X9";"X24";"X8";"X10";"X20";"X13";"X23";"X11";"X0"] (6,"X10") (16,"X9")
  else
    SG_DEC32_LOOP "63" SI65_MC (INLINE_LOOP_EXEC hl el) hl el (1024 * k)
      ["X9";"X24";"X8";"X10";"X11";"X20";"X13";"X23";"X12";"X0"] (7,"X11") (19,"X10"))
  (0--5);;

(*** polyw1_pack_32 of row k after its decompose loop: w1 at fp + 10816    ***)
(*** through x20 and x14 .. x18 (fp + 10816 + 128 m), the packed row at    ***)
(*** fp + 10048 + 128 k; the last block also sets the arguments of the    ***)
(*** call of mld_H65 (c~ = H(mu || w1 packed))                              ***)

let SI65_W1IN =
  "read X20 s = word_add fp (word 10816) /\\ read X14 s = word_add fp (word 10944) /\\
   read X15 s = word_add fp (word 11072) /\\ read X16 s = word_add fp (word 11200) /\\
   read X17 s = word_add fp (word 11328) /\\ read X18 s = word_add fp (word 11456)";;

let SI65_W1PS = map (fun k ->
  let st = SI65_L ("loop" ^ string_of_int (30 + k) ^ "_exit") in
  SG_W1PS32_PROVE SI65_MC
   (if k < 5 then
     {w2_start = st; w2_stop = SI65_L ("loop" ^ string_of_int (31 + k));
      w2_steps = 181; w2_in = 10816; w2_out = 10048 + 128 * k; w2_pre = SI65_W1IN;
      w2_post = "read X8 s = word 0 /\\"; w2_spill = [80,240; 384,16; 416,16];
      w2_mods = ["X8";"X9";"X10";"X11";"X12"]}
    else
     {w2_start = st; w2_stop = SI65_L "in_polyw1_pack_end";
      w2_steps = 191; w2_in = 10816; w2_out = 10688; w2_pre = SI65_W1IN;
      w2_post = "read X0 s = word_add fp (word 11872) /\\ read X1 s = word 48 /\\
                 read X2 s = word_add fp (word 1728) /\\ read X3 s = word 64 /\\
                 read X4 s = word_add fp (word 10048) /\\ read X5 s = word 768 /\\
                 read X6 s = word 0 /\\ read X7 s = word 0 /\\";
      w2_spill = [80,240; 384,16; 416,16];
      w2_mods = ["X0";"X1";"X2";"X3";"X4";"X5";"X6";"X7";"X8";"X9";"X10";"X11";"X12"]}))
  (0--5);;

(*** The hint loops of pack_sig_h (loops 55 to 60), w0 of row k through x25 ***)
(*** (row 0), x14 .. x17 (rows 1 to 4) or the slot fp + 344 (row 5), w1 of ***)
(*** the row unpacked at fp + 10816 (x20), the hints at sig + 3248 (x18)  ***)

let SI65_HROW_INSTS =
  map (fun (k,lp,lo,hi,wreg,slot) ->
    {hr3_fn = "mldsa65_signature_internal"; hr3_k = k; hr3_head = SI65_L lp;
     hr3_exit = SI65_L (lp ^ "_exit2"); hr3_lo = lo; hr3_hi = hi;
     hr3_wreg = wreg; hr3_woff = 3904 + 1024 * k; hr3_w1reg = "X20";
     hr3_w1off = 10816; hr3_hreg = "X18"; hr3_hoff = 3248; hr3_omega = 55;
     hr3_cregs = ("X13","X0","X24");
     hr3_mods = if k = 0 then "X8; X9; X10; X11" else "X8; X9; X10; X11; X12";
     hr3_slot = slot})
  [0,"loop55",0x5450,0x5488,"X25",[];
   1,"loop56",0x5884,0x58c8,"X14",[];
   2,"loop57",0x5c00,0x5c44,"X15",[];
   3,"loop58",0x5f7c,0x5fc0,"X16",[];
   4,"loop59",0x62f8,0x633c,"X17",[];
   5,"loop60",0x6674,0x66bc,"",[344,9024]];;

let SI65_HROW = map SG_HROW32_PROVE SI65_HROW_INSTS;;

(*** The inlined poly_uniform_gamma1 of the column loop of yvec_lazy (y_j, ***)
(*** nonce 5 att + j with 5 att at fp + 416 and j in x23, rho'' through   ***)
(*** the slot fp + 440, y_j to fp + 10816 = x20)                          ***)

let SI65_G1A_Y = SG_G1A_PROVE SI65_MC
  {ga_start = SI65_L "loop3"; ga_stop = SI65_L "loop4"; ga_steps = 65;
   ga_pre = "read (memory :> bytes32 (word_add sp (word 416))) s = word nb /\\
             read X23 s = word j /\\
             read (memory :> bytes64 (word_add sp (word 440))) s = rp /\\";
   ga_post = "read X27 s = word 680 /\\ read X24 s = word 136 /\\ read X25 s = word 0 /\\";
   ga_so = 12256; ga_io = 11936; ga_slots = [416,4; 440,8];
   ga_mods = ["X8";"X9";"X10";"X24";"X25";"X27"];
   ga_plan = [13,["nonce",12000];
              28,["split",12320; "split",12384; "split",12432; "zero16",12320];
              63,["split",12444]]};;

let SI65_SQZ_Y = G1_SQZ_PROVE SI65_MC
  (G1_EXEC_PLT (SI65_AT 0x33c) (SI65_L "loop4_exit"))
  (SI65_L "loop4") (SI65_L "loop4_exit") ("X27","X24","X25","X21","X22")
  12256 10048;;

let SI65_Z19_Y = SG_Z19S "mldsa65_signature_internal" "loop5" "X20";;

let SI65_G1_Y = SG_G1M_PROVE SI65_MC
  {gm_start = SI65_L "loop3"; gm_stop = SI65_L "after_memset_1"; gm_sqzx = 0x33c;
   gm_sqzl = SI65_L "loop4"; gm_sqz = ("X27","X24","X25","X21","X22");
   gm_zl = SI65_L "loop5";
   gm_io = 11936; gm_so = 12256; gm_bo = 10048; gm_zo = 10816;
   gm_slots = [408,8; 416,4; 440,8];
   gm_pre = "read (memory :> bytes32 (word_add fr (word 656))) s = word nb /\\
             read X23 s = word j /\\
             read (memory :> bytes64 (word_add fr (word 680))) s = rp /\\
             read (memory :> bytes64 (word_add fr (word 648))) s = word_add fr (word 10297) /\\
             read X20 s = word_add fr (word 11056) /\\";
   gm_post = "read X24 s = word_add fr (word 4144) /\\
              read X21 s = word_add fr (word 12176) /\\";
   gm_n1 = 7; gm_n2 = 21; gm_mods = ["X21";"X22";"X24";"X25";"X27"]}
  (SI65_G1A_Y,SI65_SQZ_Y,SI65_Z19_Y);;

(*** The inlined poly_uniform_gamma1 of the z loop (y_i, nonce 5 att + i ***)
(*** with 5 att at fp + 11848 (16 bits) and i in x25, rho'' in x8 after  ***)
(*** its load from fp + 11840, y_i to fp + 10816 = x20), from the load   ***)
(*** of the nonce to the return of the memset                            ***)

let SI65_G1A_Z = SG_G1A_PROVE SI65_MC
  {ga_start = SI65_AT 0x3bbc; ga_stop = SI65_L "loop40"; ga_steps = 56;
   ga_pre = "read X8 s = rp /\\ read X9 s = word_add sp (word 11840) /\\
             read (memory :> bytes16 (word_add sp (word 11848))) s = word nb /\\
             read X25 s = word j /\\ read Q7 s = word 0 /\\
             read X21 s = word_add sp (word 11936) /\\ read X23 s = word 0 /\\";
   ga_post = "read X25 s = word 680 /\\ read X24 s = word 136 /\\ read X23 s = word 0 /\\";
   ga_so = 11936; ga_io = 12160; ga_slots = [11848,2];
   ga_mods = ["X8";"X9";"X24";"X25"];
   ga_plan = [8,["nonce16",12224];
              16,["split",12000; "split",12064; "split",12112; "zero16",12000];
              54,["split",12124]]};;

let SI65_SQZ_Z = G1_SQZ_PROVE SI65_MC
  (G1_EXEC_PLT (SI65_AT 0x3c9c) (SI65_L "loop40_exit"))
  (SI65_L "loop40") (SI65_L "loop40_exit") ("X25","X24","X23","X21","X22")
  11936 12256;;

let SI65_Z19_Z = SG_Z19S "mldsa65_signature_internal" "loop41" "X20";;

let SI65_G1_Z = SG_G1M_PROVE SI65_MC
  {gm_start = SI65_AT 0x3bbc; gm_stop = SI65_L "after_memset_2"; gm_sqzx = 0x3c9c;
   gm_sqzl = SI65_L "loop40"; gm_sqz = ("X25","X24","X23","X21","X22");
   gm_zl = SI65_L "loop41";
   gm_io = 12160; gm_so = 11936; gm_bo = 12256; gm_zo = 10816;
   gm_slots = [352,8; 11848,2];
   gm_pre = "read X8 s = rp /\\ read X9 s = word_add fr (word 12080) /\\
             read (memory :> bytes16 (word_add fr (word 12088))) s = word nb /\\
             read X25 s = word j /\\ read Q7 s = word 0 /\\
             read X21 s = word_add fr (word 12176) /\\ read X23 s = word 0 /\\
             read (memory :> bytes64 (word_add fr (word 592))) s = word_add fr (word 12505) /\\
             read X20 s = word_add fr (word 11056) /\\";
   gm_post = "read X23 s = word_add (word pc) (word 245760) /\\
              read X25 s = word_add (word pc) (word 245760) /\\";
   gm_n1 = 6; gm_n2 = 21; gm_mods = ["X21";"X22";"X23";"X24";"X25"]}
  (SI65_G1A_Z,SI65_SQZ_Z,SI65_Z19_Z);;

(*** polyw1_unpack_32 of row k in pack_sig_h (straight-line, before the    ***)
(*** hint loop of the row): the packed row at fp + 10048 + 128 k, unpacked ***)
(*** to fp + 10816. Row 0 also copies c~ (fp + 11872) to sig, zeroes the   ***)
(*** hints (sig + 3248, 61 bytes) and loads the row pointers; rows 1 to 5  ***)
(*** store the count of the row before at sig + 3303 + k - 1.             ***)

let SI65_MASK = "word 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f";;

let SI65_SIGNOV (a,l) rs = String.concat "" (map (fun r -> Printf.sprintf
   "nonoverlapping (%s,%d) (%s) /\\ " a l r) rs);;

let SI65_W1U0 = SG_W1U32_PROVE SI65_MC
  {w3_start = SI65_L "loop45_exit1"; w3_stop = SI65_L "loop55"; w3_steps = 222;
   w3_in = 10048; w3_out = 10816;
   w3_bind = "(sig:int64) (c0:int128) (c1:int128) (c2:int128)";
   w3_nov = String.concat "" (map (fun r -> SI65_SIGNOV r
       ["word pc,libmldsa_size"; "word_add fp (word 16),56";
        "word_add fp (word 11872),48"; "word_add fp (word 10816),1024";
        "word_add fp (word 10048),128"])
      ["sig",48; "word_add sig (word 3248)",61]);
   w3_pre = "read Q17 s = " ^ SI65_MASK ^ " /\\
     read (memory :> bytes64 (word_add fp (word 64))) s = sig /\\
     read (memory :> bytes64 (word_add fp (word 16))) s = word_add sig (word 3248) /\\
     read (memory :> bytes64 (word_add fp (word 24))) s = word_add fp (word 8000) /\\
     read (memory :> bytes64 (word_add fp (word 32))) s = word_add fp (word 6976) /\\
     read (memory :> bytes64 (word_add fp (word 40))) s = word_add fp (word 5952) /\\
     read (memory :> bytes64 (word_add fp (word 48))) s = word_add fp (word 4928) /\\
     read (memory :> bytes128 (word_add fp (word 11872))) s = c0 /\\
     read (memory :> bytes128 (word_add fp (word 11888))) s = c1 /\\
     read (memory :> bytes128 (word_add fp (word 11904))) s = c2 /\\";
   w3_post = "read X8 s = word 0 /\\ read X9 s = word 0 /\\ read X10 s = sig /\\
     read X13 s = word 4294705408 /\\ read X0 s = word 261888 /\\
     read X14 s = word_add fp (word 4928) /\\ read X15 s = word_add fp (word 5952) /\\
     read X16 s = word_add fp (word 6976) /\\ read X17 s = word_add fp (word 8000) /\\
     read X18 s = word_add sig (word 3248) /\\ read X22 s = word_add fp (word 1856) /\\
     read Q18 s = " ^ SI65_MASK ^ " /\\
     read (memory :> bytes128 sig) s = c0 /\\
     read (memory :> bytes128 (word_add sig (word 16))) s = c1 /\\
     read (memory :> bytes128 (word_add sig (word 32))) s = c2 /\\
     (!t. t < 61 ==> read (memory :> bytes8 (word_add sig (word (3248 + t)))) s = word 0) /\\";
   w3_rd = ["word_add fp (word 16),56"; "word_add fp (word 11872),48"];
   w3_wr = ["sig,48"; "word_add sig (word 3248),61"];
   w3_ev = "(sig:int64)";
   w3_mods = ["X0";"X8";"X9";"X10";"X13";"X14";"X15";"X16";"X17";"X18";"X22"];
   w3_plan = [187,["word_add sig (word 3280)"];
              222,["word_add sig (word 3248)"; "word_add sig (word 3264)";
                   "word_add sig (word 3293)"]]};;

let SI65_W1UK = map (fun (k,st,sp,mq) ->
  let c = 3302 + k in
  SG_W1U32_PROVE SI65_MC
  {w3_start = SI65_L st; w3_stop = SI65_L sp; w3_steps = 206;
   w3_in = 10048 + 128 * k; w3_out = 10816; w3_bind = "(sig:int64) (cnt:num)";
   w3_nov = SI65_SIGNOV (Printf.sprintf "word_add sig (word %d)" c,1)
     ["word pc,libmldsa_size"; "word_add fp (word 64),8";
      "word_add fp (word 10816),1024";
      Printf.sprintf "word_add fp (word %d),128" (10048 + 128 * k)];
   w3_pre = "read Q18 s = " ^ SI65_MASK ^ " /\\ read X8 s = word cnt /\\
             read (memory :> bytes64 (word_add fp (word 64))) s = sig /\\";
   w3_post = Printf.sprintf
     "read X9 s = word 0 /\\ read X10 s = sig /\\ read X8 s = word cnt /\\ %s
      read (memory :> bytes8 (word_add sig (word %d))) s = word cnt /\\"
     (if mq = "" then "" else "read " ^ mq ^ " s = " ^ SI65_MASK ^ " /\\") c;
   w3_rd = ["word_add fp (word 64),8"];
   w3_wr = [Printf.sprintf "word_add sig (word %d),1" c];
   w3_ev = "(sig:int64)"; w3_mods = ["X9";"X10"]; w3_plan = []})
  [1,"loop55_exit2","loop56","Q18"; 2,"loop56_exit2","loop57","Q18";
   3,"loop57_exit2","loop58","Q18"; 4,"loop58_exit2","loop59","Q18";
   5,"loop59_exit2","loop60",""];;

(*** The sums of the columns j > 0 of A y: row i of w (fp + 3904 + 1024 i) ***)
(*** plus the product at fp + 544, with (rows 0 to 4) the setup of the     ***)
(*** next call of mldsa_poly_uniform (seed at fp + 12160, j and i + 1 at  ***)
(*** fp + 12192 and fp + 12193 through x21 = fp + 11936). Row 5 writes no  ***)
(*** X register; x8 is listed so that INLINE_MAPX_STMT's MAYCHANGE [PC; ..] ***)
(*** is not empty                                                           ***)

let SI65_ADD_RANGES = [0x610,0x9ec; 0xa74,0xe50; 0xed8,0x12b4; 0x133c,0x1718;
                       0x17a0,0x1b7c; 0x1c04,0x1fc8];;

let SI65_ADD i =
  let (a,b) = el i SI65_ADD_RANGES in
  let st = SI65_AT a and sp = SI65_AT b in
  let tm = INLINE_MAPX_STMT SI65_MC st sp
   ["x",3904 + 1024 * i; "y",544] (3904 + 1024 * i) "mld_poly_add x y i"
   544 (3904 + 1024 * (i + 1) - 544)
   ((if i < 5 then ["X0";"X1";"X8"] else ["X8"]) @ INLINE_MAP_QMODS)
   (if i < 5 then "(j:num)" else "")
   (if i < 5 then "read X21 s = word_add fp (word 11936) /\\ read X23 s = word j /\\"
    else "")
   (if i < 5 then Printf.sprintf
     "read X0 s = word_add fp (word 544) /\\
      read X1 s = word_add fp (word 12160) /\\ read X8 s = word %d /\\
      read (memory :> bytes8 (word_add fp (word 12192))) s = word_zx (word j:int64) /\\
      read (memory :> bytes8 (word_add fp (word 12193))) s = word %d /\\" (i + 1) (i + 1)
    else "")
   (if i < 5 then [12192,2] else []) in
  INLINE_MAPX_PROVE tm (INLINE_LOOP_EXEC st sp)
   ["x",3904 + 1024 * i; "y",544] ((b - a) / 4) [mld_poly_add] [WORD_ADD_SYM];;

let SI65_ADDS = map SI65_ADD (0--5);;

(*** z_i += y_i (after the memset of the z sampling, to the reduce loop): ***)
(*** z at fp + 1856, y_i at fp + 10816; the region also zeroes the input  ***)
(*** buffer of the sampling (fp + 12160, 66 bytes) and sets the registers ***)
(*** of the reduction and of the hint test (w24 = 2 gamma2 + 1)           ***)

let SI65_ZADD =
  let st = SI65_L "after_memset_2" and sp = SI65_L "loop42" in
  INLINE_MAPX_PROVE
   (INLINE_MAPX_STMT SI65_MC st sp ["x",1856; "y",10816] 1856 "mld_poly_add x y i"
     368 (11840 - 368) (["X8";"X9";"X21";"X22";"X24"] @ INLINE_MAP_QMODS) ""
     "read (memory :> bytes128 (word_add fp (word 368))) s =
        word 0xff801fffff801fffff801fffff801fff /\\"
     "read X8 s = word 0 /\\ read X21 s = word_add fp (word 11936) /\\
      read X22 s = word_add fp (word 1856) /\\ read X24 s = word 523777 /\\
      read Q4 s = word 0x00400000004000000040000000400000 /\\
      read Q5 s = word 0xff801fffff801fffff801fffff801fff /\\"
     [12160,66])
   (INLINE_LOOP_EXEC st sp) ["x",1856; "y",10816]
   ((layout sp - layout st) / 4) [mld_poly_add] [WORD_ADD_SYM];;

(*** The row loop: w0_j -= c s2_j (w0_j at x25 = fp + 3904 + 1024 j, which ***)
(*** the code computes at step 3), up to the reduce loop                  ***)

let SI65_RSUB_FIX wth =
  SUBGOAL_THEN `word_add (word_add fp (word 3904)) (word_shl (word j) 10):int64 = w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[wth] THEN UNDISCH_TAC `j < 6` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

let SI65_RSUB =
  let st = SI65_L "in_poly_sub" and sp = SI65_L "loop49" in
  INLINE_MAPP_PROVE
   (INLINE_MAPP_STMT SI65_MC st sp 10816 "mld_poly_sub x y i" 368 (11840 - 368)
     (["X8";"X9";"X25"] @ INLINE_MAP_QMODS) "(j:num) (p:int64)"
     "w = word_add fp (word (3904 + 1024 * j)) /\\ j < 6 /\\"
     "read X8 s = word_add fp (word 3904) /\\ read X22 s = word j /\\
      read X21 s = p /\\
      read (memory :> bytes128 (word_add fp (word 368))) s =
        word 0xff801fffff801fffff801fffff801fff /\\"
     "read X8 s = p /\\ read X9 s = word 256 /\\ read X25 s = w /\\
      read Q4 s = word 0x00400000004000000040000000400000 /\\
      read Q5 s = word 0xff801fffff801fffff801fffff801fff /\\"
     [] [368,16])
   (INLINE_LOOP_EXEC st sp) 10816 ((layout sp - layout st) / 4) 3 SI65_RSUB_FIX
   [mld_poly_sub] [];;

(*** The row loop: w0_j += c t0_j (w0_j at x25), up to the back edge, with  ***)
(*** the counters of the loop (x22 = j, x12 = 128 (j + 1), x21, x23, the  ***)
(*** t0 offset at fp + 416) and the constants of the next eta unpacking   ***)

let SI65_RADD =
  let st = SI65_L "in_poly_add_3" and sp = SI65_L "loop45_back" in
  SG_MAPP_PROVE 6
   (INLINE_MAPP_STMT SI65_MC st sp 10816 "mld_poly_add x y i" 416 (11840 - 416)
     (["X8";"X12";"X21";"X22";"X23";"X25"] @ INLINE_MAP_QMODS)
     "(j:num) (k:num) (h:int64) (p:int64)" "j < 6 /\\"
     "read X25 s = w /\\ read X22 s = word j /\\ read X27 s = word (128 * j) /\\
      read X21 s = p /\\ read X23 s = h /\\
      read (memory :> bytes64 (word_add fp (word 416))) s = word k /\\"
     ("read X22 s = word (j + 1) /\\ read X12 s = word (128 * j + 128) /\\
      read X21 s = word_add p (word 1024) /\\ read X23 s = word_add h (word 1024) /\\
      read (memory :> bytes64 (word_add fp (word 416))) s = word (k + 416) /\\
      read X25 s = word_add fp (word 3904) /\\
      read Q17 s = " ^ SI65_MASK ^ " /\\
      read Q16 s = word 0x00000004000000040000000400000004 /\\
      (read ZF s <=> j + 1 = 6) /\\")
     [416,8] [416,8])
   (INLINE_LOOP_EXEC st sp) 10816 ((layout sp - layout st) / 4) 0 (K ALL_TAC)
   [mld_poly_add] [WORD_ADD_SYM];;

(*** polyeta_unpack (eta = 4) of s1_i in the z loop (loop36 to join5, s1 at ***)
(*** [fp + 512], the output at fp + 1856 = x22) and of s2_j in the row loop ***)
(*** (loop45 to join7, s2 at [fp + 448], output fp + 10816 = x20): the     ***)
(*** vector loops (38, 47), the scalar loops (37, 46) and the regions      ***)

let SI65_ETA4V = map (fun (hl,regs) ->
  SG_ETA4V_LOOP SI65_MC (INLINE_LOOP_EXEC (SI65_L hl) (SI65_L (hl ^ "_exit")))
   (SI65_L hl) (SI65_L (hl ^ "_exit")) 0x3c5c0 regs
   ["X8";"X10";"X11";"X12";"Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7"])
  ["loop38",("X9",["X17";"X16";"X15";"X13"],"Q16","Q17");
   "loop47",("X9",["X18";"X17";"X16";"X15"],"Q17","Q16")];;

let SI65_PAGES rs = String.concat "" (map (fun r ->
  Printf.sprintf "read %s s = word_add (word pc) (word 245760) /\\ " r) rs);;

let SI65_ETA_Z = SG_ETA4C_PROVE SI65_MC
  {ec_start = SI65_L "loop36"; ec_stop = SI65_L "join5"; ec_ireg = "X25";
   ec_rreg = "X22"; ec_roff = 1856; ec_aslot = 512;
   ec_pre = "read (memory :> bytes64 (word_add fp (word 360))) s = word_add fp (word 2880) /\\";
   ec_post = "read (memory :> bytes64 (word_add fp (word 416))) s = word (128 * i) /\\";
   ec_wr = [416,8]; ec_rd = [360,8];
   ec_mods = ["X8";"X9";"X10";"X11";"X12";"X13";"X15";"X16";"X17"];
   ec_branch = 16; ec_adrp = [5;6;8;9]; ec_shl = 7; ec_ns = 1; ec_nv = 1}
  (el 0 SI65_ETA4V);;

let SI65_ETA_R = SG_ETA4C_PROVE SI65_MC
  {ec_start = SI65_L "loop45"; ec_stop = SI65_L "join7"; ec_ireg = "X22";
   ec_rreg = "X20"; ec_roff = 10816; ec_aslot = 448;
   ec_pre = "read Q17 s = " ^ SI65_MASK ^ " /\\
             read Q16 s = word 0x00000004000000040000000400000004 /\\ " ^
             SI65_PAGES ["X15";"X16";"X17";"X18"];
   ec_post = "read X27 s = word (128 * i) /\\";
   ec_wr = []; ec_rd = [];
   ec_mods = ["X8";"X9";"X10";"X11";"X12";"X27"];
   ec_branch = 10; ec_adrp = []; ec_shl = 4; ec_ns = 2; ec_nv = 1}
  (el 1 SI65_ETA4V);;

(*** polyz_pack_19 of z_i (fp + 1856) into the signature at x27 + 48 (x27 = ***)
(*** sig + 640 i), the constants of the TBLs through 17 page registers;    ***)
(*** about 8 minutes                                                       ***)

let SI65_ZPACK = SG_ZPACK19_PROVE SI65_MC
  {zp_start = SI65_L "loop44"; zp_stop = SI65_L "loop44_exit";
   zp_steps = 832; zp_in = 1856; zp_out = 48; zp_inreg = "X8"; zp_opreg = "X27";
   zp_offreg = "X9";
   zp_pages = ["X23";"X12";"X13";"X15";"X16";"X17";"X18";"X0";"X25";"X1";"X2";"X3";
               "X4";"X5";"X6";"X7";"X30"];
   zp_cd = 0x3c4b0; zp_ncd = 17; zp_q = "Q29";
   zp_post = "read X8 s = word_add fp (word 2880) /\\ read X9 s = word 688 /\\";
   zp_mods = ["X8";"X9";"X10";"X11";"Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";
              "Q16";"Q17";"Q18";"Q19";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q27";"Q28"]};;
