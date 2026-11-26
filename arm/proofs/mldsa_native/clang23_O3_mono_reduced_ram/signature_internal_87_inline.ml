(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of the inlined code of mldsa87_signature_internal       *)
(* (clang 23 -O3 monolithic reduced-RAM build), for its proof as that of     *)
(* mldsa44_signature_internal (signature_internal_44_inline.ml), as         *)
(* (label of the head, theorem) where there are several of a shape:         *)
(*                                                                           *)
(* - the loops whose instances the generators of inline_sign_pwm.ml and     *)
(*   inline_sign_arith.ml list (the pointwise products, reduce, the norm    *)
(*   checks) and the unpacking loop of t0 (inline_sign_pack.ml);            *)
(* - polyveck_caddq (rows 4 to 6 index the coefficients, SG_CADDQI_LOOP),   *)
(*   the eight sums of A y, the sum of the z loop and the subtraction and   *)
(*   the sum of the row loop (inline_sign_sig.ml);                           *)
(* - polyeta_unpack (eta = 2) of s1_i and s2_j (the generators of           *)
(*   inline_sign_eta.ml with the constant 2 in w0 and the constants loaded  *)
(*   from the image rather than the frame);                                  *)
(* - the rolled loop over the 8 rows that decomposes w and packs w1 (DW1R,  *)
(*   as x86's), with its decompose loop (SG_DEC32_LOOP of                   *)
(*   inline_sign6587.ml) and its packing block (as the w1 pack of verify);  *)
(* - c~ = H(mu || w1, 64), inlined with mu at fp + 1920 and w1 at           *)
(*   fp + 12288 (the tactics of inline_sign_shake_gen.ml);                  *)
(* - the two inlined poly_uniform_gamma1 (y of a column, y of the z loop); *)
(* - polyz_pack_19 of z_i (SG_ZPACK19_PROVE of inline_sign6587.ml);         *)
(* - pack_sig_h: the unpacking of w1 of each row (SG_W1U32_PROVE, row 0     *)
(*   with the copy of c~ and the zeroing of the hints) and the hint loops    *)
(*   of the rows (SG_HROW32_PROVE).                                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpackz.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_map.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_chknorm.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_gamma1.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_sig.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack_tac.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_polyeta.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hints_tac.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack_sig.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_eta.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1unpack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hrow.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pwm.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpackz19.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_usehint32.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack32.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_shake_gen.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_shake_stack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign6587.ml";;

let SI87_IS fn = fn = "mldsa87_signature_internal";;

let SI87_PWM =
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM4_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI87_IS fn) INLINE_PWM4_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM7_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI87_IS fn) INLINE_PWM7_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM6_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI87_IS fn) INLINE_PWM6_INSTANCES) @
  map (fun ((_,hl,_,_) as x) -> hl, INLINE_PWM16_OF_INSTANCE x)
    (filter (fun (fn,_,_,_) -> SI87_IS fn) INLINE_PWM16_INSTANCES);;

let SI87_RED = map (fun ((_,_,hl,_,_,_) as x) -> hl, INLINE_REDUCE_OF_INSTANCE x)
  (filter (fun (_,fn,_,_,_,_) -> SI87_IS fn) INLINE_REDUCE_INSTANCES);;

let SI87_CHK = map (fun ((_,_,hl,_,_,_) as x) -> hl, INLINE_CHKNORM_OF_INSTANCE x)
  (filter (fun (_,fn,_,_,_,_) -> SI87_IS fn) INLINE_CHKNORM_INSTANCES);;

let SI87_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let SI87_LOOP prover (_,hl,ex,rs) = hl, prover SI87_MC (INLINE_LOOP_EXEC hl ex) hl ex rs;;

let SI87_T0UNP = map (SI87_LOOP INLINE_POLYT0_LOOP)
  (filter (fun (fn,_,_,_) -> SI87_IS fn) INLINE_POLYT0_INSTANCES);;

let SI87_L s = "mldsa87_signature_internal_" ^ s;;
let SI87_AT k = string_of_int (layout "mldsa87_signature_internal" + k);;

(* ------------------------------------------------------------------------- *)
(* Straight-line code and loops of the 44 shapes at the 87 offsets.          *)
(* ------------------------------------------------------------------------- *)


(*** polyveck_caddq: loops 30 to 37; rows 4 to 6 (loops 34 to 36) index ***)
(*** the coefficients (ldrsw [x19, x8, lsl #2]), the others the bytes     ***)

let SI87_CADDQ_REGS = ["X9";"X19";"X8";"X10";"X11";"X12"];;

let SI87_CADDQ = map (fun (hl,k0) ->
  let ex = INLINE_LOOP_EXEC (SI87_L hl) (SI87_L (hl ^ "_exit")) in
  hl, (if k0 >= 4096 && k0 < 7168
       then SG_CADDQI_LOOP SI87_MC ex (SI87_L hl) (SI87_L (hl ^ "_exit")) k0 SI87_CADDQ_REGS
       else INLINE_CADDQK_LOOP SI87_MC ex (SI87_L hl) (SI87_L (hl ^ "_exit")) k0
              SI87_CADDQ_REGS))
  (map (fun i -> "loop" ^ string_of_int (30 + i), 1024 * i) (0--7));;

(*** The sums of A y (rows 0 to 7): row i of w at F + 4096 + 1024 i plus  ***)
(*** the product at F + 736, with the setup of the next poly_uniform for   ***)
(*** rows 0 to 6 (seed at F + 14368, indices at F + 14400 and F + 14401)   ***)

let SI87_ADD_EXTRA i =
  if i < 7 then
    Printf.sprintf
     "read X0 s = word_add fp (word 736) /\\
      read X1 s = word_add fp (word 14368) /\\
      read (memory :> bytes8 (word_add fp (word 14400))) s = word_zx (word j:int64) /\\
      read (memory :> bytes8 (word_add fp (word 14401))) s = word %d /\\" (i + 1)
  else "";;

let SI87_ADD_RANGES =
  [0x620,0xa14; 0xa9c,0xe90; 0xf18,0x130c; 0x1394,0x1788; 0x1810,0x1c04;
   0x1c8c,0x2080; 0x2108,0x24fc; 0x2584,0x2960];;

let SI87_ADD_TERM i (a,b) =
  INLINE_MAPX_STMT SI87_MC (SI87_AT a) (SI87_AT b)
   ["x",4096 + 1024 * i; "y",736] (4096 + 1024 * i) "mld_poly_add x y i"
   736 (4096 + 1024 * (i + 1) - 736)
   ((if i < 7 then ["X0";"X1";"X8"] else ["X8"]) @ INLINE_MAP_QMODS)
   (if i < 7 then "(j:num)" else "")
   (if i < 7 then "read X19 s = word j /\\ read X20 s = word_add fp (word 14336) /\\" else "")
   (SI87_ADD_EXTRA i)
   (if i < 7 then [14400,2] else []);;

let SI87_ADD_PROVE i =
  let (a,b) = el i SI87_ADD_RANGES in
  INLINE_MAPX_PROVE (SI87_ADD_TERM i (a,b))
   (INLINE_LOOP_EXEC (SI87_AT a) (SI87_AT b))
   ["x",4096 + 1024 * i; "y",736] ((b - a) / 4) [mld_poly_add] [WORD_ADD_SYM];;

let SI87_ADDS = map SI87_ADD_PROVE (0--7);;

(*** z_i += y_i (+0x4300..+0x470c): c s1_i at F + 2048, y_i at F + 13312, ***)
(*** with x25 reloaded from F + 184 and the constants of the reduction    ***)

let SI87_Q5 = "339618401959998730991157055895298383871";;

let SI87_ZADD_TERM =
  INLINE_MAPX_STMT SI87_MC (SI87_AT 0x4300) (SI87_AT 0x470c)
   ["x",2048; "y",13312] 2048 "mld_poly_add x y i" 184 (14336 - 184)
   ("X25"::INLINE_MAP_QMODS) "(q:int64)"
   ("read (memory :> bytes64 (word_add fp (word 184))) s = q /\\
     read (memory :> bytes128 (word_add fp (word 192))) s = word " ^ SI87_Q5 ^ " /\\")
   ("read X25 s = q /\\
     read Q4 s = word 0x00400000004000000040000000400000 /\\
     read Q5 s = word " ^ SI87_Q5 ^ " /\\")
   [];;

let SI87_ZADD = INLINE_MAPX_PROVE SI87_ZADD_TERM
   (INLINE_LOOP_EXEC (SI87_AT 0x4300) (SI87_AT 0x470c))
   ["x",2048; "y",13312] ((0x470c - 0x4300) / 4) [mld_poly_add] [WORD_ADD_SYM];;

(*** The row loop: w0_j -= c s2_j (+0x50b0..+0x53c8), w0_j at x20 =       ***)
(*** F + 4096 + 1024 j computed at step 4 from x23 = j; the region ends    ***)
(*** with the setup of the reduction (x8 from F + 208, q5 from F + 192)   ***)

let SI87_RSUB_TERM =
  INLINE_MAPP_STMT SI87_MC (SI87_AT 0x50b0) (SI87_AT 0x53c8)
   13312 "mld_poly_sub x y i" 192 (14336 - 192)
   ("X8"::"X9"::"X20"::INLINE_MAP_QMODS) "(j:num) (p:int64)"
   "w = word_add fp (word (4096 + 1024 * j)) /\\ j < 8 /\\"
   ("read X23 s = word j /\\
     read (memory :> bytes64 (word_add fp (word 208))) s = p /\\
     read (memory :> bytes128 (word_add fp (word 192))) s = word " ^ SI87_Q5 ^ " /\\")
   ("read X8 s = p /\\ read X9 s = word 256 /\\ read X20 s = w /\\
     read Q4 s = word 0x00400000004000000040000000400000 /\\
     read Q5 s = word " ^ SI87_Q5 ^ " /\\")
   [] [192,16; 208,8];;

let SI87_RSUB_FIX wth =
  SUBGOAL_THEN `word_add (word_add fp (word 4096)) (word_shl (word j) 10):int64 = w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[wth] THEN UNDISCH_TAC `j < 8` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

let SI87_RSUB = INLINE_MAPP_PROVE SI87_RSUB_TERM
   (INLINE_LOOP_EXEC (SI87_AT 0x50b0) (SI87_AT 0x53c8))
   13312 ((0x53c8 - 0x50b0) / 4) 4 SI87_RSUB_FIX [mld_poly_sub] [];;

(*** INLINE_MAPP_PROVE with ADRP steps (normalized after the step) ***)

let SI87_MAPP_PROVE tm exec yoff n adrps (defs:thm list) (lanes:thm list) =
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (w:int64) (pc:num). f_ev_map fp w pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN MAPP_INPUT_TAC `w:int64` `x:num->int32` THEN
  MAPP_INPUT_TAC (parse_term(Printf.sprintf "word_add fp (word %d):int64" yoff))
   `y:num->int32` THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC exec [k] THEN
                      (if mem k adrps then MLKEM_NATIVE_ADRP_TAC else ALL_TAC))
   (1--n) THEN
  WIDE_STORE_SPLIT_TAC `w:int64` 32 THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes128 (w:int64)) s = v`) (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                           (CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th))
    else NO_TAC)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC defs THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC lanes THEN NO_TAC) THEN
  TRY(W(fun (asl,w) -> if is_iff w && free_in `j:num` w &&
                          exists (fun (_,th) -> concl th = `j < 8`) asl
       then UNDISCH_TAC `j < 8` THEN SPEC_TAC(`j:num`,`j:num`) THEN
            CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
            CONV_TAC NUM_REDUCE_CONV THEN NO_TAC
       else NO_TAC)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** The row loop: w0_j += c t0_j (+0x56b8..+0x59fc, up to the back edge): ***)
(*** the counters of the loop advance (x23 = j, x19 = 96 j, x24, the       ***)
(*** pointers at F + 168 and F + 208) and the pages of the constants of    ***)
(*** the next polyeta_unpack are loaded (ADRP)                             ***)

let SI87_PAGE_REGS = ["X15";"X16";"X17";"X18";"X1";"X2";"X3"];;

let SI87_PAGES regs = String.concat "" (map (fun r ->
  "read " ^ r ^ " s = word_add (word pc) (word 245760) /\\ ") regs);;

let SI87_RADD_TERM =
  INLINE_MAPP_STMT SI87_MC (SI87_AT 0x56b8) (SI87_AT 0x59fc)
   13312 "mld_poly_add x y i" 168 (14336 - 168)
   (["X8";"X19";"X23";"X24"] @ SI87_PAGE_REGS @ INLINE_MAP_QMODS)
   "(j:num) (k:num) (h:int64) (p:int64) (q:int64)" "j < 8 /\\"
   "read X20 s = w /\\ read X23 s = word j /\\ read X19 s = word k /\\
    read X24 s = h /\\
    read (memory :> bytes64 (word_add fp (word 208))) s = p /\\
    read (memory :> bytes64 (word_add fp (word 168))) s = q /\\"
   ("read X23 s = word (j + 1) /\\ read X19 s = word (k + 96) /\\
     read X24 s = word_add h (word 1024) /\\
     read (memory :> bytes64 (word_add fp (word 208))) s = word_add p (word 1024) /\\
     read (memory :> bytes64 (word_add fp (word 168))) s = word_add q (word 416) /\\
     (read ZF s <=> j + 1 = 8) /\\ " ^ SI87_PAGES SI87_PAGE_REGS)
   [168,8; 208,8] [168,8; 208,8];;

let SI87_RADD = SI87_MAPP_PROVE SI87_RADD_TERM
   (INLINE_LOOP_EXEC (SI87_AT 0x56b8) (SI87_AT 0x59fc))
   13312 ((0x59fc - 0x56b8) / 4) [38;39;42;48;49;50;59]
   [mld_poly_add] [WORD_ADD_SYM];;

(* ------------------------------------------------------------------------- *)
(* polyeta_unpack (eta = 2) of s1_i and s2_j.                                *)
(* ------------------------------------------------------------------------- *)

(*** polyeta_unpack (eta = 2) of 87: inline_sign_eta.ml's generators with  ***)
(*** the constant 2 in creg (w0 in 87, w24 in 44), no TBL index slots in  ***)
(*** the frame (87 loads them from the constants) and the low end rdlo of ***)
(*** the frame reads as parameters, and ADRPs in the vector path           ***)

let SI87_ETA_L2_TERM creg mc loop exit g0 (kreg,rreg) =
  let n = 32 - g0 in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (r:int64) (a:int64) k (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (word_add r (word %d),%d))
            [(word pc,libmldsa_size); (word_add a (word k),96)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read X8 s = %s /\\
                  read X9 s = word %d /\\
                  read %s s = word k /\\ read %s s = r /\\
                  read %s s = word 2 /\\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word(k + j)))) s = b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  (!j. %sj < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                           mld_polyeta_unpack_2 b j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a k pc /\\
                     memaccess_inbounds e2 [word_add a (word k),96]
                                           [word_add r (word %d),%d]))
             (MAYCHANGE [PC; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
                         X18] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add r (word %d),%d)])"
   (32 * g0) (32 * n) mc loop
   (if g0 = 0 then "a" else Printf.sprintf "word_add a (word %d)" (3 * g0))
   (32 * g0 + 16) kreg rreg creg exit
   (if g0 = 0 then "" else Printf.sprintf "%d <= j /\\ " (8 * g0))
   (32 * g0) (32 * n) (32 * g0) (32 * n));;

let SI87_ETA_L2_INV creg g0 (kreg,rreg) =
  Printf.sprintf
   "\\i s. read X8 s = word_add a (word (3 * i%s)) /\\
          read X9 s = word (32 * i + %d) /\\
          read %s s = word k /\\ read %s s = r /\\ read %s s = word 2 /\\
          (!j. j < 96
               ==> read(memory :> bytes8(word_add a (word(k + j)))) s =
                   (b:num->byte) j) /\\
          (!j. %sj < 8 * i%s
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_polyeta_unpack_2 b j)"
   (if g0 = 0 then "" else Printf.sprintf " + %d" (3 * g0)) (32 * g0 + 16) kreg rreg creg
   (if g0 = 0 then "" else Printf.sprintf "%d <= j /\\ " (8 * g0))
   (if g0 = 0 then "" else Printf.sprintf " + %d" (8 * g0));;

let SI87_ETA_L2_PROVE creg mc loop exit g0 regs =
  let n = 32 - g0 in
  let ex = INLINE_LOOP_EXEC loop exit in
  prove(SI87_ETA_L2_TERM creg mc loop exit g0 regs,
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\(r:int64) (a:int64) (k:num) (pc:num).
        APPEND (f_ev_epil r a k pc)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop r a k pc i))
                 (f_ev_prol r a k pc)) :(uarch_event)list" n)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`; `k:num`;
                       `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_small_numeral n) (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (parse_term(SI87_ETA_L2_INV creg g0 regs)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `!n j. ~(n <= j /\ j < n)`; WORD_ADD_0; CONJUNCT1 LT] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    SI_ETA_L2_INPUT_TAC g0 THEN
    ARM_STEPS_TAC ex (1--2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SI_ETA_X12_EQ g0]) THEN
    ARM_STEPS_TAC ex (3--44) THEN
    SI_ETA_L2_FINAL_TAC g0;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;


let SI87_ETA_TERM mc p creg rdlo =
  let regs = (p.et_roff,1024) :: p.et_spill in
  let rl = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "(word_add fp (word %d),%d)" oo l) regs) in
  let ml = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "word_add fp (word %d),%d" oo l) regs) in
  let mcs = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "memory :> bytes(word_add fp (word %d),%d)" oo l) regs) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) (a:int64) i (b:num->byte) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\ i < %d /\\
        ALL (nonoverlapping (word_add a (word (96 * i)),96)) [%s] /\\
        ALL (nonoverlapping (word pc,libmldsa_size)) [%s]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = fp /\\
                  read %s s = word i /\\ read %s s = word (96 * i) /\\
                  read %s s = word_add fp (word %d) /\\
                  read %s s = word 2 /\\
                  read (memory :> bytes64 (word_add fp (word %d))) s = a /\\ %s
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word(96 * i + j)))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s
                  (!j. j < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * j)))) s =
                           mld_polyeta_unpack_2 b j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp a i pc /\\
                     memaccess_inbounds e2
                      [word_add a (word (96 * i)),96; word_add fp (word %d),%d;
                       word (pc + mldsa87_signature_internal_consts),400]
                      [%s]))
             (MAYCHANGE [PC; %s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                         Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                         Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [%s])"
   p.et_bind p.et_l rl rl mc p.et_start
   p.et_ireg p.et_kreg p.et_rreg p.et_roff creg p.et_aslot p.et_pre
   p.et_stop p.et_post p.et_roff rdlo (p.et_roff + 1024 - rdlo) ml
   (String.concat "; " p.et_mods) mcs);;

(*** SI_ETA_V_TAC with ADRPs (steps in st.es_adrp after the branch) ***)

let SI87_ETA_V_TAC p st ex =
  let roff = p.et_roff and be = st.es_block_end in
  let sb = "s" ^ string_of_int be in
  let adrp k = if mem k st.es_adrp then MLKEM_NATIVE_ADRP_TAC else ALL_TAC in
  let lowt = parse_term(Printf.sprintf
    "!j. j < 128 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * j)))) %s =
                     mld_polyeta_unpack_2 b j" roff sb) in
  MAP_EVERY (fun k -> ARM_STEPS_TAC ex [k] THEN adrp k THEN
                      (if k = st.es_ap then SI_ETA_AP_TAC else ALL_TAC))
   ((st.es_branch + 1)--(st.es_ap + 1)) THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC ex [k] THEN adrp k THEN ETA_NORM)
   ((st.es_ap + 2)--be) THEN
  SI_ETA_LANES_TAC roff (sb ^ ":armstate") THEN
  MAP_EVERY (fun j ->
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "read (memory :> bytes32 (word_add fp (word (%d + 4 * %d)))) %s =
       mld_polyeta_unpack_2 b %d" roff j sb j)) ASSUME_TAC THENL
     [SI_ETA_LANE_TAC; ALL_TAC]) (0--127) THEN
  SUBGOAL_THEN lowt ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if ETA_IS_LANE (concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if ETA_BIG_FACT (concl th) then ALL_TAC else NO_TAC)) THEN
  ARM_STEPS_TAC ex ((be + 1)--(st.es_call_v - 1));;

let SI87_ETA_PROVE mc p st creg rdlo (l16,l0) =
  let ex = INLINE_LOOP_EXEC p.et_start p.et_stop in
  let ov = parse_term(Printf.sprintf
    "val (ap:int64) < val (word_add fp (word %d):int64) /\\
     val (word_add fp (word %d):int64) < val (word_add ap (word 96):int64)"
    (p.et_roff + 1024) p.et_roff) in
  prove(SI87_ETA_TERM mc p creg rdlo,
    SI_ETA_SETUP_TAC p st ex (l16,l0) THEN
    ASM_CASES_TAC ov THEN
    FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                            REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
     [SI_ETA_S_TAC p st ex;
      SI87_ETA_V_TAC p st ex THEN SI_ETA_V_END_TAC p st ex]);;

(*** The instances: s1_i in the z loop (from loop43, a = [F + 704],        ***)
(*** r = F + 2048) and s2_j in the row loop (from loop52, a = [F + 640],    ***)
(*** r = F + 13312)                                                          ***)

let SI87_ETA_ZMODS =
  ["X1";"X2";"X3";"X8";"X9";"X10";"X11";"X12";"X13";"X14";"X15";"X16";"X17";
   "X18";"X22"];;

let SI87_ETA_RMODS =
  ["X8";"X9";"X10";"X11";"X12";"X13";"X14";"X15";"X16";"X17";"X18"];;

let SI87_ETA_Z =
  {et_start = SI87_L "loop43"; et_stop = SI87_L "in_polyeta_unpack_1_end";
   et_loop = SI87_L "loop45"; et_ireg = "X20"; et_kreg = "X19"; et_rreg = "X23";
   et_roff = 2048; et_aslot = 704; et_l = 7;
   et_pre = "read (memory :> bytes64 (word_add fp (word 176))) s =
               word_add fp (word 3072) /\\ read X25 s = zp /\\";
   et_post = "read (memory :> bytes64 (word_add fp (word 208))) s = zp /\\
              read X22 s = word_add fp (word 14448) /\\";
   et_bind = "(zp:int64)"; et_spill = [208,8; 224,416]; et_mods = SI87_ETA_ZMODS};;

let SI87_ETA_R =
  {et_start = SI87_L "loop52"; et_stop = SI87_L "in_polyeta_unpack_2_end";
   et_loop = SI87_L "loop54"; et_ireg = "X23"; et_kreg = "X19"; et_rreg = "X27";
   et_roff = 13312; et_aslot = 640; et_l = 8;
   et_pre = SI87_PAGES SI87_PAGE_REGS; et_post = ""; et_bind = "";
   et_spill = [224,416]; et_mods = SI87_ETA_RMODS};;

let SI87_ETA_Z_ST = {es_adrp = [5;6;7;8;9;10;11;19]; es_madd = 4; es_branch = 17;
                     es_ap = 18; es_block_end = 356; es_call_v = 364;
                     es_call_s = 24};;

let SI87_ETA_R_ST = {es_adrp = [11]; es_madd = 4; es_branch = 9; es_ap = 10;
                     es_block_end = 348; es_call_v = 354; es_call_s = 14};;

let SI87_ETA_ZL = map (fun g0 ->
  SI87_ETA_L2_PROVE "X0" SI87_MC (SI87_L "loop45") (SI87_L "loop45_exit") g0
   ("X19","X23")) [16; 0];;

let SI87_ETA_RL = map (fun g0 ->
  SI87_ETA_L2_PROVE "X0" SI87_MC (SI87_L "loop54") (SI87_L "loop54_exit") g0
   ("X19","X27")) [16; 0];;

let SI87_ETA_ZTH = SI87_ETA_PROVE SI87_MC SI87_ETA_Z SI87_ETA_Z_ST "X0" 176
  (el 0 SI87_ETA_ZL, el 1 SI87_ETA_ZL);;

let SI87_ETA_RTH = SI87_ETA_PROVE SI87_MC SI87_ETA_R SI87_ETA_R_ST "X0" 224
  (el 0 SI87_ETA_RL, el 1 SI87_ETA_RL);;

(* ------------------------------------------------------------------------- *)
(* DW1R: the decomposition of w and the packing of w1, over the 8 rows.      *)
(* ------------------------------------------------------------------------- *)

(*** polyw1_pack_32 of row i in the rolled loop38 (after the decompose    ***)
(*** loop39): the high parts at F + 13312 through x27 and the pointers     ***)
(*** x14 .. x1 = F + 13312 + 128 m, the row packed at F + 12288 + 128 i    ***)
(*** (x10 = x20 + 128 i), spills at F + 400; the loop counters advance     ***)

let SI87_W1P_PTRS =
  String.concat " /\\ " (map (fun (r,m) ->
    Printf.sprintf "read %s s = word_add fp (word %d)" r (13312 + 128 * m))
   ["X14",1; "X15",2; "X16",3; "X17",4; "X18",5; "X0",6; "X1",7]);;

let SI87_W1P_TERM = parse_term(
 "exists f_events.
    forall e (fp:int64) (x:num->int32) i (a9:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ i < 8 /\\
      nonoverlapping (word_add fp (word 400),240) (word pc,libmldsa_size) /\\
      nonoverlapping (word_add fp (word (12288 + 128 * i)),128) (word pc,libmldsa_size)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa87_signature_internal_loop39_exit) /\\
                read SP s = fp /\\ read X8 s = word i /\\ read X9 s = a9 /\\
                read X20 s = word_add fp (word 12288) /\\
                read X27 s = word_add fp (word 13312) /\\ " ^ SI87_W1P_PTRS ^ " /\\
                (!j. j < 256
                     ==> read(memory :> bytes32(word_add fp (word(13312 + 4 * j)))) s =
                         x j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa87_signature_internal_loop38_back) /\\
                read X8 s = word (i + 1) /\\ read X9 s = word_add a9 (word 1024) /\\
                (read ZF s <=> i + 1 = 8) /\\
                (!j. j < 128
                     ==> read(memory :> bytes8(word_add fp (word(12288 + 128 * i + j)))) s =
                         mld_polyw1_pack_32 x j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp i pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word 400),240; word_add fp (word 13312),1024;
                     word_add fp (word (12288 + 128 * i)),128]
                    [word_add fp (word 400),240;
                     word_add fp (word (12288 + 128 * i)),128]))
           (MAYCHANGE [PC; X8; X9; X10; X11; X12; X13] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word 400),240);
                       memory :> bytes(word_add fp (word (12288 + 128 * i)),128)])");;

let SI87_W1P_INST =
  { wp_fn = "mldsa87_signature_internal"; wp_start = "loop39_exit";
    wp_stop = "loop38_back"; wp_in = 13312; wp_out = 12288; wp_k = 8;
    wp_xw = "X27"; wp_tp = "X9"; wp_steps = 170;
    wp_mods = ["X8"; "X10"; "X11"; "X12"; "X13"] };;

let SI87_W1P_PROVE () =
  let p = SI87_W1P_INST in
  let ex = W1P2_EXEC p in
  let ith = `i < 8` in
  prove(SI87_W1P_TERM,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (i:num) (pc:num). f_ev_w1 fp i pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst ex] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN INLINE_MAP_INPUT_TAC p.wp_in `x:num->int32` THEN
  INLINE_MAP_INPUT256_TAC p.wp_in THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC ex [n] THEN INLINE_W1P2_FIX_TAC THEN
    INLINE_W1P2_SIMP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (W1P2_BASE_EQ p.wp_k p.wp_out) (ASSUME ith)]))
   (1--p.wp_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
         UNDISCH_TAC ith THEN SPEC_TAC(`i:num`,`i:num`) THEN
         CONV_TAC EXPAND_CASES_CONV THEN
         CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN NO_TAC;
         W1P2_BYTES_TAC p;
         REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC]);;

let SI87_W1P = SI87_W1P_PROVE ();;
(*** The decompose loop39 of row i (shape "62", a = x9, a1 = x27) ***)

let SI87_DEC39 = SG_DEC32_LOOP "62" SI87_MC
  (INLINE_LOOP_EXEC (SI87_L "loop39") (SI87_L "loop39_exit"))
  (SI87_L "loop39") (SI87_L "loop39_exit") 0
  ["X11";"X9";"X10";"X12";"X27";"X3";"X4";"X13";"X2"] (6,"X12") (16,"X11");;

(* ------------------------------------------------------------------------- *)
(* DW1R: the rolled loop38 over the 8 rows of w (at F + 4096): decompose     *)
(* (loop39, the high parts to F + 13312, the low parts in place) and pack    *)
(* the high parts of the row to F + 12288 + 128 i (SI87_W1P). As x86's DW1R. *)
(* ------------------------------------------------------------------------- *)

let SI87_DW1R_TERM = parse_term(
 "exists f_events.
    forall e (fp:int64) (x:num->int32) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      PAIRWISE nonoverlapping
       [(word_add fp (word 4096),8192); (word_add fp (word 12288),1024);
        (word_add fp (word 13312),1024); (word_add fp (word 400),240);
        (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa87_signature_internal_loop38) /\\
                read SP s = fp /\\ read X8 s = word 0 /\\
                read X9 s = word_add fp (word 4096) /\\
                read X20 s = word_add fp (word 12288) /\\
                read X27 s = word_add fp (word 13312) /\\ " ^ SI87_W1P_PTRS ^ " /\\
                read X2 s = word 4286586879 /\\ read X3 s = word 4294443520 /\\
                read X4 s = word 4190208 /\\
                (!i. i < 2048
                     ==> read(memory :> bytes32(word_add fp (word(4096 + 4 * i)))) s =
                         x i) /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa87_signature_internal_loop38_exit) /\\
                (!i. i < 2048
                     ==> read(memory :> bytes32(word_add fp (word(4096 + 4 * i)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 x i) /\\
                (!t. t < 1024
                     ==> read(memory :> bytes8(word_add fp (word(12288 + t)))) s =
                         mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                          128 x t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word 4096),8192; word_add fp (word 12288),1024;
                     word_add fp (word 13312),1024; word_add fp (word 400),240]
                    [word_add fp (word 4096),8192; word_add fp (word 12288),1024;
                     word_add fp (word 13312),1024; word_add fp (word 400),240]))
           (MAYCHANGE [PC; X8; X9; X10; X11; X12; X13] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word 4096),8192);
                       memory :> bytes(word_add fp (word 12288),1024);
                       memory :> bytes(word_add fp (word 13312),1024);
                       memory :> bytes(word_add fp (word 400),240)])");;

let SI87_DW1R_LO = prove
 (`!x i. mld_polyvec_map mld_poly_decompose_lo_32 x i = mld_decompose_lo_32 (x i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_polyvec_map; mld_polyvec; mld_poly_of; mld_poly_decompose_lo_32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC);;

let SI87_DW1R_W1 = prove
 (`!x t. mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128 x t =
         mld_polyw1_pack_32 (mld_poly_decompose_hi_32 x) t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_w1; mld_polyvec_pack; o_THM; mld_polyw1_pack_32;
              mld_poly_decompose_hi_32; mld_poly_of] THEN
  MP_TAC(SPECL [`t:num`; `128`] DIVISION) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_EQ_CONV)) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`q = t DIV 128`; `r = t MOD 128`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * (q * 128 + r) = 256 * q + 2 * r`;
              ARITH_RULE `2 * (q * 128 + r) + 1 = 256 * q + 2 * r + 1`]);;

let SI87_DW1R_W1_ROW = prove
 (`!x k j. mld_polyw1_pack_32 (mld_poly_decompose_hi_32 x) (128 * k + j) =
           mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of x k)) j`,
  REWRITE_TAC[mld_polyw1_pack_32; mld_poly_decompose_hi_32; mld_poly_of] THEN
  REWRITE_TAC[ARITH_RULE `2 * (128 * k + j) = 256 * k + 2 * j`;
              ARITH_RULE `2 * (128 * k + j) + 1 = 256 * k + 2 * j + 1`; ADD_ASSOC]);;

let SI87_DW1R_SLICE = prove
 (`!(B:int64) wo k (x:num->int32) (s:armstate).
     (!i. 256 * k <= i /\ i < 2048
          ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = x i) /\
     k < 8
     ==> (!i. i < 256
              ==> read (memory :> bytes32 (word_add B (word ((wo + 1024 * k) + 4 * i)))) s =
                  mld_poly_of x k i) /\
         (!i. 256 * (k + 1) <= i /\ i < 2048
              ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = x i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(wo + 1024 * k) + 4 * i = wo + 4 * (256 * k + i)`; mld_poly_of] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`i < 256`; `k < 8`] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`256 * (k + 1) <= i`; `i < 2048`] THEN ARITH_TAC]);;

let SI87_DW1R_JOIN32 = prove
 (`!(B:int64) wo k (f:num->int32) (s:armstate).
     (!i. i < 256 * k
          ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = f i) /\
     (!i. i < 256
          ==> read (memory :> bytes32 (word_add B (word ((wo + 1024 * k) + 4 * i)))) s =
              f (256 * k + i))
     ==> !i. i < 256 * (k + 1)
             ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = f i`,
  REWRITE_TAC[ARITH_RULE `(wo + 1024 * k) + 4 * i = wo + 4 * (256 * k + i)`] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i < 256 * k` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - 256 * k`) THEN
  ANTS_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < 256 * (k + 1)`; `~(i < 256 * k)`] THEN ARITH_TAC;
                  ALL_TAC] THEN
  SUBGOAL_THEN `256 * k + (i - 256 * k) = i` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `~(i < 256 * k)` THEN ARITH_TAC);;

let SI87_DW1R_JOIN8 = prove
 (`!(B:int64) oo k (f:num->byte) (s:armstate).
     (!t. t < 128 * k
          ==> read (memory :> bytes8 (word_add B (word (oo + t)))) s = f t) /\
     (!j. j < 128
          ==> read (memory :> bytes8 (word_add B (word (oo + 128 * k + j)))) s =
              f (128 * k + j))
     ==> !t. t < 128 * (k + 1)
             ==> read (memory :> bytes8 (word_add B (word (oo + t)))) s = f t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t < 128 * k` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - 128 * k`) THEN
  ANTS_TAC THENL [MAP_EVERY UNDISCH_TAC [`t < 128 * (k + 1)`; `~(t < 128 * k)`] THEN ARITH_TAC;
                  ALL_TAC] THEN
  SUBGOAL_THEN `128 * k + (t - 128 * k) = t` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `~(t < 128 * k)` THEN ARITH_TAC);;

let SI87_DW1R_TEST = prove
 (`!k. k < 8 ==> ((k + 1 = 8) <=> ~(k + 1 < 8))`, ARITH_TAC);;

let SI87_DW1R_INV = parse_term(
 "\\k s. read SP s = fp /\\ read X8 s = word k /\\
        read X9 s = word_add fp (word (4096 + 1024 * k)) /\\
        read X20 s = word_add fp (word 12288) /\\
        read X27 s = word_add fp (word 13312) /\\ " ^ SI87_W1P_PTRS ^ " /\\
        read X2 s = word 4286586879 /\\ read X3 s = word 4294443520 /\\
        read X4 s = word 4190208 /\\
        (!j. 256 * k <= j /\\ j < 2048
             ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * j)))) s =
                 (x:num->int32) j) /\\
        (!j. j < 256 * k
             ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * j)))) s =
                 mld_decompose_lo_32 (x j)) /\\
        (!t. t < 128 * k
             ==> read (memory :> bytes8 (word_add fp (word (12288 + t)))) s =
                 mld_polyw1_pack_32 (mld_poly_decompose_hi_32 x) t)");;

let SI87_DW1R_ALLOWED = [`fp:int64`; `pc:num`; `x:num->int32`; `k:num`];;

let SI87_DW1R_EXEC = INLINE_LOOP_EXEC (SI87_L "loop38") (SI87_L "loop38_exit");;

let SI87_NONOV_SUB = prove
 (`!op:int64 n m pc sz len.
        n + m <= len /\ len < 2 EXP 64 /\ nonoverlapping (op,len) (pc,sz)
        ==> nonoverlapping (word_add op (word n),m) (pc,sz)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonoverlapping; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPECL [`2 EXP 64`; `val(op:int64)`; `len:num`; `val(pc:int64)`; `sz:num`;
                `(val(op:int64) + n MOD 2 EXP 64) MOD 2 EXP 64`; `m:num`;
                `val(pc:int64)`; `sz:num`] NONOVERLAPPING_MODULO_SUBREGIONS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[nonoverlapping; DIMINDEX_64] o
        check (fun th -> can (term_match [] `nonoverlapping (a,l) (b,m)`) (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
      SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]];
    SIMP_TAC[]]);;

let SI87_DW1R_ROW_FACTS_TAC =
  SUBGOAL_THEN
   `nonoverlapping (word_add (fp:int64) (word (4096 + 1024 * k)),1024)
                   (word_add fp (word 13312),1024) /\
    nonoverlapping (word_add fp (word (4096 + 1024 * k)),1024) (word pc,libmldsa_size) /\
    nonoverlapping (word_add fp (word (12288 + 128 * k)),128) (word pc,libmldsa_size)`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_add (fp:int64) (word (4096 + 1024 * k)) =
                           word_add (word_add fp (word 4096)) (word (1024 * k))`;
                WORD_RULE `word_add (fp:int64) (word (12288 + 128 * k)) =
                           word_add (word_add fp (word 12288)) (word (128 * k))`] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SI87_NONOV_SUB THEN
    FIRST (map (fun l ->
      EXISTS_TAC l THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV;
        FIRST_ASSUM(fun th -> ACCEPT_TAC th ORELSE
                              ACCEPT_TAC(ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th))])
      [`8192`; `1024`]);
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `x:num->int32` (concl th) &&
       not(free_in `mld_decompose_lo_32` (concl th)) &&
       not(free_in `mld_poly_decompose_hi_32` (concl th))
    then MP_TAC(MATCH_MP SI87_DW1R_SLICE (CONJ th (ASSUME `k < 8`))) else NO_TAC) THEN
  STRIP_TAC;;

let SI87_DW1R_FIN_TAC =
  let j32 = BETA_RULE(ISPECL [`fp:int64`; `4096`; `k:num`;
              `\j. mld_decompose_lo_32 ((x:num->int32) j)`] SI87_DW1R_JOIN32)
  and j8 = ISPECL [`fp:int64`; `12288`; `k:num`;
              `mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (x:num->int32))`]
             SI87_DW1R_JOIN8 in
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `k:num` SI87_DW1R_TEST) (ASSUME `k < 8`)]) THEN
  RULE_ASSUM_TAC(fun th ->
    if is_forall(concl th) && free_in `mld_poly_of:(num->int32)->num->num->int32` (concl th)
    then REWRITE_RULE[mld_poly_decompose_lo_32; mld_poly_of]
           (REWRITE_RULE[GSYM SI87_DW1R_W1_ROW] th)
    else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `1024 * (k + 1) = 1024 * k + 1024`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC j32 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC j8 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SI87_DW1R_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_DW1R_EXEC
    name ilist SI87_DW1R_ALLOWED n;;

let SI87_DW1R_BODY_TAC =
  let rowa = `word_add fp (word (4096 + 1024 * k)):int64` in
  let xk = `mld_poly_of (x:num->int32) k` in
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC SI87_DW1R_EXEC (1--1) THEN
  SI87_DW1R_ROW_FACTS_TAC THEN
  SI87_DW1R_CALL_TAC "H_DEC" [rowa; `word_add fp (word 13312):int64`; xk; `pc:num`] 2 THEN
  SI87_DW1R_CALL_TAC "H_PACK"
    [`fp:int64`; mk_comb(`mld_poly_decompose_hi_32`,xk); `k:num`; rowa; `pc:num`] 3 THEN
  ARM_STEPS_TAC SI87_DW1R_EXEC (4--4) THEN
  SI87_DW1R_FIN_TAC;;

let SI87_DW1R_PROVE () = prove(SI87_DW1R_TERM,
  ASSUME_CALLEE_SAFETY_TAILED_TAC SI87_DEC39 "H_DEC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SI87_W1P "H_PACK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (pc:num).
      APPEND (f_ev_epil fp pc)
       (APPEND (ENUMERATEL 8 (\k. f_ev_row fp pc k)) (f_ev_prol fp pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; PAIRWISE; fst SI87_DW1R_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SI87_DW1R_LO; SI87_DW1R_W1] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8` `pc + mldsa87_signature_internal_loop38`
   `pc + mldsa87_signature_internal_loop38_exit` SI87_DW1R_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    SI87_DW1R_BODY_TAC;
    FULL_EXIT_TAC SI87_DW1R_EXEC 0]);;

let SI87_DW1R = SI87_DW1R_PROVE ();;

(* ------------------------------------------------------------------------- *)
(* c~ = H(mu || w1, 64), inlined (+0x351c .. +0x38b0).                       *)
(* ------------------------------------------------------------------------- *)

(*** c~ = H(mu || w1, 64) of mldsa87_signature_internal (inlined) ***)

let SI87_C2_INST =
  { sh_fn = "mldsa87_signature_internal"; sh_start = "loop38_exit";
    sh_stop = "";
    sh_pklen = 1088; sh_a = 14752; sh_t = 14368;
    sh_vars = ""; sh_pre = "";
    sh_post = "read X0 s = word_add fp (word 3072) /\\
               read X1 s = word_add fp (word 14368) /\\
               read X21 s = word_add fp (word 14336) /\\";
    sh_reads = "";
    sh_mods = "X18; X19; X20; X21; X23; X24; X30";
    sh_calls = [63;136;209;282;355;428;501;574;600];
    sh_last_bytes = (0--7) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [0;128]; sh_steps = 639 };;

let SI87_C2_STOP = layout "mldsa87_signature_internal_after_mldsa_keccakf1600_permute_4" + 0x98;;

let SI87_C2_TERM =
  let p = SI87_C2_INST in
  parse_term(Printf.sprintf
 "exists f_events.
    forall e (fp:int64) MU WP pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (word_sub fp (word 240),%d) (word pc,libmldsa_size)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %d) /\\
                read SP s = fp /\\
                read X20 s = word_add fp (word 12288) /\\
                read (memory :> bytes(word_add fp (word 1920),64)) s = MU /\\
                read (memory :> bytes(word_add fp (word 12288),1024)) s = WP /\\
                read events s = e)
           (\\s. read PC s = word (pc + %d) /\\ %s
                read (memory :> bytes(word_add fp (word %d),64)) s =
                  num_of_bytelist(list_of_seq
                    (mld_shake256_byte 1088 (MU + 2 EXP 512 * WP)) 64) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word 1920),64; word_add fp (word 12288),1024;
                     word_add fp (word %d),208;
                     word_add fp (word %d),64; word_sub fp (word 240),240;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_add fp (word %d),208; word_add fp (word %d),64;
                     word_sub fp (word 240),240]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [%s] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word %d),208);
                       memory :> bytes(word_add fp (word %d),64);
                       memory :> bytes(word_sub fp (word 240),240)])"
  (240 + p.sh_a + 208) (SHAKE_START p) SI87_C2_STOP p.sh_post p.sh_t
  p.sh_a p.sh_t p.sh_a p.sh_t p.sh_mods p.sh_a p.sh_t);;

(*** The lanes of PK = MU + 2^512 WP from those of MU and WP ***)

let SI87_C2_LO = prove
 (`!PK MU WP n. PK = MU + 2 EXP 512 * WP /\ n + 64 <= 512
                ==> (MU DIV 2 EXP n) MOD 2 EXP 64 = (PK DIV 2 EXP n) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  SUBGOAL_THEN `2 EXP 512 = 2 EXP (n + 64) * 2 EXP (512 - (n + 64))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM MULT_ASSOC; MOD_MULT_ADD]]);;

let SI87_C2_HI = prove
 (`!PK MU WP n. PK = MU + 2 EXP 512 * WP /\ MU < 2 EXP 512
                ==> (WP DIV 2 EXP n) MOD 2 EXP 64 =
                    (PK DIV 2 EXP (512 + n)) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; DIV_LT; ADD_CLAUSES]);;

let SI87_C2_BOUND = prove
 (`!PK MU WP. PK = MU + 2 EXP 512 * WP /\ MU < 2 EXP 512 /\ WP < 2 EXP 8192
              ==> PK < 2 EXP 8704`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP 512 * WP + 2 EXP 512 <= 2 EXP 8704` MP_TAC THENL
   [SUBGOAL_THEN `2 EXP 8704 = 2 EXP 512 * 2 EXP 8192` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[ARITH_RULE `a * b + a = a * (b + 1)`; LE_MULT_LCANCEL] THEN
      ASM_ARITH_TAC];
    ASM_ARITH_TAC]);;

let SI87_C2_LANES_TAC =
  W(fun (asl,w) ->
    let find_fact a n =
      snd(find (fun (_,th) -> let c = concl th in is_eq c &&
        can (term_match [] (subst [a,`a:int64`; mk_small_numeral n,`n:num`]
              `read (memory :> bytes(a,n)) s0`)) (lhs c)) asl) in
    let fa = `word_add (fp:int64) (word 1920)` and fb = `word_add (fp:int64) (word 12288)` in
    let thm = find_fact fa 64 and thw = find_fact fb 1024 in
    let bmu = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) (MATCH_MP SHAKE_READ_BYTES_BOUND thm) in
    let bw1 = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) (MATCH_MP SHAKE_READ_BYTES_BOUND thw) in
    let pkeq = SYM(ASSUME `MU + 2 EXP 512 * WP = PK`) in
    let lane a len x th i =
      let k = mk_small_numeral(8 * i) in
      let th1 = SPECL [a; mk_small_numeral len; x; k; `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
      let th2 = MP th1 (CONJ th (EQT_ELIM(NUM_REDUCE_CONV(rand(lhand(concl th1)))))) in
      CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
        (REWRITE_RULE[WORD_ADD_0] (CONV_RULE(DEPTH_CONV NUM_MULT_CONV) th2)) in
    let lo i =
      let th = lane fa 64 `MU:num` thm i in
      let n = mk_small_numeral(64 * i) in
      let eq = MP (SPECL [`PK:num`; `MU:num`; `WP:num`; n] SI87_C2_LO)
                  (CONJ pkeq (EQT_ELIM(NUM_REDUCE_CONV
                     (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` n `64`) `512`)))) in
      REWRITE_RULE[eq] th in
    let hi i =
      let th = lane fb 1024 `WP:num` thw i in
      let n = mk_small_numeral(64 * i) in
      let eq = MP (SPECL [`PK:num`; `MU:num`; `WP:num`; n] SI87_C2_HI) (CONJ pkeq bmu) in
      CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (REWRITE_RULE[eq] th) in
    let bpk = MP (SPECL [`PK:num`; `MU:num`; `WP:num`] SI87_C2_BOUND)
                 (CONJ pkeq (CONJ bmu bw1)) in
    let high t =
      let m = mk_small_numeral(8704 + 64 * t) in
      MP (SPECL [`PK:num`; `8704`; m] SHAKE_PK_HIGH)
         (CONJ bpk (EQT_ELIM(NUM_REDUCE_CONV (mk_binop `(<=):num->num->bool` `8704` m)))) in
    MAP_EVERY ASSUME_TAC
      (map lo (0--7) @ map hi (0--127) @ map high (0--16)));;

let SI87_C2_PROVE () =
  let p = SI87_C2_INST in
  let stop = SI87_C2_STOP in
  let c0 = hd p.sh_calls in
  let exec = SHAKES_EXEC p stop in
  let call = SHAKES_CALL_TAC p stop in
  prove
   (SI87_C2_TERM,
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
     "H_PERM" THEN
    CONCRETIZE_F_EVENTS_TAC
     `\(fp:int64) (pc:num). f_ev_c2 fp pc :(uarch_event)list` THEN
    META_EXISTS_TAC THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FULL_INIT_TAC THEN
    ABBREV_TAC `PK = MU + 2 EXP 512 * WP` THEN
    SI87_C2_LANES_TAC THEN
    SHAKE_PK_ABBREV_TAC p THEN
    SHAKES_IN128_TAC 1920 [0;16;32;48] THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN SHAKE_SPLIT_TAC p)
     (1--c0) THEN
    SHAKE_SPLIT_STORES_TAC {p with sh_split = [0;16;32;48]} (SHAKE_SV c0) THEN
    SHAKE_ASSEMBLE_TAC p (SHAKE_TA 0) (SHAKE_SV c0) THEN
    call (SHAKE_TA 0) (c0 + 1) THEN
    MAP_EVERY (SHAKE_BLOCK_WITH_TAC exec call p) (1--(SHAKE_NB p - 1)) THEN
    SHAKE_LAST_WITH_TAC exec call p THEN SHAKE_TAIL_WITH_TAC exec p);;

let SI87_C2 = SI87_C2_PROVE ();;

(* ------------------------------------------------------------------------- *)
(* The two inlined poly_uniform_gamma1 (gamma1 = 2^19): the generators of    *)
(* inline_sign6587.ml (SG_G1A, SG_Z19S, SG_G1M) and G1_SQZ of               *)
(* inline_sign_gamma1.ml; the squeeze of the z loop has two more            *)
(* instructions before its memcpy, which also set x20 (SI87_SQZX).           *)
(* ------------------------------------------------------------------------- *)

(*** The squeeze loop of the z loop of 87, as G1_SQZ of inline_sign_gamma1.ml ***)
(*** with d more instructions before the memcpy, which also set xregs        ***)

let SI87_SQZX_TERM xregs mc loop exit (rem,pos,off,chunk,src) so bo =
  parse_term(Printf.sprintf
   "!mc ea el ev.
      memcpy_full_contract mc ea el ev
      ==> exists f_events.
        forall e (S:1600 word) (fr:int64) pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 16 (word_add fr (word 240)) /\\
          ALLPAIRS nonoverlapping
            [(fr,240); (word_add fr (word %d),200); (word_add fr (word %d),680)]
            [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
            (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = word_add fr (word 240) /\\
                  read %s s = word 680 /\\ read %s s = word 136 /\\
                  read %s s = word 0 /\\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                  read (memory :> bytes(ea,el)) s = ev /\\
                  read (memory :> wbytes (word_add fr (word %d))) s = S /\\
                  read events s = e)
            (\\s. read PC s = word (pc + %s) /\\
                  read SP s = word_add fr (word 240) /\\
                  read %s s = word 0 /\\ read %s s = word 136 /\\
                  read %s s = word 680 /\\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                  read (memory :> bytes(ea,el)) s = ev /\\
                  read (memory :> wbytes (word_add fr (word %d))) s =
                    keccak_squeeze 5 S /\\
                  (!j. j < 680
                       ==> read (memory :> bytes8
                                  (word_add (word_add fr (word %d)) (word j))) s =
                           mld_keccak_squeeze_byte 136 S 136 j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fr mc pc /\\
                     memaccess_inbounds e2
                      [fr,240; word_add fr (word %d),200;
                       word_add fr (word %d),680;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [fr,240; word_add fr (word %d),200;
                       word_add fr (word %d),680]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
             MAYCHANGE [%s] ,,
             MAYCHANGE [memory :> bytes(fr,240);
                        memory :> bytes(word_add fr (word %d),200);
                        memory :> bytes(word_add fr (word %d),680)])"
   (240 + so) (240 + bo) mc loop rem pos off (240 + so)
   exit rem pos off (240 + so) (240 + bo)
   (240 + so) (240 + bo) (240 + so) (240 + bo)
   (String.concat "; " (filter (fun r -> let n = int_of_string
       (String.sub r 1 (String.length r - 1)) in n >= 19)
       ([rem; pos; off; chunk; src] @ xregs)))
   (240 + so) (240 + bo));;

let SI87_SQZX_PROVE xregs d mc exec loop exit ((rem,pos,off,chunk,src) as regs) so bo =
  let tm = SI87_SQZX_TERM xregs mc loop exit regs so bo in
  let st = 240 + so and bf = 240 + bo in
  let stv = parse_term(Printf.sprintf "word_add fr (word %d):int64" st) in
  let bfv = parse_term(Printf.sprintf "word_add fr (word %d):int64" bf) in
  let inv = parse_term(Printf.sprintf
   "\\i s. read SP s = word_add fr (word 240) /\\
          read %s s = word (680 - 136 * i) /\\ read %s s = word 136 /\\
          read %s s = word (136 * i) /\\
          read (memory :> bytes64(word_add (word pc) (word got_memcpy))) s = mc /\\
          read (memory :> bytes(ea,el)) s = ev /\\
          read (memory :> wbytes (word_add fr (word %d))) s = keccak_squeeze i S /\\
          read (memory :> bytes(word_add fr (word %d),136 * i)) s =
            nsum {j | j < i} (\\j. 2 EXP (8 * 136 * j) *
                                  val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136))"
   rem pos off st bf) in
  let allowed = [`fr:int64`; `mc:int64`; `pc:num`; `i:num`] in
  let perm_call name ilist n =
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec
      name ilist allowed n in
  let sv n = mk_var("s"^string_of_int n,`:armstate`) in
  let body_tac =
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN REWRITE_TAC[APPEND_NIL] THEN
    ARM_STEPS_TAC exec (1--7) THEN
    perm_call "H_PERM" [`read X0 s`; `keccak_squeeze i S`; `pc:num`;
                        `read SP s`; `read X30 s`] 8 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[G1_SQ_SUC]) THEN
    FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) =
              mk_comb(mk_comb(`read:(armstate,1600 word)component->armstate->1600 word`,
                mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,1600 word)component->(armstate,1600 word)component`,
                  `memory`),mk_comb(`wbytes:int64->(int64->byte,1600 word)component`,stv))),
                sv 8)
          with _ -> false)
      then ASSUME_TAC(MATCH_MP G1_FIRST136 th) THEN
           ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
      else NO_TAC) THEN
    ARM_STEPS_TAC exec (9--(19 + d)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` G1_CSEL) (ASSUME `i < 5`)]) THEN
    LIBC_PLT_TAC exec (19 + d) THEN
    MAP_EVERY G1_NOV
     [mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
        mk_pair(mk_comb(mk_comb(`word_add:int64->int64->int64`,bfv),
                        `word(136 * i):int64`),`136`)),mk_pair(stv,`200`));
      mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
        mk_pair(mk_comb(mk_comb(`word_add:int64->int64->int64`,bfv),
                        `word(136 * i):int64`),`136`)),
        `(word_add (word pc) (word got_memcpy):int64,8)`)] THEN
    G1_LIBC_CALL_TAC "H_MEMCPY" exec
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)`; `read X30 s`]
      allowed (24 + d) THEN
    ARM_STEPS_TAC exec ((25 + d)--(28 + d)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` G1_ARITH) (ASSUME `i < 5`)]) THEN
    REWRITE_TAC[MP (SPEC `i:num` G1_ARITH) (ASSUME `i < 5`)] THEN
    ASM_CASES_TAC `i + 1 < 5` THEN ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
    REPEAT CONJ_TAC THEN
    FIRST [MP_TAC(SPECL [`fr:int64`; mk_small_numeral bf; `i:num`; `S:1600 word`; sv (28 + d)] G1_EXTBLK) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
           REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           ASM_REWRITE_TAC[] THEN G1_SAFETY_TAC] in
  let exit_tac =
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]) THEN
    CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]
        (SPECL [bfv; `136`; `5`; `S:1600 word`; `s0:armstate`]
               MLD_SQUEEZE_BLOCKS_BYTES8)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 136`]; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC in
  prove(tm,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fr:int64) (mc:int64) (pc:num).
      APPEND (f_ev_epil fr mc pc)
       (APPEND (ENUMERATEL 5 (\i. if i + 1 < 5 then f_ev_c fr mc pc i
                                  else f_ev_l fr mc pc i))
               (f_ev_prol fr mc pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `S:1600 word`; `fr:int64`;
                       `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
      (REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst exec] th)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `5` (parse_term("pc + " ^ loop))
    (parse_term("pc + " ^ exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[keccak_squeeze; NSUM_CLAUSES_NUMSEG_LT; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL] THEN
    TRY DISCHARGE_SAFETY_PROPERTY_TAC;
    body_tac;
    exit_tac]);;

(*** The inlined poly_uniform_gamma1 of the column loop (y_j, nonce 7 att + j ***)
(*** with 7 att at fp + 624 and j in w19, rho'' in x25, y_j to fp + 13312)   ***)

let SI87_G1A_Y = SG_G1A_PROVE SI87_MC
  {ga_start = SI87_L "loop3"; ga_stop = SI87_L "loop4"; ga_steps = 59;
   ga_pre = "read (memory :> bytes32 (word_add sp (word 624))) s = word nb /\\
             read X19 s = word j /\\ read X25 s = rp /\\
             read X22 s = word_add sp (word 14448) /\\ read Q7 s = word 0 /\\";
   ga_post = "read X21 s = word 680 /\\ read X22 s = word 136 /\\ read X20 s = word 0 /\\";
   ga_so = 14448; ga_io = 14656; ga_slots = [624,4];
   ga_mods = ["X8";"X9";"X20";"X21";"X22"];
   ga_plan = [13,["nonce",14720];
              21,["split",14512; "split",14576; "split",14624; "zero16",14512];
              57,["split",14636]]};;

let SI87_SQZ_Y = G1_SQZ_PROVE SI87_MC
  (G1_EXEC_PLT (SI87_AT 0x34c) (SI87_L "loop4_exit"))
  (SI87_L "loop4") (SI87_L "loop4_exit") ("X21","X22","X20","X23","X24")
  14448 14752;;

let SI87_Z19_Y = SG_Z19S "mldsa87_signature_internal" "loop5" "X27";;

let SI87_G1_Y = SG_G1M_PROVE SI87_MC
  {gm_start = SI87_L "loop3"; gm_stop = SI87_L "after_memset_1"; gm_sqzx = 0x34c;
   gm_sqzl = SI87_L "loop4"; gm_sqz = ("X21","X22","X20","X23","X24");
   gm_zl = SI87_L "loop5";
   gm_io = 14656; gm_so = 14448; gm_bo = 14752; gm_zo = 13312;
   gm_slots = [216,8; 624,4];
   gm_pre = "read (memory :> bytes32 (word_add fr (word 864))) s = word nb /\\
             read X19 s = word j /\\ read X25 s = rp /\\
             read X22 s = word_add fr (word 14688) /\\ read Q7 s = word 0 /\\
             read (memory :> bytes64 (word_add fr (word 456))) s = word_add fr (word 15001) /\\
             read X27 s = word_add fr (word 13552) /\\";
   gm_post = "read X21 s = word_add fr (word 976) /\\";
   gm_n1 = 5; gm_n2 = 21; gm_mods = ["X20";"X21";"X22";"X23";"X24"]}
  (SI87_G1A_Y,SI87_SQZ_Y,SI87_Z19_Y);;

(*** The inlined poly_uniform_gamma1 of the z loop (y_i, nonce 7 att + i in ***)
(*** w9 and i in x20, rho'' in x8, y_i to fp + 13312), from in_poly_      ***)
(*** uniform_gamma1_2 (after the save of i at fp + 624) to after_memset_2   ***)

let SI87_G1A_Z = SG_G1A_PROVE SI87_MC
  {ga_start = SI87_AT 0x3fd8; ga_stop = SI87_L "loop47"; ga_steps = 54;
   ga_pre = "read X8 s = rp /\\ read X9 s = word nb /\\ read X20 s = word j /\\
             read X22 s = word_add sp (word 14448) /\\ read Q7 s = word 0 /\\
             read X21 s = word 680 /\\ read X25 s = word 0 /\\";
   ga_post = "read X21 s = word 680 /\\ read X22 s = word 136 /\\ read X25 s = word 0 /\\";
   ga_so = 14448; ga_io = 14656; ga_slots = [];
   ga_mods = ["X8";"X9";"X22"];
   ga_plan = [4,["nonce16",14720];
              12,["split",14512; "split",14576; "split",14624; "zero16",14512];
              52,["split",14636]]};;

let SI87_SQZ_Z = SI87_SQZX_PROVE ["X20"] 2 SI87_MC
  (G1_EXEC_PLT (SI87_AT 0x40b0) (SI87_L "loop47_exit"))
  (SI87_L "loop47") (SI87_L "loop47_exit") ("X21","X22","X25","X23","X24")
  14448 14752;;
let SI87_Z19_Z = SG_Z19S "mldsa87_signature_internal" "loop48" "X27";;

let SI87_G1_Z = SG_G1M_PROVE SI87_MC
  {gm_start = SI87_AT 0x3fd8; gm_stop = SI87_L "after_memset_2"; gm_sqzx = 0x40b0;
   gm_sqzl = SI87_L "loop47"; gm_sqz = ("X21","X22","X25","X23","X24");
   gm_zl = SI87_L "loop48";
   gm_io = 14656; gm_so = 14448; gm_bo = 14752; gm_zo = 13312;
   gm_slots = [216,8];
   gm_pre = "read X8 s = rp /\\ read X9 s = word nb /\\ read X20 s = word j /\\
             read X22 s = word_add fr (word 14688) /\\ read Q7 s = word 0 /\\
             read X21 s = word 680 /\\ read X25 s = word 0 /\\
             read (memory :> bytes64 (word_add fr (word 456))) s = word_add fr (word 15001) /\\
             read X27 s = word_add fr (word 13552) /\\";
   gm_post = "";
   gm_n1 = 4; gm_n2 = 21; gm_mods = ["X20";"X21";"X22";"X23";"X24";"X25"]}
  (SI87_G1A_Z,SI87_SQZ_Z,SI87_Z19_Z);;

(* ------------------------------------------------------------------------- *)
(* polyw1_unpack_32 of row k in pack_sig_h (straight-line, before the hint  *)
(* loop of the row): the packed row at fp + 12288 + 128 k, unpacked to      *)
(* fp + 13312 (x27). Row 0 also copies c~ (fp + 14368, 64 bytes) to sig,     *)
(* zeroes the hints (sig + 4544, 83 bytes; only the first omega = 75 are    *)
(* used before the counts overwrite the rest) and loads the pointers of the *)
(* rows 1 to 4 and the constants of the hint test; rows 1 to 7 store the    *)
(* count of the row before at sig + 4619 + k - 1 (through [fp + 72] =       *)
(* sig + 4096).                                                              *)
(* ------------------------------------------------------------------------- *)

let SI87_SIGNOV (a,l) rs = String.concat "" (map (fun r -> Printf.sprintf
   "nonoverlapping (%s,%d) (%s) /\\ " a l r) rs);;

let SI87_W1U0 = SG_W1U32_PROVE SI87_MC
  {w3_start = SI87_L "loop52_exit1"; w3_stop = SI87_L "loop62"; w3_steps = 223;
   w3_in = 12288; w3_out = 13312;
   w3_bind = "(sig:int64) (c0:int128) (c1:int128) (c2:int128) (c3:int128)";
   w3_nov = String.concat "" (map (fun r -> SI87_SIGNOV r
       ["word pc,libmldsa_size"; "word_add fp (word 32),64";
        "word_add fp (word 14368),64"; "word_add fp (word 13312),1024";
        "word_add fp (word 12288),128"])
      ["sig",64; "word_add sig (word 4544)",83]);
   w3_pre = "read (memory :> bytes64 (word_add fp (word 88))) s = sig /\\
     read (memory :> bytes64 (word_add fp (word 32))) s = word_add sig (word 4544) /\\
     read (memory :> bytes64 (word_add fp (word 40))) s = word_add fp (word 8192) /\\
     read (memory :> bytes64 (word_add fp (word 48))) s = word_add fp (word 7168) /\\
     read (memory :> bytes64 (word_add fp (word 56))) s = word_add fp (word 6144) /\\
     read (memory :> bytes64 (word_add fp (word 64))) s = word_add fp (word 5120) /\\
     read (memory :> bytes128 (word_add fp (word 14368))) s = c0 /\\
     read (memory :> bytes128 (word_add fp (word 14384))) s = c1 /\\
     read (memory :> bytes128 (word_add fp (word 14400))) s = c2 /\\
     read (memory :> bytes128 (word_add fp (word 14416))) s = c3 /\\";
   w3_post = "read X8 s = word 0 /\\ read X9 s = word 0 /\\ read X10 s = sig /\\
     read X13 s = word 4294705408 /\\ read X1 s = word 261888 /\\
     read X0 s = word_add sig (word 4544) /\\
     read X15 s = word_add fp (word 5120) /\\ read X16 s = word_add fp (word 6144) /\\
     read X17 s = word_add fp (word 7168) /\\ read X18 s = word_add fp (word 8192) /\\
     read X23 s = word_add fp (word 2048) /\\
     read (memory :> bytes128 sig) s = c0 /\\
     read (memory :> bytes128 (word_add sig (word 16))) s = c1 /\\
     read (memory :> bytes128 (word_add sig (word 32))) s = c2 /\\
     read (memory :> bytes128 (word_add sig (word 48))) s = c3 /\\
     (!t. t < 75 ==> read (memory :> bytes8 (word_add sig (word (4544 + t)))) s = word 0) /\\";
   w3_rd = ["word_add fp (word 32),64"; "word_add fp (word 14368),64"];
   w3_wr = ["sig,64"; "word_add sig (word 4544),83"];
   w3_ev = "(sig:int64)";
   w3_mods = ["X0";"X1";"X8";"X9";"X10";"X13";"X15";"X16";"X17";"X18";"X23"];
   w3_plan = [37,["word_add sig (word 4608)"];
              223,["word_add sig (word 4544)"; "word_add sig (word 4560)";
                   "word_add sig (word 4576)"; "word_add sig (word 4592)"]]};;

let SI87_W1UK = map (fun k ->
  let c = 4618 + k in
  let st = if k = 1 then "loop62_exit2" else Printf.sprintf "loop%d_exit2" (62 + k) in
  let sp = Printf.sprintf "loop%d" (63 + k) in
  SG_W1U32_PROVE SI87_MC
  {w3_start = SI87_L st; w3_stop = SI87_L sp; w3_steps = 205;
   w3_in = 12288 + 128 * k; w3_out = 13312; w3_bind = "(sig:int64) (cnt:num)";
   w3_nov = SI87_SIGNOV (Printf.sprintf "word_add sig (word %d)" c,1)
     ["word pc,libmldsa_size"; "word_add fp (word 72),8";
      "word_add fp (word 13312),1024";
      Printf.sprintf "word_add fp (word %d),128" (12288 + 128 * k)];
   w3_pre = "read X8 s = word cnt /\\
             read (memory :> bytes64 (word_add fp (word 72))) s = word_add sig (word 4096) /\\";
   w3_post = Printf.sprintf
     "read X9 s = word 0 /\\ read X10 s = word_add sig (word 4096) /\\ read X8 s = word cnt /\\
      read (memory :> bytes8 (word_add sig (word %d))) s = word cnt /\\" c;
   w3_rd = ["word_add fp (word 72),8"];
   w3_wr = [Printf.sprintf "word_add sig (word %d),1" c];
   w3_ev = "(sig:int64)"; w3_mods = ["X9";"X10"]; w3_plan = []})
  (1--7);;

(* ------------------------------------------------------------------------- *)
(* The hint loops of pack_sig_h (loops 62 and 64 to 70), w0 of row k at      *)
(* fp + 4096 + 1024 k (row 0: computed as sp + 4096 in the loop; rows 1 to  *)
(* 4: x15 .. x18; rows 5 to 7: from the slots fp + 160, 152, 144), w1 of    *)
(* the row unpacked at fp + 13312 (x27), the hints at sig + 4544 (x0),       *)
(* omega = 75; too many hints leave to join10 (= loopN_exit1).               *)
(* ------------------------------------------------------------------------- *)

let SI87_HROW_INSTS =
  map (fun (k,lp,lo,hi,wreg,slot) ->
    {hr3_fn = "mldsa87_signature_internal"; hr3_k = k; hr3_head = SI87_L lp;
     hr3_exit = SI87_L (lp ^ "_exit2"); hr3_lo = lo; hr3_hi = hi;
     hr3_wreg = wreg; hr3_woff = 4096 + 1024 * k; hr3_w1reg = "X27";
     hr3_w1off = 13312; hr3_hreg = "X0"; hr3_hoff = 4544; hr3_omega = 75;
     hr3_cregs = ("X13","X1","X14");
     hr3_mods = if k = 0 then "X8; X9; X10; X11" else "X8; X9; X10; X11; X12";
     hr3_slot = slot})
  [0,"loop62",0x5d7c,0x5db8,"",[];
   1,"loop64",0x61c4,0x6208,"X15",[];
   2,"loop65",0x653c,0x6580,"X16",[];
   3,"loop66",0x68b4,0x68f8,"X17",[];
   4,"loop67",0x6c2c,0x6c70,"X18",[];
   5,"loop68",0x6fa4,0x6fec,"",[160,9216];
   6,"loop69",0x7320,0x7368,"",[152,10240];
   7,"loop70",0x769c,0x76e4,"",[144,11264]];;

let SI87_HROW = map SG_HROW32_PROVE SI87_HROW_INSTS;;

(* ------------------------------------------------------------------------- *)
(* polyz_pack_19 of z_i (fp + 2048) into the signature at x25 + 64 (x25 =   *)
(* sig + 640 i), the constants of the TBLs through 17 page registers        *)
(* ------------------------------------------------------------------------- *)

let SI87_ZPACK = SG_ZPACK19_PROVE SI87_MC
  {zp_start = SI87_L "loop51"; zp_stop = SI87_L "loop51_exit";
   zp_steps = 832; zp_in = 2048; zp_out = 64; zp_inreg = "X8"; zp_opreg = "X25";
   zp_offreg = "X9";
   zp_pages = ["X12";"X13";"X21";"X14";"X15";"X16";"X17";"X18";"X30";"X1";"X2";"X3";
               "X4";"X5";"X6";"X7";"X24"];
   zp_cd = 0x3c4b0; zp_ncd = 17; zp_q = "Q29";
   zp_post = "read X8 s = word_add fp (word 3072) /\\ read X9 s = word 704 /\\";
   zp_mods = ["X8";"X9";"X10";"X11";"Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";
              "Q16";"Q17";"Q18";"Q19";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q27";"Q28"]};;
