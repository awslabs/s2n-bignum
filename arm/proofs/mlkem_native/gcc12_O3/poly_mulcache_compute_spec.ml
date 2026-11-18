(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Precomputation of the mulcache for polynomial multiplication.             *)
(* This is the code for mlkem_poly_mulcache_compute from mlkem-native's      *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), verified in the whole image (see libmlkem.ml)    *)
(* with the specification of the -O2 code.                                   *)
(*                                                                           *)
(* At -O2 the code is a scalar loop over the 64 pairs of outputs, reading    *)
(* the zetas from the table mlk_zetas. At -O3 gcc has vectorized it: unless  *)
(* the output may overlap the input, by a check that computes with the       *)
(* addresses modulo 2^64, a straight-line block of about 230 instructions    *)
(* does everything. Its 7 groups of 16 outputs use LD4 to split 32 input     *)
(* coefficients into 4 vectors, multiply the odd ones by 17 vectors of zetas *)
(* (and their negations) that are stored in the read-only data rather than   *)
(* taken from mlk_zetas, do the Montgomery reduction, and store with ST2.    *)
(* The next 8 outputs are done with 64-bit vectors and the last 8 with a     *)
(* vector filled by single-lane loads. Otherwise the code uses a scalar loop *)
(* like that at -O2. When the output and the input do not overlap, the check *)
(* always takes the vector code, so that is the only path verified here.     *)
(*                                                                           *)
(* The statement differs from that of the -O2 code in that the vector code   *)
(* saves D8 on the stack, so there is a stack frame of 16 bytes. The safety  *)
(* theorem lists the block of vectors of constants as a read-only region,    *)
(* rather than the zetas.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_mulcache_compute"];;

(* ------------------------------------------------------------------------- *)
(* The check for overlap. With x4 = src + 2 and x2 = dst + 256, cmp x4, x2   *)
(* then, with x2 = src + 512, ccmp x0, x2 leave the carry flag clear, taking *)
(* the scalar code, if src + 2 < dst + 256 and dst < src + 512, computing    *)
(* modulo 2^64. When the 256 bytes from dst and the 512 bytes from src do    *)
(* not overlap, this does not happen, also when one of them wraps around the *)
(* end of the address space.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOD_2N_CASES_STMT =
  `!x n. x < 2 * n ==> x MOD n = if x < n then x else x - n`;;

let MOD_2N_CASES = assume_spec MOD_2N_CASES_STMT;;

let WORD_SUB_FLAG_64_STMT =
  `!x y:int64.
     &(val x) - &(val y):int = &(val(word_sub x y)) <=> val y <= val x`;;

let WORD_SUB_FLAG_64 = assume_spec WORD_SUB_FLAG_64_STMT;;

let MULCACHE_ALIAS_STMT =
  `!dst src:int64.
     nonoverlapping (dst,256) (src,512)
     ==> (if val (word_add src (word 2):int64) <
             val (word_add dst (word 256):int64)
          then &(val dst) - &(val (word_add src (word 512))):int =
               &(val (word_sub dst (word_add src (word 512))))
          else T)`;;

let MULCACHE_ALIAS = assume_spec MULCACHE_ALIAS_STMT;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the vector code. The last 8 pairs of outputs but 8 are done  *)
(* with 4 32-bit lanes, as sign extensions, a shift and a narrowing shift,   *)
(* which are rewritten to the form montred_neon of the 16-bit lanes.         *)
(* ------------------------------------------------------------------------- *)

let CONG_MONT_ZETA = INTEGER_RULE
 `!n a z p x r:int. (r == a * (x * z)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

let WORD_SHL_0_32_STMT =
  `!w:int32. word_shl w 0 = w`;;

let WORD_SHL_0_32 = assume_spec WORD_SHL_0_32_STMT;;

let WORD_USHR16_SUB_STMT =
  `!y:int32. word_subword (word_ushr y 16) (0,16):int16 =
             word_subword y (16,16)`;;

let WORD_USHR16_SUB = assume_spec WORD_USHR16_SUB_STMT;;

let MC_TAIL_MONTRED_STMT =
  `!p:int32.
     word_subword
      (word_ushr
        (word_add p
          (word_mul (word_sx (word_mul (word_subword p (0,16)) (word 62209):
                              int16):int32) (word 4294963967))) 16) (0,16):
     int16 = montred_neon p`;;

let MC_TAIL_MONTRED = assume_spec MC_TAIL_MONTRED_STMT;;

let WORD_SUBWORD_ZX16_STMT =
  `!w:int16. word_subword (word_subword w (0,16):int128) (0,16):int16 = w`;;

let WORD_SUBWORD_ZX16 = assume_spec WORD_SUBWORD_ZX16_STMT;;

let ZX64_SUB = map (fun k -> prove(subst [mk_small_numeral k,`k:num`]
  `!w:int64. word_subword (word_subword w (0,128):int128) (k,16):int16 =
             word_subword w (k,16)`, BITBLAST_TAC)) [0;16;32;48];;

let WORD_ZX_ZX_64_STMT =
  `!w:int64. word_zx(word_zx w:int128):int64 = w`;;

let WORD_ZX_ZX_64 = assume_spec WORD_ZX_ZX_64_STMT;;

(* ------------------------------------------------------------------------- *)
(* Tactics for the simulation.                                               *)
(* ------------------------------------------------------------------------- *)

(*** The facts for the 255 input coefficients that are read, from the input
 *** fact for all of them, with the addresses as the simulation has them
 ***)

let MC_LOAD_FACTS_TAC =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `x:num->int16` (concl th) then
      MAP_EVERY (fun e ->
        MP_TAC(SPEC (mk_small_numeral e) th) THEN
        ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)))
        (1--255)
    else failwith "MC_LOAD_FACTS_TAC");;

(*** The 128-bit loads by LD4 from 2 bytes after the start of the input, and
 *** the 64-bit loads of the next four coefficients, merged from the facts
 *** for the coefficients
 ***)

let MC_MERGE_TAC s =
  let mk c k = subst [mk_small_numeral c,`c:num`; s,`s:armstate`]
     (if k = 3 then `read (memory :> bytes128 (word_add src (word c))) s`
      else `read (memory :> bytes64 (word_add src (word c))) s`) in
  MAP_EVERY (fun (t,k) -> MP_TAC(READ_MEMORY_MERGE_CONV k t))
   (map (fun m -> (mk (2 + 16 * m) 3, 3)) (0--27) @
    map (fun c -> (mk c 2, 2)) [450; 458; 466; 474]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

(*** The registers loaded by LD4 as lanes of the coefficients ***)

let MC_SIMD_ALL_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read X (s:armstate):int128 = whatever`)
           (concl th) &&
       can (find_term (fun t -> match t with
              Const("word_subdeinterleave",_) -> true | _ -> false))
           (concl th)
    then CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [montred_neon]))
          (CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th)
    else th);;

(*** The steps of the straight-line code, with ADRP after each of the steps
 *** that compute a page, and the lanes simplified
 ***)

let mc_adrp_steps =
  [8;12;16;18;36;41;48;52;55;57;62;67;71;80;84;89;94;99;103];;

let mc_step_tac n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_EXEC [n] THEN
  (if mem n mc_adrp_steps then MLKEM_NATIVE_ADRP_TAC else ALL_TAC) THEN
  MC_SIMD_ALL_TAC THEN SIMD_SIMPLIFY_TAC[montred_neon];;

(*** The facts for the output as vectors of montred_neon of the products,
 *** with the last 16 outputs from 64-bit and 128-bit stores of vectors made
 *** by shifts and narrowing, brought to the same form
 ***)

let MC_IS_DST_FACT c =
  is_eq c &&
  (can (term_match [] `read (memory :> bytes128 a) s = x`) c ||
   can (term_match [] `read (memory :> bytes256 a) s = x`) c ||
   can (term_match [] `read (memory :> bytes64 a) s = x`) c) &&
  free_in `dst:int64` (lhs c);;

let MC_DST_CLEAN_TAC =
  RULE_ASSUM_TAC(fun th ->
    if MC_IS_DST_FACT (concl th)
    then CONV_RULE(RAND_CONV(TRY_CONV(REWRITE_CONV[WORD_SHL_0_32]) THENC
                             SIMD_SIMPLIFY_CONV [montred_neon] THENC
                             TRY_CONV(REWRITE_CONV[MC_TAIL_MONTRED]) THENC
                             SIMD_SIMPLIFY_CONV [montred_neon])) th
    else th) THEN
  RULE_ASSUM_TAC(fun th ->
    if MC_IS_DST_FACT (concl th)
    then CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SUBWORD_ZX16] THENC
                             SIMD_SIMPLIFY_CONV [montred_neon])) th
    else th) THEN
  RULE_ASSUM_TAC(fun th ->
    if MC_IS_DST_FACT (concl th)
    then CONV_RULE(RAND_CONV(REWRITE_CONV ZX64_SUB THENC
                             SIMD_SIMPLIFY_CONV [montred_neon])) th
    else th) THEN
  RULE_ASSUM_TAC(fun th ->
    if MC_IS_DST_FACT (concl th) &&
       can (term_match [] `read (memory :> bytes64 a) s = x`) (concl th)
    then CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_ZX_ZX_64])) th else th);;

(*** The stores split into the 16-bit lanes of the output ***)

let MC_SPLIT_TAC =
  MAP_EVERY (fun (pat,k) ->
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        CONV_RULE (SIMD_SIMPLIFY_CONV []) o
        CONV_RULE(READ_MEMORY_SPLIT_CONV k) o
        check (fun th ->
          can (term_match [] pat) (concl th) && free_in `dst:int64` (concl th)))))
   [`read (memory :> bytes256 a) s = x`,4;
    `read (memory :> bytes128 a) s = x`,3;
    `read (memory :> bytes64 a) s = x`,2];;

(*** The facts for the input are no longer needed ***)

let MC_DISCARD_SRC_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let c = concl th in
    is_eq c && free_in `src:int64` (lhs c) &&
    (can (term_match [] `read (memory :> bytes16 a) s = (y:int16)`) c ||
     can (term_match [] `read (memory :> bytes128 a) s = (y:int128)`) c ||
     can (term_match [] `read (memory :> bytes64 a) s = (y:int64)`) c))));;

(*** One output: Montgomery reduction of a product of an input coefficient
 *** and a zeta that is a numeral, which is 169 times a power of 17 that
 *** is checked by evaluation
 ***)

let MC_LANE_TAC =
  REWRITE_TAC[MONTRED_NEON_SCALAR] THEN
  W(fun (asl,w) ->
    let m = find_term (fun t ->
      try fst(dest_const(rator t)) = "montred_scalar" with _ -> false) w in
    let tm = rand m in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE [] tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = CONV_RULE(ONCE_DEPTH_CONV INVERSE_MOD_CONV)
               (MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2))))) in
    let cth,bth = CONJ_PAIR th3 in
    let zz = rand(rand(rand(rator(concl cth)))) in
    CONJ_TAC THENL
     [REWRITE_TAC[mulcache; o_THM; INT_CONG_RREM; BITREVERSE7_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      MATCH_MP_TAC CONG_MONT_ZETA THEN
      MAP_EVERY EXISTS_TAC [`&169:int`; zz] THEN
      CONJ_TAC THENL
       [ACCEPT_TAC cth;
        REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV];
      MP_TAC bth THEN CONV_TAC(LAND_CONV INT_REDUCE_CONV) THEN
      INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The vectors of zetas and the vector of 3329^-1 mod 2^16, as a Q and a D
 *** register, in the image
 ***)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_CONSTANTS =
  map (fun k -> MLKEM_NATIVE_IMAGE_CONST_RULE
         (layout ("mlkem_poly_mulcache_compute_const" ^ string_of_int k)) 128)
      (2--18) @
  map (MLKEM_NATIVE_IMAGE_CONST_RULE
        (layout "mlkem1024_polyvec_basemul_acc_montgomery_cached_consts"))
      [128; 64];;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!dst src x pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (dst,256))
        [(word pc,libmlkem_size); (src,512);
         (word_sub stackpointer (word 16),16)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [(word pc,libmlkem_size); (src,512)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
           read PC s = word (pc + mlkem_poly_mulcache_compute) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256);
                  memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Unlike mlkem_mulcache_compute, this has just two arguments, and the ***)
(*** vectors of constants are read-only data.                            ***)

let mlkem_native_poly_mulcache_compute_signature =
  ([("x", "int16_t[static 128]", "false");
    ("a", "int16_t[static 256]", "true")],
   "void",
   [("a", "256", 2)],
   [("x", "128", 2)],
   []);;
let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_mulcache_compute_consts):int64`,
                       `mlkem_poly_mulcache_compute_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_poly_mulcache_compute_signature
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_EXEC;;

(*** The steps of the straight-line code between the ADRP instructions ***)

let mc_safe_ranges =
  let rec go lo l = match l with
    | [] -> [(lo,235)]
    | a::t -> (lo,a)::go (a+1) t in
  go 7 mc_adrp_steps;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (dst,256))
           [word pc,libmlkem_size; src,512;
            word_sub stackpointer (word 16),16] /\
           ALL (nonoverlapping (word_sub stackpointer (word 16),16))
           [word pc,libmlkem_size; src,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_mulcache_compute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events src dst pc
                         (word_sub stackpointer (word 16))
                         returnaddress /\
                         memaccess_inbounds e2
                         [src,512; dst,256;
                          word_sub stackpointer (word 16),16;
                          word (pc + mlkem_poly_mulcache_compute_consts),
                          mlkem_poly_mulcache_compute_consts_size]
                         [dst,256; word_sub stackpointer (word 16),16]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (dst,256);
                 memory :> bytes (word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
