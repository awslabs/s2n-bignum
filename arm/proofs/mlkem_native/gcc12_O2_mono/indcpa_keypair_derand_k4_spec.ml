(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-1024 (FIPS 203 Algorithm 13). This  *)
(* is the code for mlkem1024_indcpa_keypair_derand from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 as one translation  *)
(* unit (see mlkem_native/README.md). It hashes the 32-byte seed d followed  *)
(* by the byte 4 with SHA3-512 into the seeds rho and sigma, generates the   *)
(* matrix in NTT form from rho, samples the secret s and the error e from    *)
(* sigma and transforms them, computes t = A s + e in the NTT domain, and    *)
(* writes the encoding of t followed by rho as the public key and the        *)
(* encoding of s as the secret key, zeroing its buffers. It is verified in   *)
(* the whole image (see libmlkem.ml), using the theorems for mlkem_sha3_512, *)
(* mlkem1024_gen_matrix, mlkem1024_poly_getnoise_eta1_4x, mlk_poly_ntt_c,    *)
(* mlk_poly_mulcache_compute_c,                                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c1024, mlk_poly_reduce_c and    *)
(* mlk_poly_tobytes_c in the image, and the contracts for memset and         *)
(* memcpy.                                                                   *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined all the polyvec    *)
(* functions:                                                                *)
(*                                                                           *)
(*  - polyvec_ntt and polyvec_reduce: the kernel is called for each          *)
(*    polynomial, and polyvec_mulcache_compute and polyvec_tobytes are loops *)
(*    of calls (the second polyvec_tobytes rotated by gcc), unrolled in the  *)
(*    proof; the postcondition of the polyvec function is proved from those  *)
(*    of the calls (mlkem_native/indcpa_inline.ml);                          *)
(*  - polyvec_basemul: a loop over the rows calling the c1024 kernel, which  *)
(*    is the gcc 12 -O2 mlkem1024_polyvec_basemul_acc_montgomery_cached, as  *)
(*    the gcc 12 -O2 code does;                                              *)
(*  - polyvec_tomont and polyvec_add: two nested loops each, the inner one   *)
(*    the vector code of poly_tomont or poly_add for one polynomial. The     *)
(*    inner loops are proved as lemmas from their head to their exit, with   *)
(*    the events (mlkem_native/inline_loops.ml), and the outer loops, of     *)
(*    four iterations, are unrolled.                                         *)
(*                                                                           *)
(* The buffers are at the same offsets from each other as with gcc 12 -O2;   *)
(* the frame is the 15680 bytes of the function and the 3680 of              *)
(* mlkem1024_gen_matrix below them, 19360 in all.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/gen_matrix_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta1_4x_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_tobytes_spec.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memset"; layout_range "mlkem1024_indcpa_keypair_derand"];;

let KP4_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code: those of the NTTs of s and e, those of the multiplication       *)
(* cache, those of the matrix-vector product in Montgomery form, and those   *)
(* of the final results after Montgomery conversion, addition and reduction. *)
(* The two lemmas on single coefficients relate the computation of the code  *)
(* to MultiplyNTTs and the addition of e in the NTT domain, for even and odd *)
(* coefficients.                                                             *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_COEFF_EVEN_K4_STMT =
  `!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 3 (2 * p + 1) * YT 3 + A 3 (2 * p) * Y 3 (2 * p)) +
                   (A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`;;

let KPKE_KEYGEN_COEFF_EVEN_K4 = assume_spec KPKE_KEYGEN_COEFF_EVEN_K4_STMT;;

let KPKE_KEYGEN_COEFF_ODD_K4_STMT =
  `!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 3 (2 * p + 1) * Y 3 (2 * p) + A 3 (2 * p) * Y 3 (2 * p + 1)) +
            (A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`;;

let KPKE_KEYGEN_COEFF_ODD_K4 = assume_spec KPKE_KEYGEN_COEFF_ODD_K4_STMT;;

let KPKE_KEYGEN_K4_RESULT_STMT =
  `!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 4]) = rho,sigma /\
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 4 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(mc(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(mc(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(sh(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(sh(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 1024 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 1024 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 1024 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 1024)) +
         2 EXP (8 * 1536) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 1024)) =
         num_of_bytelist(SND(kpke_keygen mlkem1024 d))`;;

let KPKE_KEYGEN_K4_RESULT = assume_spec KPKE_KEYGEN_K4_RESULT_STMT;;


(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The input to SHA3-512 is the seed copied as two 128-bit words and  *)
(* the byte 4 (the parameter k), and its output is the two seeds rho and     *)
(* sigma as in mlkem_g.                                                      *)
(* ------------------------------------------------------------------------- *)

let KP4_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let KP4_ALIGNED_16_32 = assume_spec KP4_ALIGNED_16_32_STMT;;

let KP4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3887)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3872 else 3856))`;;

let KP4_BUFFER_ADDRESS = assume_spec KP4_BUFFER_ADDRESS_STMT;;

let KP4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KP4_BUFFER_ADDRESS))
    else NO_TAC);;

let KP4_INPUT_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 15424); `d:byte list`; `4`; s]
               INLINE_SEED_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    STRIP_TAC];;

let KP4_G_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)`)
           (concl th)
    then ASSUME_TAC th THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                 (REWRITE_RULE
                   [ASSUME `FST(mlkem_g(APPEND d [word 4])) = rho`;
                    ASSUME `SND(mlkem_g(APPEND d [word 4])) = sigma`]
                   (MATCH_MP MLKEM_G_BYTES th))) THEN
         CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC
    else NO_TAC);;

(*** A seed of 32 bytes as two 128-bit words: the seed d at coins, and rho
     before it is copied into the public key ***)

let KP4_HALVES_TAC a v =
  let pat = subst [a,`a:int64`]
   (parse_term(Printf.sprintf
     "read (memory :> bytes(a,32)) s = num_of_bytelist %s" v)) in
  let avoid = subtract (frees pat) [`s:armstate`] in
  FIRST_ASSUM(MP_TAC o MATCH_MP INLINE_BYTES128_HALVES o check (fun th ->
    can (term_match avoid pat) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KP4_RHO_TAC s =
  MP_TAC(SPECL [`word_add pk (word 1536):int64`; `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] INLINE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The inner loops of polyvec_tomont and polyvec_add, the inlined vector     *)
(* code of poly_tomont and poly_add for one polynomial, as lemmas from their *)
(* head to their exit, with the events (mlkem_native/inline_loops.ml).       *)
(* ------------------------------------------------------------------------- *)

let KP4_TOMONT = INLINE_TOMONT_LOOP_REG
  "mlkem_native_libmlkem_gcc12_O2_mono_mc" KP4_EXEC
  "mlkem1024_indcpa_keypair_derand_loop4"
  "mlkem1024_indcpa_keypair_derand_loop4_exit" "X0" "X1";;

let KP4_ADD = INLINE_REG_IDX_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KP4_EXEC "add" "mlkem1024_indcpa_keypair_derand_loop6"
  "mlkem1024_indcpa_keypair_derand_loop6_exit" "X1" "X2" "X0";;

(* ------------------------------------------------------------------------- *)
(* The callees, and the lemmas for the inlined loops, as for subroutines.    *)
(* The matrix is generated without transposition, so the theorem is         *)
(* specialized to that case, as for gcc 12 -O2.                             *)
(* ------------------------------------------------------------------------- *)

let KP4_SUB_TAC th =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th);;

let LOCAL_SHA3_512_TAC =
  KP4_SUB_TAC MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_GEN_MATRIX_TAC =
  KP4_SUB_TAC
   (INDCPA_GEN_MATRIX_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
     `word 0:int64`);;

let LOCAL_GETNOISE_TAC =
  KP4_SUB_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_NTT_TAC =
  KP4_SUB_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_MULCACHE_TAC =
  KP4_SUB_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_BASEMUL_TAC =
  KP4_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  KP4_SUB_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_TOBYTES_TAC =
  KP4_SUB_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let KP4_LEMMA_TAC name ilist n =
  USE_THEN name (fun th -> KP4_SUB_TAC th ilist n);;

(*** The vectors of constants of the tomont loops, from the image ***)

let KP4_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mlkem1024_indcpa_keypair_derand_const2";
    layout "mlk_poly_invntt_tomont_c_const2"];;

let KP4_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the matrix as  *)
(* given by SampleNTT, the bounds on the inputs of the multiplications, the  *)
(* rows of the matrix-vector product, and rho in the public key, and the     *)
(* test of the loop over the rows, whose pointers are at constant offsets    *)
(* from the stack pointer, so the loop is simply unrolled.                   *)
(* ------------------------------------------------------------------------- *)

let KP4_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (4 * r + j))):int64" b) in
  SUBGOAL_THEN
   `!r j n. r < 4 /\ j < 4 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word j; word r]) n /\
                mlkem_sample_ntt (APPEND rho [word j; word r]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r j n. r < 4 /\ j < 4 /\ n < 256
            ==> ival((AM:num->int16)(1024 * r + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word j; word r]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `1024 * r + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word j; word r]`;
                  `k:num`; `n:num`]
                 MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let KP4_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!r j n. r < 4 /\ j < 4 /\ n < 256
                     ==> ival((AM:num->int16)(1024 * r + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word j; word r]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let KP4_PT_GOAL = `!r p. r < 4 /\ p < 128
            ==> (ival((PT:num->int16)(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival((MC:num->int16)(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival((SH:num->int16)(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(SH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(SH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p))))) (mod &3329) /\
                (ival(PT(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(SH(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(SH(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(SH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(SH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(SH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(SH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(SH(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p + 1))))) (mod &3329)`;;

let KP4_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 4096 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`1024`; `4`; `m:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1024 * 4 = 4096`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `4`; `q:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let KP4_BASEMUL_DEFS =
  [basemul4_even; basemul4_odd; pmul_acc4; pmull_acc4; pmull];;

let KP4_PT_TAC b s =
  INDCPA_GHOST_TAC "PT" (b + 10240) 1024 s THEN
  SUBGOAL_THEN KP4_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMULK_ROW_TAC 4 "PT" (b + 10240 + 512 * r)
                     "ambound" (map (KP4_AM_INST r) [0;1;2;3])
                     KP4_BASEMUL_DEFS) [0;1;2;3]);
    ALL_TAC];;

let KP4_PC_TAC s =
  let pcs = mk_comb(`read PC`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = pcs then
      ASSUME_TAC(CONV_RULE(RAND_CONV
       (REWRITE_CONV
         [WORD_RULE `word_sub (word_add (s:int64) x) (word_add s y) =
                     word_sub x y`] THENC
        ONCE_DEPTH_CONV WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
        REWRITE_CONV[])) th)
    else NO_TAC);;

let KP4_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1568 = 1536 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:byte list`; `rho:byte list`; `sigma:byte list`;
                `SH:num->int16`; `EH:num->int16`; `MC:num->int16`;
                `PT:num->int16`; `PT2:num->int16`; `TR:num->int16`;
                `SR:num->int16`] KPKE_KEYGEN_K4_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `FST(mlkem_g(APPEND d [word 4])) = rho`);
                  GSYM(ASSUME `SND(mlkem_g(APPEND d [word 4])) = sigma`);
                  PAIR];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]];;


(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees), as for gcc 12 -O2, with the same frame. The      *)
(* proof is by cases on whether the stack pointer is a multiple of 32, which *)
(* gives the address b of the buffers, at offsets 0 (the matrix), 8192 (s),  *)
(* 10240 (t), 12288 (e), 14336 (the multiplication cache), 15360 (rho and    *)
(* sigma) and 15424 (the input of SHA3-512).                                 *)
(* ------------------------------------------------------------------------- *)

let KP4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19360 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19360):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  UNDISCH_TAC
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 4])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 4]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 4]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC] THEN
  X_CHOOSE_THEN `ft:int64->num->(uarch_event)list`
    (LABEL_TAC "H_TOMONT") KP4_TOMONT THEN
  X_CHOOSE_THEN `fa:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD") KP4_ADD;;

let KP4_PART v j = if j = 0 then mk_var(v,`:num->int16`) else
  subst [mk_small_numeral(256 * j),`n:num`; mk_var(v,`:num->int16`),
         `v:num->int16`] `\i. (v:num->int16)(n + i)`;;

let KP4_CASE_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = KP4_SP n in
  let part = KP4_PART in
  ENSURES_INIT_TAC "s0" THEN
  KP4_HALVES_TAC `coins:int64` "d" THEN

  (*** The setup, the input to SHA3-512 and the call ***)

  ARM_STEPS_TAC KP4_EXEC (1--11) THEN KP4_BUFFER_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (12--25) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (26--35) THEN
  KP4_INPUT_TAC b `s35:armstate` THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP4_EXEC [36] THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND d [word 4]:byte list`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  KP4_G_TAC THEN

  (*** The matrix ***)

  ARM_STEPS_TAC KP4_EXEC (38--41) THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 42 THEN
  INDCPA_GHOST_TAC "AM" b 4096 (st 42) THEN
  KP4_MATRIX_TAC b `s42:armstate` THEN

  (*** The noise, s and e from two calls with four outputs ***)

  ARM_STEPS_TAC KP4_EXEC (43--60) THEN
  INDCPA_NONZERO_TAC 19360 (b + 9728) THEN INDCPA_NONCE_TAC 3 THEN
  INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 3:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 61 THEN
  INDCPA_NOISE_TAC "S0" (b + 8192) 4 "sigma" "word j" (st 61) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (62--75) THEN
  INDCPA_NONZERO_TAC 19360 (b + 13824) THEN INDCPA_NONCE_TAC 7 THEN
  INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 7:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 76 THEN
  INDCPA_NOISE_TAC "E0" (b + 12288) 4 "sigma" "word(4 + j)" (st 76) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs of s and e ***)

  POLYVEC_GHOST_SPLIT_TAC "S0" (b + 8192) 4 (st 76) THEN
  POLYVEC_GHOST_SPLIT_TAC "E0" (b + 12288) 4 (st 76) THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k1) THEN
    LOCAL_NTT_TAC [`read X0 s`; part "S0" j; `pc:num`; `read X30 s`]
      (k1 + 1)) [0,77,78; 1,80,84; 2,86,88; 3,90,92] THEN
  POLYVEC_INLINE_JOIN_TAC 4 [] (PV_NTT_POST 4 (sp(b + 8192)) "S0" (st 93))
  THEN
  INDCPA_NTT_TAC "SH" (b + 8192) 4 "S0" "sigma" "word j" (st 93) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "S0" 1024 THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k1) THEN
    LOCAL_NTT_TAC [`read X0 s`; part "E0" j; `pc:num`; `read X30 s`]
      (k1 + 1)) [0,94,95; 1,97,98; 2,100,102; 3,104,105] THEN
  POLYVEC_INLINE_JOIN_TAC 4 [] (PV_NTT_POST 4 (sp(b + 12288)) "E0" (st 106))
  THEN
  INDCPA_NTT_TAC "EH" (b + 12288) 4 "E0" "sigma" "word(4 + j)" (st 106) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "E0" 1024 THEN

  (*** The multiplication cache, in a loop of four calls ***)

  POLYVEC_GHOST_SPLIT_TAC "SH" (b + 8192) 4 (st 106) THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC KP4_EXEC ((107 + 8 * q)--(110 + 8 * q)) THEN
    LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; part "SH" q; `pc:num`;
                        `read X30 s`] (111 + 8 * q) THEN
    ARM_STEPS_TAC KP4_EXEC ((112 + 8 * q)--(114 + 8 * q)) THEN
    KP4_PC_TAC (st(114 + 8 * q))) [0;1;2;3] THEN
  POLYVEC_INLINE_JOIN_TAC 4 []
   (PV_MULCACHE_POST 4 (sp(b + 14336)) "SH" (st 138)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 14336) 4 "SH" (st 138) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "SH" 1024 THEN

  (*** The matrix-vector product, one row per iteration of the loop ***)

  ARM_STEPS_TAC KP4_EXEC (139--143) THEN
  MAP_EVERY (fun q ->
    let a = (b + 2048 * q,"AM",1024 * q)
    and y = (b + 8192,"SH") and t = (b + 14336,"MC") in
    ARM_STEPS_TAC KP4_EXEC ((144 + 10 * q)--(149 + 10 * q)) THEN
    INDCPA_BASEMULK_PRE_TAC 4 a y t (st(149 + 10 * q)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("AM",1024 * q) "SH" "MC")
      (150 + 10 * q) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 4 a y t THEN
    ARM_STEPS_TAC KP4_EXEC ((151 + 10 * q)--(153 + 10 * q)) THEN
    KP4_PC_TAC (st(153 + 10 * q))) [0;1;2;3] THEN
  KP4_AM_BOUND_TAC THEN KP4_PT_TAC b (st 183) THEN

  (*** The Montgomery form of t, in the inlined loops, four iterations of
       the outer one ***)

  POLYVEC_GHOST_SPLIT_TAC "PT" (b + 10240) 4 (st 183) THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    KP4_CONSTANTS THEN
  ARM_STEPS_TAC KP4_EXEC (184--184) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (185--189) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (190--191) THEN
  MAP_EVERY (fun r ->
    ARM_STEPS_TAC KP4_EXEC ((192 + 6 * r)--(193 + 6 * r)) THEN
    KP4_LEMMA_TAC "H_TOMONT"
     [`read events s`; `read X0 s`; part "PT" r; `pc:num`] (194 + 6 * r) THEN
    ARM_STEPS_TAC KP4_EXEC ((195 + 6 * r)--(197 + 6 * r))) [0;1;2;3] THEN
  POLYVEC_INLINE_JOIN_TAC 4 [tomont_3329; o_THM]
   (PV_TOMONT_POST 4 (sp(b + 10240)) "PT" (st 215)) THEN
  INDCPA_TOMONT_TAC "PT2" (b + 10240) 1024 "PT" (st 215) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "PT" 1024 THEN

  (*** Adding e, in the inlined loops, four iterations of the outer one ***)

  POLYVEC_GHOST_SPLIT_TAC "PT2" (b + 10240) 4 (st 215) THEN
  POLYVEC_GHOST_SPLIT_TAC "EH" (b + 12288) 4 (st 215) THEN
  ARM_STEPS_TAC KP4_EXEC (216--217) THEN
  MAP_EVERY (fun r ->
    ARM_STEPS_TAC KP4_EXEC ((218 + 7 * r)--(219 + 7 * r)) THEN
    KP4_LEMMA_TAC "H_ADD"
     [`read events s`; `read X1 s`; `read X2 s`; part "PT2" r; part "EH" r;
      `pc:num`] (220 + 7 * r) THEN
    ARM_STEPS_TAC KP4_EXEC ((221 + 7 * r)--(224 + 7 * r)) THEN
    KP4_PC_TAC (st(224 + 7 * r))) [0;1;2;3] THEN
  POLYVEC_GHOST_DROP_ALL_TAC "PT2" 1024 THEN
  POLYVEC_GHOST_DROP_ALL_TAC "EH" 1024 THEN

  (*** The reductions of t and s ***)

  MAP_EVERY (fun (j,k0,k1) ->
    let x = if j = 0 then
      `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)` else
      subst [mk_small_numeral(256 * j),`n:num`]
       `\i. word_add ((PT2:num->int16)(n + i)) ((EH:num->int16)(n + i))` in
    ARM_STEPS_TAC KP4_EXEC (k0--k1) THEN
    LOCAL_REDUCE_TAC [`read X0 s`; x; `pc:num`; `read X30 s`] (k1 + 1))
   [0,246,247; 1,249,250; 2,252,254; 3,256,257] THEN
  POLYVEC_INLINE_JOIN_TAC 4 []
   (PV_REDUCE_POST 4 (sp(b + 10240))
     "\\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 258)) THEN
  INDCPA_REDUCE_TAC "TR" (b + 10240) 1024
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 258) THEN
  POLYVEC_GHOST_SPLIT_TAC "SH" (b + 8192) 4 (st 258) THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k1) THEN
    LOCAL_REDUCE_TAC [`read X0 s`; part "SH" j; `pc:num`; `read X30 s`]
      (k1 + 1)) [0,259,260; 1,262,263; 2,265,266; 3,268,270] THEN
  POLYVEC_INLINE_JOIN_TAC 4 [] (PV_REDUCE_POST 4 (sp(b + 8192)) "SH" (st 271))
  THEN
  INDCPA_REDUCE_TAC "SR" (b + 8192) 1024 "(SH:num->int16) i" (st 271) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "SH" 1024 THEN

  (*** The encodings of the keys, in two loops of calls, the second rotated
       (two calls per iteration, exit in the middle) ***)

  INDCPA_TOBYTES_PRE_TAC "SR" (b + 8192) 1024 (st 271) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN (INDCPA_SP(b + 8192)) 4
  THEN INLINE_SP_NORMALIZE_TAC THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC KP4_EXEC ((272 + 9 * q)--(275 + 9 * q)) THEN
    LOCAL_TOBYTES_TAC
     [`read X0 s`; `read X1 s`;
      subst [mk_small_numeral(256 * q),`n:num`]
       `SUB_LIST(n,256) (list_of_seq (SR:num->int16) 1024)`; `pc:num`;
      `read X30 s`] (276 + 9 * q) THEN
    ARM_STEPS_TAC KP4_EXEC ((277 + 9 * q)--(279 + 9 * q)) THEN
    KP4_PC_TAC (st(279 + 9 * q))) [0;1;2;3] THEN
  POLYVEC_TOBYTES_JOIN_TAC 4 `sk:int64` `list_of_seq (SR:num->int16) 1024`
    `s306:armstate` THEN
  INDCPA_TOBYTES_POST_TAC "SR" 1024 `\i. ival((SH:num->int16) i)` THEN
  INDCPA_TOBYTES_PRE_TAC "TR" (b + 10240) 1024 (st 306) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN (INDCPA_SP(b + 10240)) 4
  THEN INLINE_SP_NORMALIZE_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (307--312) THEN
  LOCAL_TOBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `SUB_LIST(0,256) (list_of_seq (TR:num->int16) 1024)`; `pc:num`;
    `read X30 s`] 313 THEN
  ARM_STEPS_TAC KP4_EXEC (314--316) THEN KP4_PC_TAC (st 316) THEN
  MAP_EVERY (fun j ->
    let k0 = 317 + 10 * (j - 1) in
    ARM_STEPS_TAC KP4_EXEC (k0--(k0 + 4)) THEN
    LOCAL_TOBYTES_TAC
     [`read X0 s`; `read X1 s`;
      subst [mk_small_numeral(256 * j),`n:num`]
       `SUB_LIST(n,256) (list_of_seq (TR:num->int16) 1024)`; `pc:num`;
      `read X30 s`] (k0 + 5) THEN
    ARM_STEPS_TAC KP4_EXEC ((k0 + 6)--(k0 + 8)) THEN
    KP4_PC_TAC (st(k0 + 8))) [1;2;3] THEN
  POLYVEC_TOBYTES_JOIN_TAC 4 `pk:int64` `list_of_seq (TR:num->int16) 1024`
    `s345:armstate` THEN
  INDCPA_TOBYTES_POST_TAC "TR" 1024
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  KP4_HALVES_TAC (INDCPA_SP(b + 15360)) "rho" THEN
  ARM_STEPS_TAC KP4_EXEC (346--350) THEN KP4_RHO_TAC (st 350) THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KP4_EXEC
   [351,351; 357,360; 366,369; 375,378; 384,387] THEN
  ARM_STEPS_TAC KP4_EXEC (393--400) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (401--416) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk sk coins (d:byte list) guard mf mc ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 4])))
                            [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 19360),19360) /\
        PAIRWISE nonoverlapping
         [(pk,1568); (sk,1536); (word_sub stackpointer (word 19360),19360)] /\
        ALLPAIRS nonoverlapping
         [(pk,1568); (sk,1536); (word_sub stackpointer (word 19360),19360)]
         [(coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem1024_indcpa_keypair_derand) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk; sk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist d)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(pk,1568)) s =
                  num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
                  read (memory :> bytes(sk,1536)) s =
                  num_of_bytelist(SND(kpke_keygen mlkem1024 d)) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,1568); memory :> bytes(sk,1536);
                memory :> bytes(word_sub stackpointer (word 19360),19360)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem1024_gen_matrix) and the safety contract for memcpy, as   *)
(* for gcc 12 -O2. The events depend only on the addresses and on rho. The   *)
(* inner loops use the same lemmas as the correctness proof, with the        *)
(* contents of the memory as the data, and the vectors of constants of the   *)
(* tomont loop are read-only objects.                                        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KP_SAFE_TEMPLATE =
 `\(pk:int64) (sk:int64) (coins:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (stackpointer:int64) (returnaddress:int64) (rho:byte list).
   if aligned 32 stackpointer
   then f_ev_a pk sk coins guard mf mc pc stackpointer returnaddress rho
   else f_ev_u pk sk coins guard mf mc pc stackpointer returnaddress rho
   :(uarch_event)list`;;

let KP_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `coins:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `rho:byte list`];;

let KP4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP
              MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
              th) `word 0:int64`) "H_GM" THEN
         ASSUME_TAC(CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let gth = MATCH_MP
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP4_TOMONT "H_TOMONT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP4_ADD "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC KP_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19360):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  UNDISCH_TAC
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 4])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 4]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 4]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KP_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

(*** The contents of a polynomial at the address in a register, as the data
     of the lemmas for the loops ***)

let KP4_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;

let KP4_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  let rest0 = [`pc:num`; `read X30 s`] in
  let st n = "s"^string_of_int n in
  let call = KP4_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN
  KP4_HALVES_TAC `coins:int64` "d" THEN
  ARM_STEPS_TAC KP4_EXEC (1--11) THEN KP4_BUFFER_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (12--25) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (26--35) THEN
  KP4_INPUT_TAC b `s35:armstate` THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP4_EXEC [36] THEN
  call "H_SHA3"
   ([e; x 0; x 1; `APPEND d [word 4]:byte list`; `33`; `guard:int64`] @
    rest) 37 THEN
  KP4_G_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (38--41) THEN
  call "H_GM" ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest)
   42 THEN
  ARM_STEPS_TAC KP4_EXEC (43--60) THEN INLINE_GOT_TAC THEN
  INDCPA_NONZERO_TAC 19360 (b + 9728) THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest)
   61 THEN
  ARM_STEPS_TAC KP4_EXEC (62--75) THEN INLINE_GOT_TAC THEN
  INDCPA_NONZERO_TAC 19360 (b + 13824) THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest)
   76 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k1) THEN
    call "H_NTT" ([e; x 0] @ rest0) (k1 + 1))
   [77,78; 80,84; 86,88; 90,92; 94,95; 97,98; 100,102; 104,105] THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC KP4_EXEC ((107 + 8 * q)--(110 + 8 * q)) THEN
    call "H_MULCACHE" ([e; x 0; x 1] @ rest0) (111 + 8 * q) THEN
    ARM_STEPS_TAC KP4_EXEC ((112 + 8 * q)--(114 + 8 * q)) THEN
    KP4_PC_TAC (st(114 + 8 * q))) [0;1;2;3] THEN
  ARM_STEPS_TAC KP4_EXEC (139--143) THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC KP4_EXEC ((144 + 10 * q)--(149 + 10 * q)) THEN
    call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) (150 + 10 * q) THEN
    ARM_STEPS_TAC KP4_EXEC ((151 + 10 * q)--(153 + 10 * q)) THEN
    KP4_PC_TAC (st(153 + 10 * q))) [0;1;2;3] THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    KP4_CONSTANTS THEN
  ARM_STEPS_TAC KP4_EXEC (184--184) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (185--189) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (190--191) THEN
  MAP_EVERY (fun r ->
    ARM_STEPS_TAC KP4_EXEC ((192 + 6 * r)--(193 + 6 * r)) THEN
    call "H_TOMONT" [e; x 0; KP4_CONTENTS `X0`; `pc:num`] (194 + 6 * r) THEN
    ARM_STEPS_TAC KP4_EXEC ((195 + 6 * r)--(197 + 6 * r))) [0;1;2;3] THEN
  ARM_STEPS_TAC KP4_EXEC (216--217) THEN
  MAP_EVERY (fun r ->
    ARM_STEPS_TAC KP4_EXEC ((218 + 7 * r)--(219 + 7 * r)) THEN
    call "H_ADD"
     [e; x 1; x 2; KP4_CONTENTS `X1`; KP4_CONTENTS `X2`; `pc:num`]
     (220 + 7 * r) THEN
    ARM_STEPS_TAC KP4_EXEC ((221 + 7 * r)--(224 + 7 * r)) THEN
    KP4_PC_TAC (st(224 + 7 * r))) [0;1;2;3] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k1) THEN
    call "H_REDUCE" ([e; x 0] @ rest0) (k1 + 1))
   [246,247; 249,250; 252,254; 256,257; 259,260; 262,263; 265,266;
    268,270] THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC KP4_EXEC ((272 + 9 * q)--(275 + 9 * q)) THEN
    call "H_TOBYTES" ([e; x 0; x 1] @ rest0) (276 + 9 * q) THEN
    ARM_STEPS_TAC KP4_EXEC ((277 + 9 * q)--(279 + 9 * q)) THEN
    KP4_PC_TAC (st(279 + 9 * q))) [0;1;2;3] THEN
  ARM_STEPS_TAC KP4_EXEC (307--312) THEN
  call "H_TOBYTES" ([e; x 0; x 1] @ rest0) 313 THEN
  ARM_STEPS_TAC KP4_EXEC (314--316) THEN KP4_PC_TAC (st 316) THEN
  MAP_EVERY (fun j ->
    let k0 = 317 + 10 * (j - 1) in
    ARM_STEPS_TAC KP4_EXEC (k0--(k0 + 4)) THEN
    call "H_TOBYTES" ([e; x 0; x 1] @ rest0) (k0 + 5) THEN
    ARM_STEPS_TAC KP4_EXEC ((k0 + 6)--(k0 + 8)) THEN
    KP4_PC_TAC (st(k0 + 8))) [1;2;3] THEN
  KP4_HALVES_TAC (INDCPA_SP(b + 15360)) "rho" THEN
  ARM_STEPS_TAC KP4_EXEC (346--350) THEN KP4_RHO_TAC "s350" THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k) THEN LIBC_PLT_TAC KP4_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KP4_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KP_SAFE_ALLOWED) (k + 5))
   [351,351; 357,360; 366,369; 375,378; 384,387] THEN
  ARM_STEPS_TAC KP4_EXEC (393--400) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (401--416) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e pk sk coins (d:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH d = 32 /\
          (!i j. i < 4 /\ j < 4
                 ==> mlkem_samplentt_terminates
                      (APPEND (FST(mlkem_g(APPEND d [word 4])))
                              [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 19360),19360) /\
          PAIRWISE nonoverlapping
           [(pk,1568); (sk,1536);
            (word_sub stackpointer (word 19360),19360)] /\
          ALLPAIRS nonoverlapping
           [(pk,1568); (sk,1536);
            (word_sub stackpointer (word 19360),19360)]
           [(coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem1024_indcpa_keypair_derand) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    read (memory :> bytes(word_add pk (word 1536),32)) s =
                    num_of_bytelist(FST(mlkem_g(APPEND d [word 4]))) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk coins guard mf mc pc
                              (word_sub stackpointer (word 19360))
                              returnaddress
                              (FST(mlkem_g(APPEND d [word 4]))) /\
                       memaccess_inbounds e2
                        [coins,32; pk,1568; sk,1536;
                         word_sub stackpointer (word 19360),19360;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem1024_indcpa_keypair_derand_const2),16;
                         word(pc + mlk_poly_invntt_tomont_c_const2),16]
                        [pk,1568; sk,1536;
                         word_sub stackpointer (word 19360),19360]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1568); memory :> bytes(sk,1536);
                  memory :> bytes(word_sub stackpointer (word 19360),19360)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
