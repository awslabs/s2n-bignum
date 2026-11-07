(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Computation of the multiplication cache for a vector of 4 polynomials.    *)
(* This is the code for mlkem1024_polyvec_mulcache_compute from              *)
(* mlkem-native's portable C implementation compiled by clang 17 with -O3    *)
(* (see mlkem_native/README.md), which calls mlkem_poly_mulcache_compute for *)
(* each of the polynomials, the last time as a tail call. It is verified in  *)
(* the whole image (see libmlkem.ml), using the theorems for                 *)
(* mlkem_poly_mulcache_compute in the image. As for that function, the       *)
(* theorem of constant time and memory safety has the vectors of constants   *)
(* mlkem_poly_mulcache_compute_consts as a read-only region besides the      *)
(* zetas, which the gcc 12 -O2 theorem does not have.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_mulcache_compute_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_polyvec_mulcache_compute:
       +0x0: str     x30, [sp, #-32]!
       +0x4: stp     x20, x19, [sp, #16]
       +0x8: mov     x19, x1
       +0xc: mov     x20, x0
      +0x10: bl      <mlkem_poly_mulcache_compute>
      +0x14: add     x0, x20, #0x100
      +0x18: add     x1, x19, #0x200
      +0x1c: bl      <mlkem_poly_mulcache_compute>
      +0x20: add     x0, x20, #0x200
      +0x24: add     x1, x19, #0x400
      +0x28: bl      <mlkem_poly_mulcache_compute>
      +0x2c: add     x0, x20, #0x300
      +0x30: add     x1, x19, #0x600
      +0x34: ldp     x20, x19, [sp, #16]
      +0x38: ldr     x30, [sp], #32
      +0x3c: b       <mlkem_poly_mulcache_compute>
 ***)

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem1024_polyvec_mulcache_compute"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!dst src x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(dst,1024); (src,2048); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(dst,1024); (src,2048); (word_sub stackpointer (word 32),32)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem1024_polyvec_mulcache_compute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; src] s /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add src (word(2 * i))))
                            s = x i)
             (\s. read PC s = returnaddress /\
                  !j. j < 4
                      ==> !i. i < 128
                              ==> let z_i =
                                    read(memory :> bytes16
                                     (word_add dst (word(256 * j + 2 * i)))) s
                                  in (ival z_i ==
                                      mulcache (\n. ival(x(256 * j + n))) i)
                                     (mod &3329) /\
                                     abs(ival z_i) <= &3328)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(dst,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_mulcache_compute_k4_signature =
  ([("x", "int16_t[static 512]", "false");
    ("a", "int16_t[static 1024]", "true")],
   "void",
   [("a", "1024", 2)],
   [("x", "512", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`;
                       `word(pc + mlkem_poly_mulcache_compute_consts):int64`,
                       `mlkem_poly_mulcache_compute_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_polyvec_mulcache_compute_k4_signature
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_EXEC;;

let LOCAL_MULCACHE_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `dst:int64`; `src:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [dst,1024; src,2048; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [dst,1024; src,2048; word_sub stackpointer (word 32),32]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s =
                      word (pc + mlkem1024_polyvec_mulcache_compute) /\
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
                         (word_sub stackpointer (word 32))
                         returnaddress /\
                         memaccess_inbounds e2
                         [src,2048; dst,1024;
                          word_sub stackpointer (word 32),32;
                          word (pc + rodata_mlk_zetas),256;
                          word (pc + mlkem_poly_mulcache_compute_consts),
                          mlkem_poly_mulcache_compute_consts_size]
                         [dst,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (dst,1024);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
