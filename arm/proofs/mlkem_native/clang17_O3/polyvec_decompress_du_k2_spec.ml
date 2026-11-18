(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a vector of 2 polynomials from 10 bits per coefficient.  *)
(* This is the code for mlkem512_polyvec_decompress_du from mlkem-native's   *)
(* portable C implementation compiled by clang 17 with -O3 (see              *)
(* mlkem_native/README.md), which calls mlkem_poly_decompress_d10 for each   *)
(* of the polynomials, the last time as a tail call. It is verified in the   *)
(* whole image (see libmlkem.ml), using the theorems                         *)
(* for mlkem_poly_decompress_d10 in the image.                               *)
(*                                                                           *)
(* As at gcc -O2, mlkem_poly_decompress_d10 loads constants from the         *)
(* read-only data (here 96 bytes), so the safety theorem has a read-only     *)
(* region for them.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_decompress_d10_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem512_polyvec_decompress_du:
       +0x0: str     x30, [sp, #-32]!
       +0x4: stp     x20, x19, [sp, #16]
       +0x8: mov     x19, x1
       +0xc: mov     x20, x0
      +0x10: bl      mlkem_poly_decompress_d10
      +0x14: add     x0, x20, #0x200
      +0x18: add     x1, x19, #0x140
      +0x1c: ldp     x20, x19, [sp, #16]
      +0x20: ldr     x30, [sp], #32
      +0x24: b       mlkem_poly_decompress_d10
 ***)

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem512_polyvec_decompress_du"];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_DECOMPRESS_DU_SPLIT_STMT =
  `!a n s j.
        read (memory :> bytes(a,640)) s = n /\ j < 2
        ==> read (memory :> bytes(word_add a (word(320 * j)),320)) s =
            (n DIV 2 EXP (2560 * j)) MOD 2 EXP 2560`;;

let POLYVEC_DECOMPRESS_DU_SPLIT =
  assume_spec POLYVEC_DECOMPRESS_DU_SPLIT_STMT;;

let POLYVEC_DECOMPRESS_DU_FIELD_STMT =
  `!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 2560 DIV 2 EXP (10 * i)) MOD 2 EXP 10 =
            (n DIV 2 EXP (k + 10 * i)) MOD 2 EXP 10`;;

let POLYVEC_DECOMPRESS_DU_FIELD =
  assume_spec POLYVEC_DECOMPRESS_DU_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DECOMPRESS_D10_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,1024); (a,640); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,1024); (a,640); (word_sub stackpointer (word 32),32)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem512_polyvec_decompress_du) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,640)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 512
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_decompress_du_k2_signature =
  ([("r", "int16_t[static 512]", "false");
    ("a", "uint8_t[static 640]", "true")],
   "void",
   [("a", "640", 1)],
   [("r", "512", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:
      [`word(pc + mlkem_poly_decompress_d10_consts):int64`,
       `mlkem_poly_decompress_d10_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_polyvec_decompress_du_k2_signature
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_EXEC;;

let LOCAL_DECOMPRESS_D10_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [r,1024; a,640; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [r,1024; a,640; word_sub stackpointer (word 32),32]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem512_polyvec_decompress_du) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a r pc (word_sub stackpointer (word 32))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,640; r,1024; word_sub stackpointer (word 32),32;
                          word (pc + mlkem_poly_decompress_d10_consts),
                          mlkem_poly_decompress_d10_consts_size]
                         [r,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (r,1024);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
