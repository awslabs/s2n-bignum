(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a vector of 4 polynomials into bytes, 12 bits per coefficient. *)
(* This is the code for mlkem1024_polyvec_tobytes from mlkem-native's        *)
(* portable C implementation compiled by clang 17 with -O3 (see              *)
(* mlkem_native/README.md), which calls mlkem_poly_tobytes for each of the   *)
(* polynomials, the last time as a tail call. It is verified in the whole    *)
(* image (see libmlkem.ml), using the theorems for mlkem_poly_tobytes in the *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_tobytes_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_polyvec_tobytes:
       +0x0: str     x30, [sp, #-32]!
       +0x4: stp     x20, x19, [sp, #16]
       +0x8: mov     x19, x1
       +0xc: mov     x20, x0
      +0x10: bl      mlkem_poly_tobytes
      +0x14: add     x0, x20, #0x180
      +0x18: add     x1, x19, #0x200
      +0x1c: bl      mlkem_poly_tobytes
      +0x20: add     x0, x20, #0x300
      +0x24: add     x1, x19, #0x400
      +0x28: bl      mlkem_poly_tobytes
      +0x2c: add     x0, x20, #0x480
      +0x30: add     x1, x19, #0x600
      +0x34: ldp     x20, x19, [sp, #16]
      +0x38: ldr     x30, [sp], #32
      +0x3c: b       mlkem_poly_tobytes
 ***)

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem1024_polyvec_tobytes"];;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem1024_polyvec_tobytes"];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let ALL_SUB_LIST = prove
 (`!P (l:A list) m n. ALL P l ==> ALL P (SUB_LIST(m,n) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES; ALL] THEN
  INDUCT_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; ALL]);;

let POLYVEC_TOBYTES_SPLIT_STMT =
  `!a (l:int16 list) s j.
        read (memory :> bytes(a,2048)) s = num_of_wordlist l /\ j < 4
        ==> read (memory :> bytes(word_add a (word(512 * j)),512)) s =
            num_of_wordlist (SUB_LIST(256 * j,256) l)`;;

let POLYVEC_TOBYTES_SPLIT = assume_spec POLYVEC_TOBYTES_SPLIT_STMT;;

let POLYVEC_TOBYTES_JOIN_STMT =
  `!r (l:int16 list) s.
        LENGTH l = 1024 /\
        (!j. j < 4
             ==> read (memory :> bytes(word_add r (word(384 * j)),384)) s =
                 num_of_wordlist
                  (MAP word_zx (SUB_LIST(256 * j,256) l):(12 word)list))
        ==> read (memory :> bytes(r,1536)) s =
            num_of_wordlist (MAP word_zx l:(12 word)list)`;;

let POLYVEC_TOBYTES_JOIN = assume_spec POLYVEC_TOBYTES_JOIN_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,1536); (a,2048); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,1536); (a,2048); (word_sub stackpointer (word 32),32)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem1024_polyvec_tobytes) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,2048)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 1024 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,1536)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1536);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_polyvec_tobytes_k4_signature =
  ([("r", "uint8_t[static 1536]", "false");
    ("a", "int16_t[static 1024]", "true")],
   "void",
   [("a", "1024", 2)],
   [("r", "1536", 1)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_polyvec_tobytes_k4_signature
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_EXEC;;

let LOCAL_TOBYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [r,1536; a,2048; word_sub stackpointer (word 32),32] /\
           ALLPAIRS nonoverlapping
           [r,1536; a,2048; word_sub stackpointer (word 32),32]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem1024_polyvec_tobytes) /\
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
                         [a,2048; r,1536; word_sub stackpointer (word 32),32]
                         [r,1536; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                [memory :> bytes (r,1536);
                 memory :> bytes (word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_poly_tobytes, for the callers that branch on the result.         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FULL_TAC ilist n =
  REMOVE_THEN "H_POLY" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      (`e:(uarch_event)list`::ilist) n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_POLY" safety_th]);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
          [(r,1536); (a,2048); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
          [(r,1536); (a,2048); (word_sub stackpointer (word 32),32)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem1024_polyvec_tobytes) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,2048)) s = num_of_wordlist l /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 1024 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,1536)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 =
                     f_events a r pc (word_sub stackpointer (word 32))
                     returnaddress /\
                     memaccess_inbounds e2
                     [a,2048; r,1536; word_sub stackpointer (word 32),32]
                     [r,1536; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1536);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
