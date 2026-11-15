(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a vector of 3 polynomials into bytes, 12 bits per coefficient. *)
(* This is the code for mlkem768_polyvec_tobytes from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_tobytes for each of the   *)
(* polynomials, the last time as a tail call. It is verified in the whole    *)
(* image (see libmlkem.ml), using the theorems for mlkem_poly_tobytes in the *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_tobytes_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem768_polyvec_tobytes:
       +0x0: push   rbp
       +0x1: mov    rbp,rsi
       +0x4: push   rbx
       +0x5: mov    rbx,rdi
       +0x8: sub    rsp,0x8
       +0xc: call   <mlkem_poly_tobytes>
      +0x11: lea    rsi,[rbp+0x200]
      +0x18: lea    rdi,[rbx+0x180]
      +0x1f: call   <mlkem_poly_tobytes>
      +0x24: add    rsp,0x8
      +0x28: lea    rsi,[rbp+0x400]
      +0x2f: lea    rdi,[rbx+0x300]
      +0x36: pop    rbx
      +0x37: pop    rbp
      +0x38: jmp    <mlkem_poly_tobytes>
 ***)

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem768_polyvec_tobytes"];;

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
        read (memory :> bytes(a,1536)) s = num_of_wordlist l /\ j < 3
        ==> read (memory :> bytes(word_add a (word(512 * j)),512)) s =
            num_of_wordlist (SUB_LIST(256 * j,256) l)`;;

let POLYVEC_TOBYTES_SPLIT =
  assume_spec POLYVEC_TOBYTES_SPLIT_STMT;;

let POLYVEC_TOBYTES_JOIN_STMT =
  `!r (l:int16 list) s.
        LENGTH l = 768 /\
        (!j. j < 3
             ==> read (memory :> bytes(word_add r (word(384 * j)),384)) s =
                 num_of_wordlist
                  (MAP word_zx (SUB_LIST(256 * j,256) l):(12 word)list))
        ==> read (memory :> bytes(r,1152)) s =
            num_of_wordlist (MAP word_zx l:(12 word)list)`;;

let POLYVEC_TOBYTES_JOIN =
  assume_spec POLYVEC_TOBYTES_JOIN_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_TOBYTES_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,1152)) [(word pc,libmlkem_size); (a,1536)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,libmlkem_size); (a,1536); (r,1152)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem768_polyvec_tobytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,1536)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 768 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,1152)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1152);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_TOBYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,1152)) [(word pc,libmlkem_size); (a,1536)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,libmlkem_size); (a,1536); (r,1152)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem768_polyvec_tobytes) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,1536; r,1152; word_sub stackpointer (word 32),40]
                          [r,1152; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1152);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_poly_tobytes, for mlkem768_check_pk, whose result the            *)
(* encapsulation branches on.                                                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FULL_TAC ilist n =
  REMOVE_THEN "H_POLY" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist) n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_POLY" safety_th]);;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,1152)) [(word pc,libmlkem_size); (a,1536)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,libmlkem_size); (a,1536); (r,1152)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem768_polyvec_tobytes) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,1536)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (LENGTH l = 768 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,1152)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,1536; r,1152; word_sub stackpointer (word 32),40]
                          [r,1152; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1152);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
