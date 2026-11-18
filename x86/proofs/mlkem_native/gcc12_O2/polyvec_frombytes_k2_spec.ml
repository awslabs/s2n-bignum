(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 2 polynomials from bytes, 12 bits per            *)
(* coefficient. This is the code for mlkem512_polyvec_frombytes from         *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md), which calls mlkem_poly_frombytes for each of the *)
(* polynomials, the last time as a tail call. It is verified in the whole    *)
(* image (see libmlkem.ml), using the theorems for mlkem_poly_frombytes in   *)
(* the image.                                                                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_frombytes_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem512_polyvec_frombytes:
       +0x0: push   rbp
       +0x1: mov    rbp,rsi
       +0x4: push   rbx
       +0x5: mov    rbx,rdi
       +0x8: sub    rsp,0x8
       +0xc: call   <mlkem_poly_frombytes>
      +0x11: add    rsp,0x8
      +0x15: lea    rsi,[rbp+0x180]
      +0x1c: lea    rdi,[rbx+0x200]
      +0x23: pop    rbx
      +0x24: pop    rbp
      +0x25: jmp    <mlkem_poly_frombytes>
 ***)

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem512_polyvec_frombytes"];;

(* ------------------------------------------------------------------------- *)
(* The input and output for the polynomials, as parts of those for the       *)
(* vector.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_FROMBYTES_SPLIT_STMT =
  `!a n s j.
        read (memory :> bytes(a,768)) s = n /\ j < 2
        ==> read (memory :> bytes(word_add a (word(384 * j)),384)) s =
            (n DIV 2 EXP (3072 * j)) MOD 2 EXP 3072`;;

let POLYVEC_FROMBYTES_SPLIT =
  assume_spec POLYVEC_FROMBYTES_SPLIT_STMT;;

let POLYVEC_FROMBYTES_FIELD_STMT =
  `!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 3072 DIV 2 EXP (12 * i)) MOD 2 EXP 12 =
            (n DIV 2 EXP (k + 12 * i)) MOD 2 EXP 12`;;

let POLYVEC_FROMBYTES_FIELD =
  assume_spec POLYVEC_FROMBYTES_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FROMBYTES_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmlkem_size); (a,768)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,libmlkem_size); (a,768); (r,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem512_polyvec_frombytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,768)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 512
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_FROMBYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,1024)) [(word pc,libmlkem_size); (a,768)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,libmlkem_size); (a,768); (r,1024)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem512_polyvec_frombytes) /\
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
                          [a,768; r,1024; word_sub stackpointer (word 32),40]
                          [r,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1024);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_poly_frombytes, for mlkem512_check_pk, whose result the          *)
(* encapsulation branches on.                                                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FULL_TAC ilist n =
  REMOVE_THEN "H_POLY" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist) n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_POLY" safety_th]);;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a n pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,1024)) [(word pc,libmlkem_size); (a,768)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [(word pc,libmlkem_size); (a,768); (r,1024)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem512_polyvec_frombytes) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,768)) s = n /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 512
                         ==> read(memory :> bytes16
                                   (word_add r (word(2 * i)))) s =
                             word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,768; r,1024; word_sub stackpointer (word 32),40]
                          [r,1024; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1024);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
