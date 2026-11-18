(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* This is the code for mlkem_poly_reduce from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/layout.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_reduce","mlkem_poly_reduce"]);;

(**** print_literal_from_elf
        "x86/mlkem_native/gcc12_O2/poly_reduce.o";;
 ****)

let mlkem_native_poly_reduce_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_poly_reduce_gcc12_O2_mc"
  "x86/mlkem_native/gcc12_O2/poly_reduce.o"
[
  0x48; 0x89; 0xf9;        (* MOV (% rcx) (% rdi) *)
  0x48; 0x8d; 0xb7; 0x00; 0x02; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rdi,512)) *)
  0x66; 0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0xbf; 0x11;        (* MOVSX (% edx) (Memop Word (%% (rcx,0))) *)
  0x89; 0xd0;              (* MOV (% eax) (% edx) *)
  0x69; 0xd2; 0xbf; 0x4e; 0x00; 0x00;
                           (* IMUL3 (% edx) (% edx,Imm32 (word 20159)) *)
  0x81; 0xc2; 0x00; 0x00; 0x00; 0x02;
                           (* ADD (% edx) (Imm32 (word 33554432)) *)
  0xc1; 0xfa; 0x1a;        (* SAR (% edx) (Imm8 (word 26)) *)
  0x66; 0x69; 0xd2; 0xff; 0xf2;
                           (* IMUL3 (% dx) (% dx,Imm16 (word 62207)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x0f; 0xbf; 0xc2;        (* MOVSX (% eax) (% dx) *)
  0xc1; 0xe8; 0x10;        (* SHR (% eax) (Imm8 (word 16)) *)
  0xf7; 0xd8;              (* NEG (% eax) *)
  0x8d; 0xba; 0x01; 0x0d; 0x00; 0x00;
                           (* LEA (% edi) (%% (rdx,3329)) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x48; 0x83; 0xc1; 0x02;  (* ADD (% rcx) (Imm8 (word 2)) *)
  0x31; 0xd7;              (* XOR (% edi) (% edx) *)
  0x21; 0xf8;              (* AND (% eax) (% edi) *)
  0x31; 0xd0;              (* XOR (% eax) (% edx) *)
  0x66; 0x89; 0x41; 0xfe;  (* MOV (Memop Word (%% (rcx,18446744073709551614)))
                                  (% ax) *)
  0x48; 0x39; 0xf1;        (* CMP (% rcx) (% rsi) *)
  0x75; 0xc1;              (* JNE (Imm8 (word 193)) *)
  0xc3                     (* RET *)
];;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_reduce_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The value computed for each coefficient.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The Barrett reduction as compiled: the quotient t is computed in a
 *** 32-bit register and its bottom 16 bits multiplied by -3329 in the
 *** 16-bit one, the product p, then the input is added as 32 bits r. Only
 *** the bottom 16 bits of r matter, and they are the reduction "barred".
 ***)

let BARRETT_GCC12_O2_STMT =
  `!(x:int16) (t:int32) (p:int16).
     word_zx(word_add
              (word_zx (word_join
                          (word_subword (word_zx t:int64) (16,48):48 word)
                          p:int64):int32)
              (word_sx x:int32)):int16 =
     word_add x p`;;

let BARRETT_GCC12_O2 =
  assume_spec BARRETT_GCC12_O2_STMT;;

(*** The conditional addition of 3329, mlk_scalar_signed_to_unsigned_q,
 *** as compiled, applied to the 32-bit result r of the Barrett reduction
 ***)

let CONDADD_GCC12_O2_STMT =
  `!r:int32.
     word_zx
      (word_xor
        (word_and
          (word_ishr
            (word_neg (word_ushr (word_sx (word_zx r:int16):int32) 16)) 16)
          (word_xor (word_sx (word_add (word_zx r:int64) (word 3329)):int32)
                    r))
        r):int16 =
     let w = word_zx r:int16 in
     word_add w (word_and (word_ishr w 15) (word 3329))`;;

let CONDADD_GCC12_O2 =
  assume_spec CONDADD_GCC12_O2_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT_STMT =
  `!a x pc.
        nonoverlapping (word pc,poly_reduce_size) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_gcc12_O2_mc /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = word(pc + poly_reduce_ret) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
        nonoverlapping (word pc,poly_reduce_size) (a,512) /\
        nonoverlapping (stackpointer,8) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_gcc12_O2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_reduce ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE_STMT =
  `exists f_events.
       forall e a pc.
           nonoverlapping (word pc,poly_reduce_size) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + poly_reduce_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc /\
                         memaccess_inbounds e2 [a,512] [a,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           nonoverlapping (word pc,poly_reduce_size) (a,512) /\
           nonoverlapping (stackpointer,8) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_reduce_gcc12_O2_mc
    (layout "mlkem_poly_reduce") [];;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        nonoverlapping (word pc,libmlkem_size) (a,512) /\
        nonoverlapping (stackpointer,8) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_reduce) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           nonoverlapping (word pc,libmlkem_size) (a,512) /\
           nonoverlapping (stackpointer,8) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_reduce) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* modulus check of the encapsulation key, whose result the encapsulation    *)
(* branches on. The loop is that of the correctness proof, but with the loop *)
(* test at the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires,    *)
(* and the versions as a subroutine and in the image follow.                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_FULL_STMT =
  `exists f_events.
       forall e a x pc.
           nonoverlapping (word pc,poly_reduce_size) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [a] s /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add a (word(2 * i)))) s = x i) /\
                    read events s = e)
               (\s. read RIP s = word (pc + poly_reduce_ret) /\
                    (!i. i < 256
                         ==> ival(read(memory :> bytes16
                                    (word_add a (word(2 * i)))) s) =
                             ival(x i) rem &3329) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc /\
                         memaccess_inbounds e2 [a,512] [a,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_FULL =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_FULL_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a x pc stackpointer returnaddress.
           nonoverlapping (word pc,poly_reduce_size) (a,512) /\
           nonoverlapping (stackpointer,8) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add a (word(2 * i)))) s = x i) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> ival(read(memory :> bytes16
                                    (word_add a (word(2 * i)))) s) =
                             ival(x i) rem &3329) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a x pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           nonoverlapping (word pc,libmlkem_size) (a,512) /\
           nonoverlapping (stackpointer,8) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_reduce) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add a (word(2 * i)))) s = x i) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> ival(read(memory :> bytes16
                                    (word_add a (word(2 * i)))) s) =
                             ival(x i) rem &3329) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
