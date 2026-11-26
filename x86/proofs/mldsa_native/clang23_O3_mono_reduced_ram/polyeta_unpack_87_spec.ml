(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 3 bits per coefficient, of 2 - a: the      *)
(* statement. This is the code for mldsa87_polyeta_unpack                    *)
(* (mld_polyeta_unpack in poly_kl.c with MLDSA_ETA = 2, for ML-DSA-87) from  *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which reads 3     *)
(* bytes for each 8 coefficients, stores the masked fields and then 2 - a    *)
(* over them, one coefficient at a time (the last one only once). It is      *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_polyeta_unpack_2 of common/mldsa_native_packing.ml. It is also shown  *)
(* to be constant time and memory safe. The function saves RBP, R14 and RBX  *)
(* in the 24 bytes below the return address and uses nothing else of the     *)
(* stack.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyeta_unpack:
       +0x0: push    %rbp
       +0x1: push    %r14
       +0x3: push    %rbx
       +0x4: xor     %eax,%eax
       +0x6: cs      nopw 0x0(%rax,%rax,1)
      +0x10: movzbl  (%rsi,%rax,1),%ecx
      +0x14: and     $0x7,%ecx
      +0x17: mov     %ecx,(%rdi)
      +0x19: movzbl  (%rsi,%rax,1),%edx
      +0x1d: shr     $0x3,%edx
      +0x20: and     $0x7,%edx
      +0x23: mov     %edx,0x4(%rdi)
      +0x26: movzbl  (%rsi,%rax,1),%r8d
      +0x2b: shr     $0x6,%r8d
      +0x2f: movzbl  0x1(%rsi,%rax,1),%r9d
      +0x35: and     $0x1,%r9d
      +0x39: lea     (%r8,%r9,4),%r9d
      +0x3d: mov     %r9d,0x8(%rdi)
      +0x41: movzbl  0x1(%rsi,%rax,1),%r8d
      +0x47: shr     $1,%r8d
      +0x4a: and     $0x7,%r8d
      +0x4e: mov     %r8d,0xc(%rdi)
      +0x52: movzbl  0x1(%rsi,%rax,1),%r10d
      +0x58: shr     $0x4,%r10d
      +0x5c: and     $0x7,%r10d
      +0x60: mov     %r10d,0x10(%rdi)
      +0x64: movzbl  0x1(%rsi,%rax,1),%r11d
      +0x6a: shr     $0x7,%r11d
      +0x6e: movzbl  0x2(%rsi,%rax,1),%ebx
      +0x73: and     $0x3,%ebx
      +0x76: lea     (%r11,%rbx,2),%r11d
      +0x7a: mov     %r11d,0x14(%rdi)
      +0x7e: movzbl  0x2(%rsi,%rax,1),%ebx
      +0x83: shr     $0x2,%ebx
      +0x86: and     $0x7,%ebx
      +0x89: mov     %ebx,0x18(%rdi)
      +0x8c: movzbl  0x2(%rsi,%rax,1),%ebp
      +0x91: shr     $0x5,%ebp
      +0x94: mov     $0x2,%r14d
      +0x9a: sub     %ecx,%r14d
      +0x9d: mov     %r14d,(%rdi)
      +0xa0: mov     $0x2,%ecx
      +0xa5: sub     %edx,%ecx
      +0xa7: mov     %ecx,0x4(%rdi)
      +0xaa: mov     $0x2,%ecx
      +0xaf: sub     %r9d,%ecx
      +0xb2: mov     %ecx,0x8(%rdi)
      +0xb5: mov     $0x2,%ecx
      +0xba: sub     %r8d,%ecx
      +0xbd: mov     %ecx,0xc(%rdi)
      +0xc0: mov     $0x2,%ecx
      +0xc5: sub     %r10d,%ecx
      +0xc8: mov     %ecx,0x10(%rdi)
      +0xcb: mov     $0x2,%ecx
      +0xd0: sub     %r11d,%ecx
      +0xd3: mov     %ecx,0x14(%rdi)
      +0xd6: mov     $0x2,%ecx
      +0xdb: sub     %ebx,%ecx
      +0xdd: mov     %ecx,0x18(%rdi)
      +0xe0: mov     $0x2,%ecx
      +0xe5: sub     %ebp,%ecx
      +0xe7: mov     %ecx,0x1c(%rdi)
      +0xea: add     $0x20,%rdi
      +0xee: add     $0x3,%rax
      +0xf2: cmp     $0x60,%rax
      +0xf6: jne     <mldsa87_polyeta_unpack+0x10>
      +0xfc: pop     %rbx
      +0xfd: pop     %r14
      +0xff: pop     %rbp
     +0x100: xor     %eax,%eax
     +0x102: xor     %ecx,%ecx
     +0x104: xor     %edi,%edi
     +0x106: xor     %edx,%edx
     +0x108: xor     %esi,%esi
     +0x10a: xor     %r8d,%r8d
     +0x10d: xor     %r9d,%r9d
     +0x110: xor     %r10d,%r10d
     +0x113: xor     %r11d,%r11d
     +0x116: ret     
 ***)

let MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_polyeta_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves R13, R12, RBP and RBX, which it uses, in  *)
(* the 32 bytes below the return address.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,96);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,96)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_polyeta_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyeta_unpack_2 b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,96);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,96)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_polyeta_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyeta_unpack_2 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 24))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,96; r,1024; word_sub stackpointer (word 24),24;
                        stackpointer,8]
                       [r,1024; word_sub stackpointer (word 24),24]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,96);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,96)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_polyeta_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 24))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,96; r,1024; word_sub stackpointer (word 24),24;
                        stackpointer,8]
                       [r,1024; word_sub stackpointer (word 24),24]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
