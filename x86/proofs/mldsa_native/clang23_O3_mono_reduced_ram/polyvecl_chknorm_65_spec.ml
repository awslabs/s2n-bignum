(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 5 polynomials: the statement. This is the code  *)
(* for mldsa65_polyvecl_chknorm (mld_polyvecl_chknorm in polyvec.c) from     *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which has inlined *)
(* mldsa_poly_chknorm: one loop over the 256 coefficients of each of the 5   *)
(* polynomials, ORing a mask for each coefficient into a register of its     *)
(* own. It is verified in the whole image (see libmldsa.ml) against          *)
(* mld_polyvec_chknorm of common/mldsa_native_polyvec.ml, and shown to be    *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvecl_chknorm:
       +0x0: xor     %ecx,%ecx
       +0x2: xor     %eax,%eax
       +0x4: data16  data16 cs nopw 0x0(%rax,%rax,1)
      +0x10: movslq  (%rdi,%rax,4),%rdx
      +0x14: mov     %edx,%r8d
      +0x17: neg     %r8d
      +0x1a: mov     %rdx,%r9
      +0x1d: shr     $0x1f,%r9
      +0x21: xor     %edx,%r8d
      +0x24: and     %r9d,%r8d
      +0x27: xor     %edx,%r8d
      +0x2a: not     %r8d
      +0x2d: add     %esi,%r8d
      +0x30: movslq  %r8d,%rdx
      +0x33: shr     $0x1f,%rdx
      +0x37: or      %edx,%ecx
      +0x39: inc     %rax
      +0x3c: cmp     $0x100,%rax
      +0x42: jne     <mldsa65_polyvecl_chknorm+0x10>
      +0x44: xor     %edx,%edx
      +0x46: xor     %eax,%eax
      +0x48: nopl    0x0(%rax,%rax,1)
      +0x50: movslq  0x400(%rdi,%rax,4),%r8
      +0x58: mov     %r8d,%r9d
      +0x5b: neg     %r9d
      +0x5e: mov     %r8,%r10
      +0x61: shr     $0x1f,%r10
      +0x65: xor     %r8d,%r9d
      +0x68: and     %r10d,%r9d
      +0x6b: xor     %r8d,%r9d
      +0x6e: not     %r9d
      +0x71: add     %esi,%r9d
      +0x74: movslq  %r9d,%r8
      +0x77: shr     $0x1f,%r8
      +0x7b: or      %r8d,%edx
      +0x7e: inc     %rax
      +0x81: cmp     $0x100,%rax
      +0x87: jne     <mldsa65_polyvecl_chknorm+0x50>
      +0x89: xor     %r8d,%r8d
      +0x8c: xor     %eax,%eax
      +0x8e: xchg    %ax,%ax
      +0x90: movslq  0x800(%rdi,%rax,4),%r9
      +0x98: mov     %r9d,%r10d
      +0x9b: neg     %r10d
      +0x9e: mov     %r9,%r11
      +0xa1: shr     $0x1f,%r11
      +0xa5: xor     %r9d,%r10d
      +0xa8: and     %r11d,%r10d
      +0xab: xor     %r9d,%r10d
      +0xae: not     %r10d
      +0xb1: add     %esi,%r10d
      +0xb4: movslq  %r10d,%r9
      +0xb7: shr     $0x1f,%r9
      +0xbb: or      %r9d,%r8d
      +0xbe: inc     %rax
      +0xc1: cmp     $0x100,%rax
      +0xc7: jne     <mldsa65_polyvecl_chknorm+0x90>
      +0xc9: push    %r14
      +0xcb: push    %rbx
      +0xcc: xor     %r9d,%r9d
      +0xcf: xor     %eax,%eax
      +0xd1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
      +0xe0: movslq  0xc00(%rdi,%rax,4),%r10
      +0xe8: mov     %r10d,%r11d
      +0xeb: neg     %r11d
      +0xee: mov     %r10,%rbx
      +0xf1: shr     $0x1f,%rbx
      +0xf5: xor     %r10d,%r11d
      +0xf8: and     %ebx,%r11d
      +0xfb: xor     %r10d,%r11d
      +0xfe: not     %r11d
     +0x101: add     %esi,%r11d
     +0x104: movslq  %r11d,%r10
     +0x107: shr     $0x1f,%r10
     +0x10b: or      %r10d,%r9d
     +0x10e: inc     %rax
     +0x111: cmp     $0x100,%rax
     +0x117: jne     <mldsa65_polyvecl_chknorm+0xe0>
     +0x119: xor     %eax,%eax
     +0x11b: xor     %r10d,%r10d
     +0x11e: xchg    %ax,%ax
     +0x120: movslq  0x1000(%rdi,%r10,4),%r11
     +0x128: mov     %r11d,%ebx
     +0x12b: neg     %ebx
     +0x12d: mov     %r11,%r14
     +0x130: shr     $0x1f,%r14
     +0x134: xor     %r11d,%ebx
     +0x137: and     %r14d,%ebx
     +0x13a: xor     %r11d,%ebx
     +0x13d: not     %ebx
     +0x13f: add     %esi,%ebx
     +0x141: movslq  %ebx,%r11
     +0x144: shr     $0x1f,%r11
     +0x148: or      %r11d,%eax
     +0x14b: inc     %r10
     +0x14e: cmp     $0x100,%r10
     +0x155: jne     <mldsa65_polyvecl_chknorm+0x120>
     +0x157: or      %ecx,%edx
     +0x159: or      %edx,%r8d
     +0x15c: or      %r8d,%r9d
     +0x15f: or      %r9d,%eax
     +0x162: pop     %rbx
     +0x163: pop     %r14
     +0x165: xor     %ecx,%ecx
     +0x167: xor     %edi,%edi
     +0x169: xor     %edx,%edx
     +0x16b: xor     %esi,%esi
     +0x16d: xor     %r8d,%r8d
     +0x170: xor     %r9d,%r9d
     +0x173: xor     %r10d,%r10d
     +0x176: xor     %r11d,%r11d
     +0x179: ret     
 ***)

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_polyvecl_chknorm"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the vector x at v, 5 polynomials of 256 coefficients of  *)
(* 32 bits each (see common/mldsa_native_polyvec.ml), and the bound in the   *)
(* low 32 bits of bnd, the result is mld_polyvec_chknorm 5 x bnd: all ones   *)
(* if some coefficient is not below the bound in absolute value, zero        *)
(* otherwise. The function saves R14 and RBX in the 16 bytes below the       *)
(* return address, before its fourth loop.                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(v,5120); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_polyvecl_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 5 x (word_zx bnd)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the bound only, with all       *)
(* accesses within the vector, the stack frame and the slot of the return    *)
(* address, and the writes within the stack frame.                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(v,5120); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_polyvecl_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 5 x (word_zx bnd)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v bnd pc (word_sub stackpointer (word 16))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,5120; word_sub stackpointer (word 16),16;
                       stackpointer,8]
                      [word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(v,5120); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_polyvecl_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v bnd pc (word_sub stackpointer (word 16))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,5120; word_sub stackpointer (word 16),16;
                       stackpointer,8]
                      [word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
