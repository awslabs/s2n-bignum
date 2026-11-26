(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 13 bits per coefficient, of 2^12 - a: the    *)
(* statement. This is the code for mldsa_polyt0_pack                         *)
(* (mld_polyt0_pack in poly.c) from mldsa-native's portable C implementation *)
(* compiled by clang 23 with -O3 and MLD_CONFIG_REDUCE_RAM (see              *)
(* mldsa_native/README.md), which handles 8 coefficients in each iteration   *)
(* and writes their 13 bytes with 13 single-byte stores. It is verified in   *)
(* the whole image (see libmldsa.ml) against mld_polyt0_pack of              *)
(* common/mldsa_native_packing.ml, byte by byte. It is also shown to be      *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_pack:
       +0x0: push    %rbp
       +0x1: push    %r14
       +0x3: push    %rbx
       +0x4: add     $0x1c,%rsi
       +0x8: xor     %eax,%eax
       +0xa: nopw    0x0(%rax,%rax,1)
      +0x10: mov     $0x1000,%ebp
      +0x15: sub     -0x1c(%rsi),%ebp
      +0x18: mov     $0x1000,%ebx
      +0x1d: sub     -0x18(%rsi),%ebx
      +0x20: mov     $0x1000,%r11d
      +0x26: sub     -0x14(%rsi),%r11d
      +0x2a: mov     $0x1000,%r10d
      +0x30: sub     -0x10(%rsi),%r10d
      +0x34: mov     $0x1000,%r9d
      +0x3a: sub     -0xc(%rsi),%r9d
      +0x3e: mov     $0x1000,%r8d
      +0x44: sub     -0x8(%rsi),%r8d
      +0x48: mov     $0x1000,%edx
      +0x4d: sub     -0x4(%rsi),%edx
      +0x50: mov     $0x1000,%ecx
      +0x55: sub     (%rsi),%ecx
      +0x57: mov     %bpl,(%rdi,%rax,1)
      +0x5b: shr     $0x8,%ebp
      +0x5e: mov     %ebx,%r14d
      +0x61: shl     $0x5,%r14d
      +0x65: or      %ebp,%r14d
      +0x68: mov     %r14b,0x1(%rdi,%rax,1)
      +0x6d: mov     %ebx,%ebp
      +0x6f: shr     $0x3,%ebp
      +0x72: mov     %bpl,0x2(%rdi,%rax,1)
      +0x77: shr     $0xb,%ebx
      +0x7a: lea     0x0(,%r11,4),%ebp
      +0x82: or      %ebx,%ebp
      +0x84: mov     %bpl,0x3(%rdi,%rax,1)
      +0x89: shr     $0x6,%r11d
      +0x8d: mov     %r10d,%ebx
      +0x90: shl     $0x7,%ebx
      +0x93: or      %r11d,%ebx
      +0x96: mov     %bl,0x4(%rdi,%rax,1)
      +0x9a: mov     %r10d,%r11d
      +0x9d: shr     $1,%r11d
      +0xa0: mov     %r11b,0x5(%rdi,%rax,1)
      +0xa5: shr     $0x9,%r10d
      +0xa9: mov     %r9d,%r11d
      +0xac: shl     $0x4,%r11d
      +0xb0: or      %r10d,%r11d
      +0xb3: mov     %r11b,0x6(%rdi,%rax,1)
      +0xb8: mov     %r9d,%r10d
      +0xbb: shr     $0x4,%r10d
      +0xbf: mov     %r10b,0x7(%rdi,%rax,1)
      +0xc4: shr     $0xc,%r9d
      +0xc8: lea     (%r8,%r8,1),%r10d
      +0xcc: or      %r9d,%r10d
      +0xcf: mov     %r10b,0x8(%rdi,%rax,1)
      +0xd4: shr     $0x7,%r8d
      +0xd8: mov     %edx,%r9d
      +0xdb: shl     $0x6,%r9d
      +0xdf: or      %r8d,%r9d
      +0xe2: mov     %r9b,0x9(%rdi,%rax,1)
      +0xe7: mov     %edx,%r8d
      +0xea: shr     $0x2,%r8d
      +0xee: mov     %r8b,0xa(%rdi,%rax,1)
      +0xf3: shr     $0xa,%edx
      +0xf6: lea     0x0(,%rcx,8),%r8d
      +0xfe: or      %edx,%r8d
     +0x101: mov     %r8b,0xb(%rdi,%rax,1)
     +0x106: shr     $0x5,%ecx
     +0x109: mov     %cl,0xc(%rdi,%rax,1)
     +0x10d: add     $0x20,%rsi
     +0x111: add     $0xd,%rax
     +0x115: cmp     $0x1a0,%rax
     +0x11b: jne     <mldsa_polyt0_pack+0x10>
     +0x121: xorps   %xmm0,%xmm0
     +0x124: movaps  %xmm0,-0x10(%rsp)
     +0x129: movaps  %xmm0,-0x20(%rsp)
     +0x12e: lea     -0x20(%rsp),%rax
     +0x133: pop     %rbx
     +0x134: pop     %r14
     +0x136: pop     %rbp
     +0x137: xor     %eax,%eax
     +0x139: xor     %ecx,%ecx
     +0x13b: xor     %edi,%edi
     +0x13d: xor     %edx,%edx
     +0x13f: xor     %esi,%esi
     +0x141: xor     %r8d,%r8d
     +0x144: xor     %r9d,%r9d
     +0x147: xor     %r10d,%r10d
     +0x14a: xor     %r11d,%r11d
     +0x14d: ret     
 ***)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_polyt0_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves RBP, R14 and RBX, which it uses, in the  *)
(* 24 bytes below the return address, and clears 32 bytes below those, the   *)
(* temporary array that mld_polyt0_pack zeroizes, with two aligned SSE       *)
(* stores into the red zone (so the frame is 56 bytes). The stores fault     *)
(* unless RSP + 8 is a multiple of 16 on entry, as the ABI requires, which   *)
(* the statements assume.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (r,416))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_polyt0_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 416
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyt0_pack x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (r,416))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_polyt0_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyt0_pack x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 56))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,416; word_sub stackpointer (word 56),56;
                        stackpointer,8]
                       [r,416; word_sub stackpointer (word 56),56]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (r,416))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_polyt0_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 56))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,416; word_sub stackpointer (word 56),56;
                        stackpointer,8]
                       [r,416; word_sub stackpointer (word 56),56]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
