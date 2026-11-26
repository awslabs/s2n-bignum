(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t144 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 and MLD_CONFIG_REDUCE_RAM (the monolithic build, see                  *)
(* mldsa_native/README.md). In this configuration the matrix is not          *)
(* expanded: the code copies rho into a structure mld_polymat_lazy on the    *)
(* stack, and for each row k computes polynomial k of t = A * s1 + s2 with   *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy, which samples the   *)
(* entries of row k when it needs them, mldsa_poly_invntt_tomont and         *)
(* mldsa44_polyeta_unpack (for s2). Clang inlines the rest: the loops that   *)
(* add them (mld_poly_add), reduce the sum and add q to the negative         *)
(* coefficients (mld_poly_reduce, mld_poly_caddq), split it at 2^13          *)
(* (mld_poly_power2round) and pack t1 (mld_polyt1_pack); t0 is packed with   *)
(* mldsa_polyt0_pack. The two polynomials and the structure are then zeroed  *)
(* with memset. It is verified in the whole image (see libmldsa.ml) against  *)
(* mld_compute_t of common/mldsa_native_sign.ml, the specification of the    *)
(* code without MLD_CONFIG_REDUCE_RAM, for s1hat within the bound            *)
(* MLD_NTT_BOUND of the C contract (see lazy_eq_spec.ml), using the          *)
(* theorems for the callees and for the inlined loops, assuming that the     *)
(* sampling of the matrix terminates (mld_matrix_terminates), and shown to   *)
(* be constant time and memory safe, with the events depending on rho,       *)
(* which is public.                                                          *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyeta_unpack_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyt0_pack_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mld_compute_pack_t0_t144:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0xc60,%rsp
      +0x18: mov     %rcx,0x18(%rsp)
      +0x1d: mov     %rdx,%r14
      +0x20: mov     %rsi,%r15
      +0x23: mov     %rdi,%r12
      +0x26: movdqu  (%r8),%xmm0
      +0x2b: movdqu  0x10(%r8),%xmm1
      +0x31: movdqa  %xmm0,0xc20(%rsp)
      +0x3a: movdqa  %xmm1,0xc30(%rsp)
      +0x43: add     $0x4,%r12
      +0x47: xor     %r13d,%r13d
      +0x4a: lea     0x20(%rsp),%rbx
      +0x4f: nop     
      +0x50: mov     %rbx,%rdi
      +0x53: lea     0x820(%rsp),%rsi
      +0x5b: mov     %r14,%rdx
      +0x5e: mov     %r13d,%ecx
      +0x61: call    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy>
      +0x66: mov     %rbx,%rdi
      +0x69: call    <mldsa_poly_invntt_tomont>
      +0x6e: lea     0x0(,%r13,2),%rsi
      +0x76: add     %r13,%rsi
      +0x79: shl     $0x5,%rsi
      +0x7d: add     0x18(%rsp),%rsi
      +0x82: lea     0x420(%rsp),%rdi
      +0x8a: call    <mldsa44_polyeta_unpack>
      +0x8f: mov     $0xc,%eax
      +0x94: data16  data16 cs nopw 0x0(%rax,%rax,1)
      +0xa0: movdqa  0x3f0(%rsp,%rax,4),%xmm0
      +0xa9: movdqa  0x400(%rsp,%rax,4),%xmm1
      +0xb2: movdqa  0x410(%rsp,%rax,4),%xmm2
      +0xbb: movdqa  0x420(%rsp,%rax,4),%xmm3
      +0xc4: paddd   -0x10(%rsp,%rax,4),%xmm0
      +0xca: paddd   (%rsp,%rax,4),%xmm1
      +0xcf: movdqa  %xmm0,-0x10(%rsp,%rax,4)
      +0xd5: movdqa  %xmm1,(%rsp,%rax,4)
      +0xda: paddd   0x10(%rsp,%rax,4),%xmm2
      +0xe0: paddd   0x20(%rsp,%rax,4),%xmm3
      +0xe6: movdqa  %xmm2,0x10(%rsp,%rax,4)
      +0xec: movdqa  %xmm3,0x20(%rsp,%rax,4)
      +0xf2: add     $0x10,%rax
      +0xf6: cmp     $0x10c,%rax
      +0xfc: jne     <mld_compute_pack_t0_t144+0xa0>
      +0xfe: mov     $0x4,%eax
     +0x103: movdqa  0x22c95(%rip),%xmm5
     +0x10b: movdqa  0x22c9d(%rip),%xmm6
     +0x113: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x120: movdqa  0x10(%rsp,%rax,4),%xmm0
     +0x126: movdqa  0x20(%rsp,%rax,4),%xmm1
     +0x12c: movdqa  %xmm0,%xmm2
     +0x130: paddd   %xmm5,%xmm2
     +0x134: movdqa  %xmm1,%xmm3
     +0x138: paddd   %xmm5,%xmm3
     +0x13c: psrad   $0x17,%xmm2
     +0x141: psrad   $0x17,%xmm3
     +0x146: pshufd  $0xf5,%xmm2,%xmm4
     +0x14b: pmuludq %xmm6,%xmm2
     +0x14f: pshufd  $0xe8,%xmm2,%xmm2
     +0x154: pmuludq %xmm6,%xmm4
     +0x158: pshufd  $0xe8,%xmm4,%xmm4
     +0x15d: punpckldq %xmm4,%xmm2
     +0x161: pshufd  $0xf5,%xmm3,%xmm4
     +0x166: pmuludq %xmm6,%xmm3
     +0x16a: pshufd  $0xe8,%xmm3,%xmm3
     +0x16f: pmuludq %xmm6,%xmm4
     +0x173: pshufd  $0xe8,%xmm4,%xmm4
     +0x178: punpckldq %xmm4,%xmm3
     +0x17c: paddd   %xmm0,%xmm2
     +0x180: paddd   %xmm1,%xmm3
     +0x184: movdqa  %xmm2,0x10(%rsp,%rax,4)
     +0x18a: movdqa  %xmm3,0x20(%rsp,%rax,4)
     +0x190: add     $0x8,%rax
     +0x194: cmp     $0x104,%rax
     +0x19a: jne     <mld_compute_pack_t0_t144+0x120>
     +0x19c: xor     %eax,%eax
     +0x19e: movdqa  0x22c2a(%rip),%xmm7
     +0x1a6: cs      nopw 0x0(%rax,%rax,1)
     +0x1b0: movslq  0x20(%rsp,%rax,4),%rcx
     +0x1b5: lea     0x7fe001(%rcx),%edx
     +0x1bb: mov     %rcx,%rsi
     +0x1be: shr     $0x1f,%rsi
     +0x1c2: xor     %ecx,%edx
     +0x1c4: and     %esi,%edx
     +0x1c6: xor     %ecx,%edx
     +0x1c8: mov     %edx,0x20(%rsp,%rax,4)
     +0x1cc: inc     %rax
     +0x1cf: cmp     $0x100,%rax
     +0x1d5: jne     <mld_compute_pack_t0_t144+0x1b0>
     +0x1d7: mov     $0x4,%eax
     +0x1dc: movdqa  0x22bdc(%rip),%xmm6
     +0x1e4: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x1f0: movdqa  0x10(%rsp,%rax,4),%xmm0
     +0x1f6: movdqa  0x20(%rsp,%rax,4),%xmm1
     +0x1fc: movdqa  %xmm0,%xmm2
     +0x200: paddd   %xmm6,%xmm2
     +0x204: movdqa  %xmm1,%xmm3
     +0x208: paddd   %xmm6,%xmm3
     +0x20c: movdqa  %xmm2,%xmm4
     +0x210: psrad   $0xd,%xmm4
     +0x215: movdqa  %xmm3,%xmm5
     +0x219: psrad   $0xd,%xmm5
     +0x21e: movdqa  %xmm4,0x410(%rsp,%rax,4)
     +0x227: movdqa  %xmm5,0x420(%rsp,%rax,4)
     +0x230: pand    %xmm7,%xmm2
     +0x234: pand    %xmm7,%xmm3
     +0x238: psubd   %xmm2,%xmm0
     +0x23c: psubd   %xmm3,%xmm1
     +0x240: movdqa  %xmm0,0x10(%rsp,%rax,4)
     +0x246: movdqa  %xmm1,0x20(%rsp,%rax,4)
     +0x24c: add     $0x8,%rax
     +0x250: cmp     $0x104,%rax
     +0x256: jne     <mld_compute_pack_t0_t144+0x1f0>
     +0x258: mov     $0xc,%eax
     +0x25d: mov     %r12,%rcx
     +0x260: mov     0x414(%rsp,%rax,1),%edx
     +0x267: mov     %dl,-0x4(%rcx)
     +0x26a: shr     $0x8,%edx
     +0x26d: mov     0x418(%rsp,%rax,1),%esi
     +0x274: lea     0x0(,%rsi,4),%edi
     +0x27b: or      %edx,%edi
     +0x27d: mov     %dil,-0x3(%rcx)
     +0x281: shr     $0x6,%esi
     +0x284: mov     0x41c(%rsp,%rax,1),%edx
     +0x28b: mov     %edx,%edi
     +0x28d: shl     $0x4,%edi
     +0x290: or      %esi,%edi
     +0x292: mov     %dil,-0x2(%rcx)
     +0x296: shr     $0x4,%edx
     +0x299: mov     0x420(%rsp,%rax,1),%esi
     +0x2a0: mov     %esi,%edi
     +0x2a2: shl     $0x6,%edi
     +0x2a5: or      %edx,%edi
     +0x2a7: mov     %dil,-0x1(%rcx)
     +0x2ab: shr     $0x2,%esi
     +0x2ae: mov     %sil,(%rcx)
     +0x2b1: add     $0x10,%rax
     +0x2b5: add     $0x5,%rcx
     +0x2b9: cmp     $0x40c,%rax
     +0x2bf: jne     <mld_compute_pack_t0_t144+0x260>
     +0x2c1: imul    $0x1a0,%r13,%rdi
     +0x2c8: add     %r15,%rdi
     +0x2cb: mov     %rbx,%rsi
     +0x2ce: call    <mldsa_polyt0_pack>
     +0x2d3: inc     %r13
     +0x2d6: add     $0x140,%r12
     +0x2dd: cmp     $0x4,%r13
     +0x2e1: jne     <mld_compute_pack_t0_t144+0x50>
     +0x2e7: lea     0x420(%rsp),%rbx
     +0x2ef: mov     $0x400,%edx
     +0x2f4: mov     %rbx,%rdi
     +0x2f7: xor     %esi,%esi
     +0x2f9: call    <memset>
     +0x2fe: lea     0x20(%rsp),%rbx
     +0x303: mov     $0x400,%edx
     +0x308: mov     %rbx,%rdi
     +0x30b: xor     %esi,%esi
     +0x30d: call    <memset>
     +0x312: lea     0x820(%rsp),%rbx
     +0x31a: mov     $0x420,%edx
     +0x31f: mov     %rbx,%rdi
     +0x322: xor     %esi,%esi
     +0x324: call    <memset>
     +0x329: lea     -0x28(%rbp),%rsp
     +0x32d: pop     %rbx
     +0x32e: pop     %r12
     +0x330: pop     %r13
     +0x332: pop     %r14
     +0x334: pop     %r15
     +0x336: pop     %rbp
     +0x337: xor     %eax,%eax
     +0x339: xor     %ecx,%ecx
     +0x33b: xor     %edi,%edi
     +0x33d: xor     %edx,%edx
     +0x33f: xor     %esi,%esi
     +0x341: xor     %r8d,%r8d
     +0x344: ret     
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_compute_pack_t0_t144";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector s1hat (s1 in the NTT domain) of 4 polynomials sh  *)
(* at s1hat, with coefficients below MLD_NTT_BOUND = 94279689 in absolute    *)
(* value, the 4 polynomials of s2 packed in 96 bytes each, s2b at s2, and    *)
(* rho, the 32 bytes r at rho: the 4 polynomials of t1 packed in 320 bytes   *)
(* each are written at pkt1 and the 4 of t0 packed in 416 bytes each at t0,  *)
(* with t = mld_compute_t, if the sampling of the matrix terminates, and the *)
(* result is 0. The function saves RBP, the frame pointer, and five more     *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, and then reserves 3168 bytes for the structure            *)
(* mld_polymat_lazy (1056 bytes), two polynomials and the spill of s2,       *)
(* below which the call of                                                   *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy uses 1654 bytes,     *)
(* with its return address: 4901 bytes of stack below the return address in  *)
(* all, including the red zone of the callees.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        (!j. j < 1024 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
        PAIRWISE nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4901),4901)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4901),4901)]
         [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1280); (t0,1664)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t144) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 1024
                       ==> read(memory :> bytes32
                                 (word_add s1hat (word(4 * j)))) s =
                           sh j) /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add s2 (word j))) s =
                           s2b j) /\
                  read (memory :> bytes(rho,32)) s = r)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word 0 /\
                  (!j. j < 1280
                       ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                           mld_polyvec_pack 320 mld_polyt1_pack
                            (mld_polyvec_map mld_poly_power2round_hi
                              (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j) /\
                  (!j. j < 1664
                       ==> read(memory :> bytes8(word_add t0 (word j))) s =
                           mld_polyvec_pack 416 mld_polyt0_pack
                            (mld_polyvec_map mld_poly_power2round_lo
                              (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                memory :> bytes(word_sub stackpointer (word 4901),4901)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho and the stack, with all       *)
(* accesses within the arguments, the stack, the return address and the      *)
(* constants of the callees, and the writes within the outputs and the       *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        (!j. j < 1024 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
        PAIRWISE nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4901),4901)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4901),4901)]
         [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1280); (t0,1664)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t144) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 1024
                       ==> read(memory :> bytes32
                                 (word_add s1hat (word(4 * j)))) s =
                           sh j) /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add s2 (word j))) s =
                           s2b j) /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word 0 /\
                  (!j. j < 1280
                       ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                           mld_polyvec_pack 320 mld_polyt1_pack
                            (mld_polyvec_map mld_poly_power2round_hi
                              (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j) /\
                  (!j. j < 1664
                       ==> read(memory :> bytes8(word_add t0 (word j))) s =
                           mld_polyvec_pack 416 mld_polyt0_pack
                            (mld_polyvec_map mld_poly_power2round_lo
                              (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pkt1 t0 s1hat s2 rho r mf mc pc
                            (word_sub stackpointer (word 4901))
                            returnaddress /\
                     memaccess_inbounds e2
                      [s1hat,4096; s2,384; rho,32; pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4901),4901;
                       stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mld_compute_pack_t0_t144_consts),64;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4901),4901]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                memory :> bytes(word_sub stackpointer (word 4901),4901)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        PAIRWISE nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4901),4901)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4901),4901)]
         [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1280); (t0,1664)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t144) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 1024
                       ==> read(memory :> bytes32
                                 (word_add s1hat (word(4 * j)))) s =
                           sh j) /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add s2 (word j))) s =
                           s2b j) /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pkt1 t0 s1hat s2 rho r mf mc pc
                            (word_sub stackpointer (word 4901))
                            returnaddress /\
                     memaccess_inbounds e2
                      [s1hat,4096; s2,384; rho,32; pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4901),4901;
                       stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mld_compute_pack_t0_t144_consts),64;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4901),4901]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                memory :> bytes(word_sub stackpointer (word 4901),4901)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
