(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t165 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 and MLD_CONFIG_REDUCE_RAM (the monolithic build, see                  *)
(* mldsa_native/README.md). In this configuration the matrix is not          *)
(* expanded: the code copies rho into a structure mld_polymat_lazy on the    *)
(* stack, and for each row k computes polynomial k of t = A * s1 + s2 with   *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy, which samples the   *)
(* entries of row k when it needs them, and mldsa_poly_invntt_tomont. Clang  *)
(* inlines the rest: the unpacking of s2 (eta = 4, 4 bits per coefficient),  *)
(* the loops that add the two (mld_poly_add), reduce the sum and add q to    *)
(* the negative coefficients (mld_poly_reduce, mld_poly_caddq), split it at  *)
(* 2^13 (mld_poly_power2round) and pack t1 (mld_polyt1_pack); t0 is packed   *)
(* with mldsa_polyt0_pack. The two polynomials and the structure are then    *)
(* zeroed with memset. It is verified in the whole image (see libmldsa.ml)   *)
(* against mld_compute_t of common/mldsa_native_sign.ml, the specification   *)
(* of the code without MLD_CONFIG_REDUCE_RAM, for s1hat within the bound     *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyt0_pack_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mld_compute_pack_t0_t165:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0xc60,%rsp
      +0x18: mov     %rcx,%rbx
      +0x1b: mov     %rdx,0x18(%rsp)
      +0x20: mov     %rsi,%r15
      +0x23: mov     %rdi,%r12
      +0x26: movdqu  (%r8),%xmm0
      +0x2b: movdqu  0x10(%r8),%xmm1
      +0x31: movdqa  %xmm0,0xc20(%rsp)
      +0x3a: movdqa  %xmm1,0xc30(%rsp)
      +0x43: add     $0x2,%rbx
      +0x47: add     $0x4,%r12
      +0x4b: xor     %r13d,%r13d
      +0x4e: lea     0x20(%rsp),%r14
      +0x53: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
      +0x60: mov     %r14,%rdi
      +0x63: lea     0x820(%rsp),%rsi
      +0x6b: mov     0x18(%rsp),%rdx
      +0x70: mov     %r13d,%ecx
      +0x73: call    <mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy>
      +0x78: mov     %r14,%rdi
      +0x7b: call    <mldsa_poly_invntt_tomont>
      +0x80: xor     %eax,%eax
      +0x82: movdqa  0x17916(%rip),%xmm4
      +0x8a: pxor    %xmm5,%xmm5
      +0x8e: movdqa  0x1791a(%rip),%xmm6
      +0x96: cs      nopw 0x0(%rax,%rax,1)
      +0xa0: movzwl  -0x2(%rbx,%rax,1),%ecx
      +0xa5: movd    %ecx,%xmm0
      +0xa9: movzwl  (%rbx,%rax,1),%ecx
      +0xad: movd    %ecx,%xmm1
      +0xb1: movdqa  %xmm0,%xmm2
      +0xb5: psrlw   $0x4,%xmm2
      +0xba: movdqa  %xmm1,%xmm3
      +0xbe: psrlw   $0x4,%xmm3
      +0xc3: punpcklbw %xmm2,%xmm0
      +0xc7: pand    %xmm4,%xmm0
      +0xcb: punpcklbw %xmm5,%xmm0
      +0xcf: punpcklwd %xmm5,%xmm0
      +0xd3: movdqa  %xmm6,%xmm2
      +0xd7: psubd   %xmm0,%xmm2
      +0xdb: movdqa  %xmm2,0x420(%rsp,%rax,8)
      +0xe4: punpcklbw %xmm3,%xmm1
      +0xe8: pand    %xmm4,%xmm1
      +0xec: punpcklbw %xmm5,%xmm1
      +0xf0: punpcklwd %xmm5,%xmm1
      +0xf4: movdqa  %xmm6,%xmm0
      +0xf8: psubd   %xmm1,%xmm0
      +0xfc: movdqa  %xmm0,0x430(%rsp,%rax,8)
     +0x105: add     $0x4,%rax
     +0x109: cmp     $0x80,%rax
     +0x10f: jne     <mld_compute_pack_t0_t165+0xa0>
     +0x111: mov     $0xc,%eax
     +0x116: cs      nopw 0x0(%rax,%rax,1)
     +0x120: movdqa  0x3f0(%rsp,%rax,4),%xmm0
     +0x129: movdqa  0x400(%rsp,%rax,4),%xmm1
     +0x132: movdqa  0x410(%rsp,%rax,4),%xmm2
     +0x13b: movdqa  0x420(%rsp,%rax,4),%xmm3
     +0x144: paddd   -0x10(%rsp,%rax,4),%xmm0
     +0x14a: paddd   (%rsp,%rax,4),%xmm1
     +0x14f: movdqa  %xmm0,-0x10(%rsp,%rax,4)
     +0x155: movdqa  %xmm1,(%rsp,%rax,4)
     +0x15a: paddd   0x10(%rsp,%rax,4),%xmm2
     +0x160: paddd   0x20(%rsp,%rax,4),%xmm3
     +0x166: movdqa  %xmm2,0x10(%rsp,%rax,4)
     +0x16c: movdqa  %xmm3,0x20(%rsp,%rax,4)
     +0x172: add     $0x10,%rax
     +0x176: cmp     $0x10c,%rax
     +0x17c: jne     <mld_compute_pack_t0_t165+0x120>
     +0x17e: mov     $0x4,%eax
     +0x183: movdqa  0x17535(%rip),%xmm5
     +0x18b: movdqa  0x1753d(%rip),%xmm6
     +0x193: movdqa  0x17555(%rip),%xmm7
     +0x19b: nopl    0x0(%rax,%rax,1)
     +0x1a0: movdqa  0x10(%rsp,%rax,4),%xmm0
     +0x1a6: movdqa  0x20(%rsp,%rax,4),%xmm1
     +0x1ac: movdqa  %xmm0,%xmm2
     +0x1b0: paddd   %xmm5,%xmm2
     +0x1b4: movdqa  %xmm1,%xmm3
     +0x1b8: paddd   %xmm5,%xmm3
     +0x1bc: psrad   $0x17,%xmm2
     +0x1c1: psrad   $0x17,%xmm3
     +0x1c6: pshufd  $0xf5,%xmm2,%xmm4
     +0x1cb: pmuludq %xmm6,%xmm2
     +0x1cf: pshufd  $0xe8,%xmm2,%xmm2
     +0x1d4: pmuludq %xmm6,%xmm4
     +0x1d8: pshufd  $0xe8,%xmm4,%xmm4
     +0x1dd: punpckldq %xmm4,%xmm2
     +0x1e1: pshufd  $0xf5,%xmm3,%xmm4
     +0x1e6: pmuludq %xmm6,%xmm3
     +0x1ea: pshufd  $0xe8,%xmm3,%xmm3
     +0x1ef: pmuludq %xmm6,%xmm4
     +0x1f3: pshufd  $0xe8,%xmm4,%xmm4
     +0x1f8: punpckldq %xmm4,%xmm3
     +0x1fc: paddd   %xmm0,%xmm2
     +0x200: paddd   %xmm1,%xmm3
     +0x204: movdqa  %xmm2,0x10(%rsp,%rax,4)
     +0x20a: movdqa  %xmm3,0x20(%rsp,%rax,4)
     +0x210: add     $0x8,%rax
     +0x214: cmp     $0x104,%rax
     +0x21a: jne     <mld_compute_pack_t0_t165+0x1a0>
     +0x21c: xor     %eax,%eax
     +0x21e: xchg    %ax,%ax
     +0x220: movslq  0x20(%rsp,%rax,4),%rcx
     +0x225: lea     0x7fe001(%rcx),%edx
     +0x22b: mov     %rcx,%rsi
     +0x22e: shr     $0x1f,%rsi
     +0x232: xor     %ecx,%edx
     +0x234: and     %esi,%edx
     +0x236: xor     %ecx,%edx
     +0x238: mov     %edx,0x20(%rsp,%rax,4)
     +0x23c: inc     %rax
     +0x23f: cmp     $0x100,%rax
     +0x245: jne     <mld_compute_pack_t0_t165+0x220>
     +0x247: mov     $0x4,%eax
     +0x24c: movdqa  0x1748c(%rip),%xmm6
     +0x254: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x260: movdqa  0x10(%rsp,%rax,4),%xmm0
     +0x266: movdqa  0x20(%rsp,%rax,4),%xmm1
     +0x26c: movdqa  %xmm0,%xmm2
     +0x270: paddd   %xmm6,%xmm2
     +0x274: movdqa  %xmm1,%xmm3
     +0x278: paddd   %xmm6,%xmm3
     +0x27c: movdqa  %xmm2,%xmm4
     +0x280: psrad   $0xd,%xmm4
     +0x285: movdqa  %xmm3,%xmm5
     +0x289: psrad   $0xd,%xmm5
     +0x28e: movdqa  %xmm4,0x410(%rsp,%rax,4)
     +0x297: movdqa  %xmm5,0x420(%rsp,%rax,4)
     +0x2a0: pand    %xmm7,%xmm2
     +0x2a4: pand    %xmm7,%xmm3
     +0x2a8: psubd   %xmm2,%xmm0
     +0x2ac: psubd   %xmm3,%xmm1
     +0x2b0: movdqa  %xmm0,0x10(%rsp,%rax,4)
     +0x2b6: movdqa  %xmm1,0x20(%rsp,%rax,4)
     +0x2bc: add     $0x8,%rax
     +0x2c0: cmp     $0x104,%rax
     +0x2c6: jne     <mld_compute_pack_t0_t165+0x260>
     +0x2c8: mov     $0xc,%eax
     +0x2cd: mov     %r12,%rcx
     +0x2d0: mov     0x414(%rsp,%rax,1),%edx
     +0x2d7: mov     %dl,-0x4(%rcx)
     +0x2da: shr     $0x8,%edx
     +0x2dd: mov     0x418(%rsp,%rax,1),%esi
     +0x2e4: lea     0x0(,%rsi,4),%edi
     +0x2eb: or      %edx,%edi
     +0x2ed: mov     %dil,-0x3(%rcx)
     +0x2f1: shr     $0x6,%esi
     +0x2f4: mov     0x41c(%rsp,%rax,1),%edx
     +0x2fb: mov     %edx,%edi
     +0x2fd: shl     $0x4,%edi
     +0x300: or      %esi,%edi
     +0x302: mov     %dil,-0x2(%rcx)
     +0x306: shr     $0x4,%edx
     +0x309: mov     0x420(%rsp,%rax,1),%esi
     +0x310: mov     %esi,%edi
     +0x312: shl     $0x6,%edi
     +0x315: or      %edx,%edi
     +0x317: mov     %dil,-0x1(%rcx)
     +0x31b: shr     $0x2,%esi
     +0x31e: mov     %sil,(%rcx)
     +0x321: add     $0x10,%rax
     +0x325: add     $0x5,%rcx
     +0x329: cmp     $0x40c,%rax
     +0x32f: jne     <mld_compute_pack_t0_t165+0x2d0>
     +0x331: imul    $0x1a0,%r13,%rdi
     +0x338: add     %r15,%rdi
     +0x33b: mov     %r14,%rsi
     +0x33e: call    <mldsa_polyt0_pack>
     +0x343: inc     %r13
     +0x346: sub     $0xffffffffffffff80,%rbx
     +0x34a: add     $0x140,%r12
     +0x351: cmp     $0x6,%r13
     +0x355: jne     <mld_compute_pack_t0_t165+0x60>
     +0x35b: lea     0x420(%rsp),%rbx
     +0x363: mov     $0x400,%edx
     +0x368: mov     %rbx,%rdi
     +0x36b: xor     %esi,%esi
     +0x36d: call    <memset>
     +0x372: lea     0x20(%rsp),%rbx
     +0x377: mov     $0x400,%edx
     +0x37c: mov     %rbx,%rdi
     +0x37f: xor     %esi,%esi
     +0x381: call    <memset>
     +0x386: lea     0x820(%rsp),%rbx
     +0x38e: mov     $0x420,%edx
     +0x393: mov     %rbx,%rdi
     +0x396: xor     %esi,%esi
     +0x398: call    <memset>
     +0x39d: lea     -0x28(%rbp),%rsp
     +0x3a1: pop     %rbx
     +0x3a2: pop     %r12
     +0x3a4: pop     %r13
     +0x3a6: pop     %r14
     +0x3a8: pop     %r15
     +0x3aa: pop     %rbp
     +0x3ab: xor     %eax,%eax
     +0x3ad: xor     %ecx,%ecx
     +0x3af: xor     %edi,%edi
     +0x3b1: xor     %edx,%edx
     +0x3b3: xor     %esi,%esi
     +0x3b5: xor     %r8d,%r8d
     +0x3b8: ret     
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_compute_pack_t0_t165";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector s1hat (s1 in the NTT domain) of 5 polynomials sh  *)
(* at s1hat, with coefficients below MLD_NTT_BOUND = 94279689 in absolute    *)
(* value, the 6 polynomials of s2 packed in 128 bytes each, s2b at s2, and   *)
(* rho, the 32 bytes r at rho: the 6 polynomials of t1 packed in 320 bytes   *)
(* each are written at pkt1 and the 6 of t0 packed in 416 bytes each at t0,  *)
(* with t = mld_compute_t, if the sampling of the matrix terminates, and the *)
(* result is 0. The function saves RBP, the frame pointer, and five more     *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, and then reserves 3168 bytes for the structure            *)
(* mld_polymat_lazy (1056 bytes), two polynomials and the spill of s1hat,    *)
(* below which the call of                                                   *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy uses 1654 bytes,     *)
(* with its return address: 4901 bytes of stack below the return address in  *)
(* all, including the red zone of the callees.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 r /\
        (!j. j < 1280 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
        PAIRWISE nonoverlapping
         [(pkt1,1920); (t0,2496);
          (word_sub stackpointer (word 4901),4901)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1920); (t0,2496);
          (word_sub stackpointer (word 4901),4901)]
         [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1920); (t0,2496)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t165) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 1280
                       ==> read(memory :> bytes32
                                 (word_add s1hat (word(4 * j)))) s =
                           sh j) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add s2 (word j))) s =
                           s2b j) /\
                  read (memory :> bytes(rho,32)) s = r)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word 0 /\
                  (!j. j < 1920
                       ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                           mld_polyvec_pack 320 mld_polyt1_pack
                            (mld_polyvec_map mld_poly_power2round_hi
                              (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                 sh s2b)) j) /\
                  (!j. j < 2496
                       ==> read(memory :> bytes8(word_add t0 (word j))) s =
                           mld_polyvec_pack 416 mld_polyt0_pack
                            (mld_polyvec_map mld_poly_power2round_lo
                              (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                 sh s2b)) j))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                memory :> bytes(word_sub stackpointer (word 4901),4901)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho and the stack, with all       *)
(* accesses within the arguments, the stack, the return address and the      *)
(* constants of the callees, and the writes within the outputs and the       *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 r /\
        (!j. j < 1280 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
        PAIRWISE nonoverlapping
         [(pkt1,1920); (t0,2496);
          (word_sub stackpointer (word 4901),4901)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1920); (t0,2496);
          (word_sub stackpointer (word 4901),4901)]
         [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1920); (t0,2496)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t165) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 1280
                       ==> read(memory :> bytes32
                                 (word_add s1hat (word(4 * j)))) s =
                           sh j) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add s2 (word j))) s =
                           s2b j) /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word 0 /\
                  (!j. j < 1920
                       ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                           mld_polyvec_pack 320 mld_polyt1_pack
                            (mld_polyvec_map mld_poly_power2round_hi
                              (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                 sh s2b)) j) /\
                  (!j. j < 2496
                       ==> read(memory :> bytes8(word_add t0 (word j))) s =
                           mld_polyvec_pack 416 mld_polyt0_pack
                            (mld_polyvec_map mld_poly_power2round_lo
                              (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                 sh s2b)) j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pkt1 t0 s1hat s2 rho r mf mc pc
                            (word_sub stackpointer (word 4901))
                            returnaddress /\
                     memaccess_inbounds e2
                      [s1hat,5120; s2,768; rho,32; pkt1,1920; t0,2496;
                       word_sub stackpointer (word 4901),4901;
                       stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mld_compute_pack_t0_t165_consts),768;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pkt1,1920; t0,2496;
                       word_sub stackpointer (word 4901),4901]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                memory :> bytes(word_sub stackpointer (word 4901),4901)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 r /\
        PAIRWISE nonoverlapping
         [(pkt1,1920); (t0,2496);
          (word_sub stackpointer (word 4901),4901)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1920); (t0,2496);
          (word_sub stackpointer (word 4901),4901)]
         [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1920); (t0,2496)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t165) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 1280
                       ==> read(memory :> bytes32
                                 (word_add s1hat (word(4 * j)))) s =
                           sh j) /\
                  (!j. j < 768
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
                      [s1hat,5120; s2,768; rho,32; pkt1,1920; t0,2496;
                       word_sub stackpointer (word 4901),4901;
                       stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mld_compute_pack_t0_t165_consts),768;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pkt1,1920; t0,2496;
                       word_sub stackpointer (word 4901),4901]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                memory :> bytes(word_sub stackpointer (word 4901),4901)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
