(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t165 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which expands the matrix from rho into a    *)
(* buffer on the stack with mldsa65_polyvec_matrix_expand_eager, and for     *)
(* each row k computes polynomial k of t = A * s1 + s2 with                  *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_eager,                    *)
(* mldsa_poly_invntt_tomont, mldsa65_polyeta_unpack (for s2),                *)
(* mldsa_poly_add, mldsa_poly_reduce and mldsa_poly_caddq, splits it with    *)
(* mldsa_poly_power2round and packs t1 and t0 with mldsa_polyt1_pack and     *)
(* mldsa_polyt0_pack, before zeroing the buffers: the two polynomials with   *)
(* memsets that gcc inlines with REP STOSQ, so the direction flag must be    *)
(* clear, as the ABI requires on entry, and the matrix with memset, which it *)
(* calls through the PLT. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_compute_t of common/mldsa_native_sign.ml, using  *)
(* the theorems for the callees and the contract memset_full_contract of     *)
(* utils/mldsa_native_libc.ml for memset, assuming that the expansion of the *)
(* matrix terminates (mld_matrix_terminates), and shown to be constant time  *)
(* and memory safe, with the events depending on rho, which is public.       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_unpack_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_power2round_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyt1_pack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyt0_pack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mld_compute_pack_t0_t165:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  mov     r15, rcx
       +0x9  push    r14
       +0xb  mov     r14, rdi
       +0xe  push    r13
      +0x10  mov     r13, rsi
      +0x13  mov     rsi, r8
      +0x16  push    r12
      +0x18  push    rbx
      +0x19  and     rsp, 0xffffffffffffffe0
      +0x1d  sub     rsp, 0x8020
      +0x24  lea     rax, [rsp+0x820]
      +0x2c  mov     QWORD PTR [rsp+0x8], rdx
      +0x31  lea     rbx, [rsp+0x20]
      +0x36  mov     rdi, rax
      +0x39  mov     QWORD PTR [rsp+0x10], rax
      +0x3e  lea     r12, [rsp+0x420]
      +0x46  call    mldsa65_polyvec_matrix_expand_eager
     after_mldsa65_polyvec_matrix_expand_eager:
      +0x4b  xor     eax, eax
      +0x4d  nop     DWORD PTR [rax]
     loop1:
      +0x50  mov     rdx, QWORD PTR [rsp+0x8]
      +0x55  mov     rsi, QWORD PTR [rsp+0x10]
      +0x5a  mov     ecx, eax
      +0x5c  mov     rdi, rbx
      +0x5f  mov     DWORD PTR [rsp+0x1c], eax
      +0x63  call    mldsa65_polyvec_matrix_pointwise_montgomery_row_eager
     after_mldsa65_polyvec_matrix_pointwise_montgomery_row_eager:
      +0x68  mov     rdi, rbx
      +0x6b  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont:
      +0x70  mov     rsi, r15
      +0x73  mov     rdi, r12
      +0x76  sub     r15, 0xffffffffffffff80
      +0x7a  call    mldsa65_polyeta_unpack
     after_mldsa65_polyeta_unpack:
      +0x7f  mov     rsi, r12
      +0x82  mov     rdi, rbx
      +0x85  call    mldsa_poly_add
     after_mldsa_poly_add:
      +0x8a  mov     rdi, rbx
      +0x8d  call    mldsa_poly_reduce
     after_mldsa_poly_reduce:
      +0x92  mov     rdi, rbx
      +0x95  call    mldsa_poly_caddq
     after_mldsa_poly_caddq:
      +0x9a  mov     rdx, rbx
      +0x9d  mov     rsi, rbx
      +0xa0  mov     rdi, r12
      +0xa3  call    mldsa_poly_power2round
     after_mldsa_poly_power2round:
      +0xa8  mov     rdi, r14
      +0xab  mov     rsi, r12
      +0xae  add     r14, 0x140
      +0xb5  call    mldsa_polyt1_pack
     after_mldsa_polyt1_pack:
      +0xba  mov     rdi, r13
      +0xbd  mov     rsi, rbx
      +0xc0  add     r13, 0x1a0
      +0xc7  call    mldsa_polyt0_pack
     after_mldsa_polyt0_pack:
      +0xcc  mov     eax, DWORD PTR [rsp+0x1c]
      +0xd0  add     eax, 0x1
     loop1_test:
      +0xd3  cmp     eax, 0x6
     loop1_back:
      +0xd6  jne     loop1
     loop1_exit:
      +0xdc  xor     eax, eax
      +0xde  mov     rdi, r12
      +0xe1  mov     ecx, 0x80
      +0xe6  rep stos QWORD PTR es:[rdi], rax
      +0xe9  mov     ecx, 0x80
      +0xee  mov     rdi, rbx
      +0xf1  rep stos QWORD PTR es:[rdi], rax
      +0xf4  mov     rbx, QWORD PTR [rsp+0x10]
      +0xf9  mov     edx, 0x7800
      +0xfe  xor     esi, esi
     +0x100  mov     rdi, rbx
     +0x103  call    memset
     after_memset:
     +0x108  lea     rsp, [rbp-0x28]
     +0x10c  xor     eax, eax
     +0x10e  pop     rbx
     +0x10f  pop     r12
     +0x111  pop     r13
     +0x113  pop     r14
     +0x115  pop     r15
     +0x117  pop     rbp
     ret:
     +0x118  ret

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0xefc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_compute_pack_t0_t165"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The vector s1hat (s1 in    *)
(* the NTT domain) of 5 polynomials sh at s1hat, the 6 polynomials of s2     *)
(* packed in 128 bytes each, s2b at s2, and rho, the 32 bytes r at rho: the  *)
(* 6 polynomials of t1 packed in 320 bytes each are written at pkt1 and the  *)
(* 6 of t0 packed in 416 bytes each at t0, with t = mld_compute_t, if the    *)
(* expansion of the matrix terminates, and the result is 0. The function     *)
(* saves RBP, the frame pointer, and five more registers below the return    *)
(* address, lowers RSP by up to 31 bytes to align it to 32 bytes, and then   *)
(* reserves 32800 bytes for the matrix, two polynomials and three spills,    *)
(* below which the call of mldsa65_polyvec_matrix_expand_eager uses 5174     *)
(* bytes, with its return address: 38053 bytes of stack below the return     *)
(* address in all. The GOT entry of memset, which the stub reads, and the    *)
(* region (ea,el) that memset may read are apart from the outputs and the    *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 6 5 r /\
          PAIRWISE nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 38053),38053)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 38053),38053)]
           [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pkt1,1920); (t0,2496)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mld_compute_pack_t0_t165) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                  memory :> bytes(word_sub stackpointer (word 38053),38053)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address, the GOT entry of memset, the region (ea,el) that memset may read *)
(* and the constants of the callees, and the writes within the outputs and   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 6 5 r /\
          PAIRWISE nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 38053),38053)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 38053),38053)]
           [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pkt1,1920); (t0,2496)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mld_compute_pack_t0_t165) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                       e2 = f_events pkt1 t0 s1hat s2 rho r mf pc
                              (word_sub stackpointer (word 38053))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,5120; s2,768; rho,32; pkt1,1920; t0,2496;
                         word_sub stackpointer (word 38053),38053;
                         stackpointer,8; word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc +
                           mldsa65_polyvec_matrix_expand_eager_consts),4]
                        [pkt1,1920; t0,2496;
                         word_sub stackpointer (word 38053),38053]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                  memory :> bytes(word_sub stackpointer (word 38053),38053)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 6 5 r /\
          PAIRWISE nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 38053),38053)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 38053),38053)]
           [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pkt1,1920); (t0,2496)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mld_compute_pack_t0_t165) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                       e2 = f_events pkt1 t0 s1hat s2 rho r mf pc
                              (word_sub stackpointer (word 38053))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,5120; s2,768; rho,32; pkt1,1920; t0,2496;
                         word_sub stackpointer (word 38053),38053;
                         stackpointer,8; word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc +
                           mldsa65_polyvec_matrix_expand_eager_consts),4]
                        [pkt1,1920; t0,2496;
                         word_sub stackpointer (word 38053),38053]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                  memory :> bytes(word_sub stackpointer (word 38053),38053)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
