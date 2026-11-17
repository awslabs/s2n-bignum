(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t144 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). In this           *)
(* configuration the matrix is not expanded:                                 *)
(* mldsa44_polyvec_matrix_expand_lazy only copies rho into a structure       *)
(* mld_polymat_lazy on the stack, and for each row k the code computes       *)
(* polynomial k of t = A * s1 + s2 with                                      *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy, which samples the   *)
(* entries of row k when it needs them, mldsa_poly_invntt_tomont,            *)
(* mldsa44_polyeta_unpack (for s2), mldsa_poly_add, mldsa_poly_reduce and    *)
(* mldsa_poly_caddq, splits it with mldsa_poly_power2round and packs t1 and  *)
(* t0 with mldsa_polyt1_pack and mldsa_polyt0_pack, before zeroing the two   *)
(* polynomials and the structure, which gcc does inline with REP STOSQ, so   *)
(* the direction flag must be clear, as the ABI requires on entry. It is     *)
(* verified in the whole image (see libmldsa.ml) against mld_compute_t_lazy  *)
(* of common/mldsa_native_polyvec_lazy.ml, using the theorems for the        *)
(* callees, assuming that the sampling of the matrix terminates              *)
(* (mld_matrix_terminates), and shown to be constant time and memory safe,   *)
(* with the events depending on rho, which is public.                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyeta_unpack_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_power2round_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyt1_pack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyt0_pack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mld_compute_pack_t0_t144:
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
      +0x1d  sub     rsp, 0xc40
      +0x24  lea     rax, [rsp+0x820]
      +0x2c  mov     QWORD PTR [rsp+0x8], rdx
      +0x31  lea     rbx, [rsp+0x20]
      +0x36  mov     rdi, rax
      +0x39  mov     QWORD PTR [rsp+0x10], rax
      +0x3e  lea     r12, [rsp+0x420]
      +0x46  call    mldsa44_polyvec_matrix_expand_lazy
     after_mldsa44_polyvec_matrix_expand_lazy:
      +0x4b  xor     eax, eax
     loop1:
      +0x4d  mov     rdx, QWORD PTR [rsp+0x8]
      +0x52  mov     rsi, QWORD PTR [rsp+0x10]
      +0x57  mov     ecx, eax
      +0x59  mov     rdi, rbx
      +0x5c  mov     DWORD PTR [rsp+0x1c], eax
      +0x60  call    mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy
     after_mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy:
      +0x65  mov     rdi, rbx
      +0x68  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont:
      +0x6d  mov     rsi, r15
      +0x70  mov     rdi, r12
      +0x73  add     r15, 0x60
      +0x77  call    mldsa44_polyeta_unpack
     after_mldsa44_polyeta_unpack:
      +0x7c  mov     rsi, r12
      +0x7f  mov     rdi, rbx
      +0x82  call    mldsa_poly_add
     after_mldsa_poly_add:
      +0x87  mov     rdi, rbx
      +0x8a  call    mldsa_poly_reduce
     after_mldsa_poly_reduce:
      +0x8f  mov     rdi, rbx
      +0x92  call    mldsa_poly_caddq
     after_mldsa_poly_caddq:
      +0x97  mov     rdx, rbx
      +0x9a  mov     rsi, rbx
      +0x9d  mov     rdi, r12
      +0xa0  call    mldsa_poly_power2round
     after_mldsa_poly_power2round:
      +0xa5  mov     rdi, r14
      +0xa8  mov     rsi, r12
      +0xab  add     r14, 0x140
      +0xb2  call    mldsa_polyt1_pack
     after_mldsa_polyt1_pack:
      +0xb7  mov     rdi, r13
      +0xba  mov     rsi, rbx
      +0xbd  add     r13, 0x1a0
      +0xc4  call    mldsa_polyt0_pack
     after_mldsa_polyt0_pack:
      +0xc9  mov     eax, DWORD PTR [rsp+0x1c]
      +0xcd  add     eax, 0x1
     loop1_test:
      +0xd0  cmp     eax, 0x4
     loop1_back:
      +0xd3  jne     loop1
     loop1_exit:
      +0xd9  xor     eax, eax
      +0xdb  mov     rdi, r12
      +0xde  mov     ecx, 0x80
      +0xe3  rep stos QWORD PTR es:[rdi], rax
      +0xe6  mov     ecx, 0x80
      +0xeb  mov     rdi, rbx
      +0xee  rep stos QWORD PTR es:[rdi], rax
      +0xf1  mov     rdi, QWORD PTR [rsp+0x10]
      +0xf6  mov     ecx, 0x84
      +0xfb  rep stos QWORD PTR es:[rdi], rax
      +0xfe  mov     rdi, QWORD PTR [rsp+0x10]
     +0x103  lea     rsp, [rbp-0x28]
     +0x107  pop     rbx
     +0x108  pop     r12
     +0x10a  pop     r13
     +0x10c  pop     r14
     +0x10e  pop     r15
     +0x110  pop     rbp
     ret:
     +0x111  ret
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mld_compute_pack_t0_t144"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector s1hat (s1 in the NTT domain) of 4 polynomials sh  *)
(* at s1hat, the 4 polynomials of s2 packed in 96 bytes each, s2b at s2, and *)
(* rho, the 32 bytes r at rho: the 4 polynomials of t1 packed in 320 bytes   *)
(* each are written at pkt1 and the 4 of t0 packed in 416 bytes each at t0,  *)
(* with t = mld_compute_t_lazy, if the sampling of the matrix terminates,    *)
(* and the result is 0. The function saves RBP, the frame pointer, and five  *)
(* more registers below the return address, lowers RSP by up to 31 bytes to  *)
(* align it to 32 bytes, and then reserves 3136 bytes for the structure      *)
(* mld_polymat_lazy (1056 bytes), two polynomials and three spills, below    *)
(* which the call of mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy    *)
(* uses 1678 bytes, with its return address: 4893 bytes of stack below the   *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        PAIRWISE nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4893),4893)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4893),4893)]
         [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1280); (t0,1664)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t144) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
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
                              (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j) /\
                  (!j. j < 1664
                       ==> read(memory :> bytes8(word_add t0 (word j))) s =
                           mld_polyvec_pack 416 mld_polyt0_pack
                            (mld_polyvec_map mld_poly_power2round_lo
                              (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                memory :> bytes(word_sub stackpointer (word 4893),4893)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho and the stack, with all       *)
(* accesses within the arguments, the stack, the return address and the      *)
(* constants of the callees, and the writes within the outputs and the       *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        PAIRWISE nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4893),4893)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4893),4893)]
         [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1280); (t0,1664)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t144) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
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
                              (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j) /\
                  (!j. j < 1664
                       ==> read(memory :> bytes8(word_add t0 (word j))) s =
                           mld_polyvec_pack 416 mld_polyt0_pack
                            (mld_polyvec_map mld_poly_power2round_lo
                              (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r
                                 sh s2b)) j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pkt1 t0 s1hat s2 rho r pc
                            (word_sub stackpointer (word 4893))
                            returnaddress /\
                     memaccess_inbounds e2
                      [s1hat,4096; s2,384; rho,32; pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4893),4893;
                       stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16;
                       word(pc + mldsa_poly_power2round_consts),32]
                      [pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4893),4893]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                memory :> bytes(word_sub stackpointer (word 4893),4893)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e pkt1 t0 s1hat s2 rho sh s2b r pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        PAIRWISE nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4893),4893)] /\
        ALLPAIRS nonoverlapping
         [(pkt1,1280); (t0,1664);
          (word_sub stackpointer (word 4893),4893)]
         [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pkt1,1280); (t0,1664)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mld_compute_pack_t0_t144) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                  (read DF s <=> false) /\
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
                     e2 = f_events pkt1 t0 s1hat s2 rho r pc
                            (word_sub stackpointer (word 4893))
                            returnaddress /\
                     memaccess_inbounds e2
                      [s1hat,4096; s2,384; rho,32; pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4893),4893;
                       stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16;
                       word(pc + mldsa_poly_power2round_consts),32]
                      [pkt1,1280; t0,1664;
                       word_sub stackpointer (word 4893),4893]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                memory :> bytes(word_sub stackpointer (word 4893),4893)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
