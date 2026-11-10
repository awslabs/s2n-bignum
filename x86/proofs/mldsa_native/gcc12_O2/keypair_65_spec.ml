(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation with random bytes: the statement. This is the code for     *)
(* mldsa65_keypair (mld_sign_keypair in sign.c, an external API function)    *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which aligns its frame to 32 bytes, gets 32 *)
(* random bytes with randombytes, which it calls through the PLT, into a     *)
(* buffer on the stack, returns -3 (MLD_ERR_RNG_FAIL) if that fails, and     *)
(* otherwise generates the keys from them with mldsa65_keypair_internal, and *)
(* then zeroes the buffer with SSE stores. It is verified in the whole image *)
(* (see libmldsa.ml), using the theorem for the callee and the contracts     *)
(* memset_full_contract and randombytes_safety_contract of                   *)
(* utils/mldsa_native_libc.ml for the C library functions, and shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keypair_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for randombytes:

    mldsa65_keypair:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r13
       +0x6  mov     r13, rsi
       +0x9  mov     esi, 0x20
       +0xe  push    r12
      +0x10  mov     r12, rdi
      +0x13  push    rbx
      +0x14  and     rsp, 0xffffffffffffffe0
      +0x18  sub     rsp, 0x20
      +0x1c  mov     rbx, rsp
      +0x1f  mov     rdi, rbx
      +0x22  call    randombytes
     after_randombytes:
      +0x27  test    eax, eax
      +0x29  jne     join2
      +0x2b  mov     rdx, rbx
      +0x2e  mov     rsi, r13
      +0x31  mov     rdi, r12
      +0x34  call    mldsa65_keypair_internal
     join1: after_mldsa65_keypair_internal:
      +0x39  pxor    xmm0, xmm0
      +0x3d  movaps  XMMWORD PTR [rsp], xmm0
      +0x41  movaps  XMMWORD PTR [rsp+0x10], xmm0
      +0x46  lea     rsp, [rbp-0x18]
      +0x4a  pop     rbx
      +0x4b  pop     r12
      +0x4d  pop     r13
      +0x4f  pop     rbp
     ret:
      +0x50  ret
      +0x51  nop     DWORD PTR [rax+0x0]
     join2:
      +0x58  mov     eax, 0xfffffffd
      +0x5d  jmp     join1

    plt_randombytes:
       +0x0  jmp     QWORD PTR [rip+0xefca]
                     // got_randombytes
       +0x6  push    0x1
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_keypair"; layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. Either   *)
(* randombytes succeeds and the function returns 0 with the keys             *)
(* mld_keypair_pk_65 SEED and mld_keypair_sk_65 SEED for some seed SEED (the *)
(* random bytes), or it fails and the function returns -3. The theorem       *)
(* assumes that the samplings terminate for every seed. The function saves   *)
(* RBP, the frame pointer, and three more registers below the return         *)
(* address, lowers RSP by up to 31 bytes to align it to 32 bytes, and then   *)
(* reserves 32 bytes for the buffer, below which the call of                 *)
(* mldsa65_keypair_internal uses 43604 bytes, with its return address: 43699 *)
(* bytes of stack below the return address in all. The GOT entries of the C  *)
(* library functions and the region (ea,el) that they may read are apart     *)
(* from the keys and the stack.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !pk sk pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 6 5
                       (mld_keypair_rho 6 5 SEED) /\
                      mld_keypair_terminates_65 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43699),43699)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43699),43699)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_keypair) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> (!j. j < 1952
                                ==> read(memory :> bytes8
                                          (word_add pk (word j))) s =
                                    mld_keypair_pk_65 SEED j) /\
                           (!j. j < 4032
                                ==> read(memory :> bytes8
                                          (word_add sk (word j))) s =
                                    mld_keypair_sk_65 SEED j)))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43699),43699)])`;;

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the result and, for a seed SEED   *)
(* of the keys, rho and what the C code declassifies in the sampling         *)
(* (mld_keypair_declass_65), with all accesses within the arguments, the     *)
(* stack, the return address, the GOT entries, the region (ea,el) that the C *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e pk sk pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 6 5
                       (mld_keypair_rho 6 5 SEED) /\
                      mld_keypair_terminates_65 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43699),43699)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43699),43699)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_keypair) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> (!j. j < 1952
                                ==> read(memory :> bytes8
                                          (word_add pk (word j))) s =
                                    mld_keypair_pk_65 SEED j) /\
                           (!j. j < 4032
                                ==> read(memory :> bytes8
                                          (word_add sk (word j))) s =
                                    mld_keypair_sk_65 SEED j)) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events pk sk (C_RETURN s)
                             (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) mf mr pc
                             (word_sub stackpointer (word 43699))
                             returnaddress /\
                        memaccess_inbounds e2
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 43699),43699;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc + mldsa_poly_power2round_consts),32;
                          word(pc + mldsa65_keypair_internal_consts),2;
                          word(pc +
                            mldsa65_polyvec_matrix_expand_eager_consts),4]
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 43699),43699]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43699),43699)])`;;

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for a seed    *)
(* SEED of the secret key if the result is 0: they depend on the values that *)
(* the sampling declassifies, which only the seed determines.                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e pk sk pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 6 5
                       (mld_keypair_rho 6 5 SEED) /\
                      mld_keypair_terminates_65 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43699),43699)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43699),43699)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_keypair) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0
                       ==> !j. j < 4032
                               ==> read(memory :> bytes8
                                         (word_add sk (word j))) s =
                                   mld_keypair_sk_65 SEED j) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events pk sk (C_RETURN s)
                             (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) mf mr pc
                             (word_sub stackpointer (word 43699))
                             returnaddress /\
                        memaccess_inbounds e2
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 43699),43699;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc + mldsa_poly_power2round_consts),32;
                          word(pc + mldsa65_keypair_internal_consts),2;
                          word(pc +
                            mldsa65_polyvec_matrix_expand_eager_consts),4]
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 43699),43699]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43699),43699)])`;;

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
