(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a SHAKE128 state. This is the code for     *)
(* mlkem_shake128_absorb_once from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md), which calls     *)
(* mlk_keccak_absorb_once with the rate 168 of SHAKE128 and the first byte   *)
(* 0x1F of its padding, as a tail call. It is verified in the whole image    *)
(* (see libmlkem.ml), using the theorems for mlk_keccak_absorb_once in the   *)
(* image and assuming the contracts for memset in                            *)
(* utils/mlkem_native_libc.ml, since mlk_keccak_absorb_once zeroes the state *)
(* with memset.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128_absorb_once:
       +0x0: mov     x3, x2
       +0x4: mov     w4, #0x1f
       +0x8: mov     x2, x1
       +0xc: mov     w1, #0xa8
      +0x10: b       <mlk_keccak_absorb_once>
 ***)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_shake128_absorb_once"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The result is as for mlk_keccak_absorb_once, with r =  *)
(* 168 and p = 0x1F as in shake128 in common/fips202/fips202.ml. The state   *)
(* is the first 200 bytes of the context. The contract for memset is that    *)
(* at the address mf in the GOT entry, with its code and data in the region  *)
(* (ea,el), which must not overlap the state or the stack.                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st m mlen M mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 304),304)] /\
        ALLPAIRS nonoverlapping
         [(st,200); (word_sub stackpointer (word 304),304)]
         [(word pc,libmlkem_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_shake128_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,mlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 168
                     (M + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. As for mlk_keccak_absorb_once, it is stated          *)
(* directly, since the events depend on the GOT entry, the address of        *)
(* memset, as well as on the events of memset given by its contract.         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
     forall e st m mlen pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 304),304] /\
       ALLPAIRS nonoverlapping
        [st,200; word_sub stackpointer (word 304),304]
        [word pc,libmlkem_size; word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_shake128_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen] s /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen mf pc
                           (word_sub stackpointer (word 304)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 304),304;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 304),304]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlk_keccak_absorb_once and assuming the combined contract for memset   *)
(* in utils/mlkem_native_libc_full.ml.                                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
     forall e st m mlen M pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 304),304] /\
       ALLPAIRS nonoverlapping
        [st,200; word_sub stackpointer (word 304),304]
        [word pc,libmlkem_size; word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_shake128_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen] s /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read (memory :> bytes(m,mlen)) s = M /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb 168
                    (M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen mf pc
                           (word_sub stackpointer (word 304)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 304),304;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 304),304]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
