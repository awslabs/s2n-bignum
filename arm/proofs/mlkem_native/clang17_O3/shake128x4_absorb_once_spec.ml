(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE128 states.     *)
(* This is the code for mlkem_shake128x4_absorb_once from mlkem-native's     *)
(* portable C implementation compiled by clang 17 with -O3 (see              *)
(* mlkem_native/README.md), which zeroes the 800 bytes of the context with   *)
(* memset from the C library, called through the PLT of the image, and then  *)
(* calls mlk_keccak_absorb_once_x4 with the rate 168 of SHAKE128, as a tail  *)
(* call. It is verified in the whole image (see                              *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlk_keccak_absorb_once_x4 in the image and assuming the contracts for     *)
(* memset in utils/mlkem_native_libc.ml.                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccak_absorb_once_x4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem_shake128x4_absorb_once:
      +0x0: str     x30, [sp, #-64]!
      +0x4: stp     x24, x23, [sp, #16]
      +0x8: stp     x22, x21, [sp, #32]
      +0xc: stp     x20, x19, [sp, #48]
     +0x10: mov     x22, x2
     +0x14: mov     x23, x1
     +0x18: mov     w1, wzr
     +0x1c: mov     w2, #0x320
     +0x20: mov     x19, x5
     +0x24: mov     x20, x4
     +0x28: mov     x21, x3
     +0x2c: mov     x24, x0
     +0x30: bl      memset
     +0x34: mov     x0, x24
     +0x38: mov     x2, x23
     +0x3c: mov     x3, x22
     +0x40: mov     x4, x21
     +0x44: mov     x5, x20
     +0x48: mov     x6, x19
     +0x4c: ldp     x20, x19, [sp, #48]
     +0x50: mov     w1, #0xa8
     +0x54: ldp     x22, x21, [sp, #32]
     +0x58: ldp     x24, x23, [sp, #16]
     +0x5c: ldr     x30, [sp], #64
     +0x60: b       mlk_keccak_absorb_once_x4

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_shake128x4_absorb_once"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry, with its code and data in the region (ea,el). The result   *)
(* is as for mlk_keccak_absorb_once on each message, with r = 168 and p =    *)
(* 0x1F as in shake128 in common/fips202.ml. The stack is the 320 bytes used *)
(* by mlk_keccak_absorb_once_x4, which include the 64 of the function before *)
(* the tail call.                                                            *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st m0 m1 m2 m3 mlen M0 M1 M2 M3 guard mf ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (st,800) (word_sub stackpointer (word 320),320) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 320),320)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_shake128x4_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 168
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb 168
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb 168
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb 168
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset, as for mlkem_shake128x4_release.                     *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e st m0 m1 m2 m3 mlen guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 320),320) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 320),320]
            [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
             word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_clang17_O3_mc /\
                     read PC s = word (pc + mlkem_shake128x4_absorb_once) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events m0 m1 m2 m3 st mlen guard mf pc
                               (word_sub stackpointer (word 320))
                               returnaddress /\
                        memaccess_inbounds e2
                         [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                          word_sub stackpointer (word 320),320;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memset),8;
                          ea,el]
                         [st,800; word_sub stackpointer (word 320),320]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlk_keccak_absorb_once_x4 and assuming the combined contract for       *)
(* memset in utils/mlkem_native_libc_full.ml, since                          *)
(* mlk_keccak_absorb_once_x4 needs the context to be zero.                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
                 returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 320),320) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 320),320]
            [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
             word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_clang17_O3_mc /\
                     read PC s = word (pc + mlkem_shake128x4_absorb_once) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read (memory :> bytes(m0,mlen)) s = M0 /\
                     read (memory :> bytes(m1,mlen)) s = M1 /\
                     read (memory :> bytes(m2,mlen)) s = M2 /\
                     read (memory :> bytes(m3,mlen)) s = M3 /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     read (memory :> wbytes st) s =
                     word_xor
                      (keccak_absorb 168
                        (M0 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M0 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     read (memory :> wbytes (word_add st (word 200))) s =
                     word_xor
                      (keccak_absorb 168
                        (M1 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M1 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     read (memory :> wbytes (word_add st (word 400))) s =
                     word_xor
                      (keccak_absorb 168
                        (M2 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M2 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     read (memory :> wbytes (word_add st (word 600))) s =
                     word_xor
                      (keccak_absorb 168
                        (M3 + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen))
                        (mlen DIV 168))
                      (word((M3 + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                            2 EXP (8 * 168 * mlen DIV 168) MOD
                            2 EXP (8 * 168))) /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events m0 m1 m2 m3 st mlen guard mf pc
                               (word_sub stackpointer (word 320))
                               returnaddress /\
                        memaccess_inbounds e2
                         [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                          word_sub stackpointer (word 320),320;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memset),8;
                          ea,el]
                         [st,800; word_sub stackpointer (word 320),320]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
