(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Zeroing a context of four SHAKE128 states. This is the code for           *)
(* mlkem_shake128x4_release from mlkem-native's portable C implementation    *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), which zeroes  *)
(* the 800 bytes of the context with memset from the C library, called       *)
(* through the PLT of the image. It is verified in the whole image (see      *)
(* libmlkem.ml), assuming the contracts for memset in                        *)
(* utils/mlkem_native_libc.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem_shake128x4_release:
       +0x0: stp     x30, x19, [sp, #-16]!
       +0x4: mov     w1, wzr
       +0x8: mov     w2, #0x320
       +0xc: mov     x19, x0
      +0x10: bl      <memset@plt>
      +0x14: ldp     x30, x19, [sp], #16
      +0x18: ret

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_shake128x4_release"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry, with its code and data in the region (ea,el), which must   *)
(* not overlap the context or the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (st,800) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 16),16)]
         [(word pc,libmlkem_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_shake128x4_release) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st] s /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(st,800)) s = 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC (1--5) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC 5 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC (11--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEMSET_ZERO_BYTES THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. As for mlkem_poly_compress_d4, it is stated          *)
(* directly, since the events depend on the GOT entry, the address of        *)
(* memset, as well as on the events of memset given by its contract.         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e st pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 16),16]
            [word pc,libmlkem_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_clang17_O3_mc /\
                     read PC s = word (pc + mlkem_shake128x4_release) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events st mf pc
                               (word_sub stackpointer (word 16))
                               returnaddress /\
                        memaccess_inbounds e2
                         [st,800; word_sub stackpointer (word 16),16;
                          word(pc + got_memset),8; ea,el]
                         [st,800; word_sub stackpointer (word 16),16]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 16),16)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_safety_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC (1--5) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC 5 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref [`pc:num`; `st:int64`; `stackpointer:int64`; `returnaddress:int64`;
         `mf:int64`])
   10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O3_EXEC (11--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
