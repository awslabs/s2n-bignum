(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE128 states.     *)
(* This is the code for mlkem_shake128x4_absorb_once from mlkem-native's     *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which zeroes the 800 bytes of the context with   *)
(* memset from the C library, called through the PLT at 0x840 of the image,  *)
(* and then calls mlk_keccak_absorb_once_x4 with the rate 168 of SHAKE128,   *)
(* as a tail call. It is verified in the whole image (see                    *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2910, using  *)
(* the theorems for mlk_keccak_absorb_once_x4 at 0x27a0 in the image and     *)
(* assuming the contracts for memset in utils/mlkem_native_libc.ml.          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native_keccak_absorb_once_x4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image, and the PLT stub for memset:

    2910: stp     x19, x20, [sp, #-64]!
    2914: mov     x20, x1
    2918: mov     x19, x0
    291c: mov     w1, #0x0
    2920: stp     x21, x22, [sp, #16]
    2924: mov     x22, x3
    2928: mov     x21, x2
    292c: mov     x2, #0x320
    2930: stp     x23, x24, [sp, #32]
    2934: mov     x23, x4
    2938: mov     x24, x5
    293c: str     x30, [sp, #48]
    2940: bl      840 <memset@plt>
    2944: ldr     x30, [sp, #48]
    2948: mov     x6, x24
    294c: mov     x5, x23
    2950: mov     x4, x22
    2954: ldp     x23, x24, [sp, #32]
    2958: mov     x3, x21
    295c: ldp     x21, x22, [sp, #16]
    2960: mov     x2, x20
    2964: mov     x0, x19
    2968: mov     w1, #0xa8
    296c: ldp     x19, x20, [sp], #64
    2970: b       27a0 <mlk_keccak_absorb_once_x4.constprop.0>

    840: adrp    x16, 1f000 <mlk_zetas+0x18c80>
    844: ldr     x17, [x16, #4072]
    848: add     x16, x16, #0xfe8
    84c: br      x17
 ***)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x2910,0x2974; 0x840,0x850];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry at 0x1ffe8, with its code and data in the region (ea,el).   *)
(* The result is as for mlk_keccak_absorb_once on each message, with r = 168 *)
(* and p = 0x1F as in shake128 in common/fips202.ml. The stack is the 304    *)
(* bytes used by mlk_keccak_absorb_once_x4, which include the 64 of the      *)
(* function before the tail call.                                            *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st m0 m1 m2 m3 mlen M0 M1 M2 M3 guard mf ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (st,800) (word_sub stackpointer (word 304),304) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 304),304)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2910) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
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
                memory :> bytes(word_sub stackpointer (word 304),304)])`,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
    `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 304 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--24) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Zeroing the context with memset ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (1--13) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC 13 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 18 THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEMSET_ZERO_BYTES o
    check (fun th -> is_forall(concl th) && free_in `st:int64` (concl th) &&
                     free_in `bytes8:int64->(int64->byte,byte)component`
                             (concl th))) THEN

  (*** The tail call of mlk_keccak_absorb_once_x4 ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (19--30) THEN
  LOCAL_ABSORB_X4_TAC
   [`read X0 s`; `168`; `read X2 s`; `read X3 s`; `read X4 s`; `read X5 s`;
    `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 31 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset, as for mlkem_shake128x4_release.                     *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e st m0 m1 m2 m3 mlen guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 304),304) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 304),304]
            [m0,mlen; m1,mlen; m2,mlen; m3,mlen;
             word pc,0x6480; word(pc + 0x1fff8),8; guard,8;
             word(pc + 0x1ffe8),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O2_mc /\
                     read PC s = word (pc + 0x2910) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                     read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                     read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events m0 m1 m2 m3 st mlen guard mf pc
                               (word_sub stackpointer (word 304))
                               returnaddress /\
                        memaccess_inbounds e2
                         [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                          word_sub stackpointer (word 304),304;
                          word(pc + 0x1fff8),8; guard,8;
                          word(pc + 0x62b0),192; word(pc + 0x1ffe8),8;
                          ea,el]
                         [st,800; word_sub stackpointer (word 304),304]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 304),304)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_safety_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--24) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (1--13) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC 13 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET"
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref [`pc:num`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
         `m3:int64`; `mlen:num`; `guard:int64`; `mf:int64`;
         `stackpointer:int64`; `returnaddress:int64`])
   18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (19--30) THEN
  REMOVE_THEN "H_ABSORB" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `168`; `read X2 s`; `read X3 s`;
       `read X4 s`; `read X5 s`; `mlen:num`; `guard:int64`; `pc:num`;
       `read SP s`; `read X30 s`] 31 THENL
     [EXISTS_E2_TAC
       (ref [`pc:num`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
             `m3:int64`; `mlen:num`; `guard:int64`; `mf:int64`;
             `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_ABSORB" safety_th]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
