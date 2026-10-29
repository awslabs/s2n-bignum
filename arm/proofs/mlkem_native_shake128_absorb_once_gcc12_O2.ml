(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a SHAKE128 state. This is the code for     *)
(* mlkem_shake128_absorb_once from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which calls     *)
(* mlk_keccak_absorb_once with the rate 168 of SHAKE128 and the first byte   *)
(* 0x1F of its padding, as a tail call. It is verified in the whole image    *)
(* (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x24d0,   *)
(* using the theorems for mlk_keccak_absorb_once at 0x23b0 in the image.     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccak_absorb_once_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    24d0: mov     x3, x2
    24d4: mov     w4, #0x1f
    24d8: mov     x2, x1
    24dc: mov     w1, #0xa8
    24e0: b       23b0 <mlk_keccak_absorb_once>
 ***)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x24d0,0x24e4];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The result is as for mlk_keccak_absorb_once, with      *)
(* r = 168 and p = 0x1F as in shake128 in common/fips202.ml. The state is    *)
(* the first 200 bytes of the context.                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st m mlen M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 256),256)] /\
        ALL (nonoverlapping (word pc,0x6480))
         [(st,200); (word_sub stackpointer (word 256),256)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x24d0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m; word mlen] s /\
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
                memory :> bytes(word_sub stackpointer (word 256),256)])`,
  REWRITE_TAC[C_ARGUMENTS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_EXEC (1--5) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
   [`read X0 s`; `168`; `read X2 s`; `mlen:num`; `0x1F`; `M:num`;
    `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e st m mlen pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 256),256] /\
       ALL (nonoverlapping (word pc,0x6480))
        [st,200; word_sub stackpointer (word 256),256]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x24d0) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + 0x62b0),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_EXEC (1--5) THEN
  REMOVE_THEN "H_ABSORB" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `168`; `read X2 s`; `mlen:num`;
       `0x1F`; `pc:num`; `read SP s`; `read X30 s`] 6 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `st:int64`; `m:int64`; `mlen:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_ABSORB" safety_th]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
