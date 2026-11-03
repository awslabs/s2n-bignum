(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE128 states.     *)
(* This is the code for mlkem_shake128x4_absorb_once from mlkem-native's     *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which zeroes the 800 bytes of the context with   *)
(* an inline memset, as mlkem_shake128_release does for one state, and then  *)
(* calls mlk_keccak_absorb_once_x4 with the rate 168 of SHAKE128, passing    *)
(* the length of the messages on the stack. It is verified in the whole      *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x3720, using the theorems for mlk_keccak_absorb_once_x4 at 0x35d0 in the *)
(* image. The memset uses REP STOSQ, so the specifications assume that the   *)
(* direction flag DF is clear, as the ABI requires on entry.                 *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccak_absorb_once_x4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    3720: sub    rsp,0x10
    3724: mov    r10,rdi
    3727: mov    QWORD PTR [rdi],0x0
    372e: xor    eax,eax
    3730: mov    QWORD PTR [rdi+0x318],0x0
    373b: lea    rdi,[rdi+0x8]
    373f: mov    r11,rcx
    3742: mov    rcx,r10
    3745: and    rdi,0xfffffffffffffff8
    3749: sub    rcx,rdi
    374c: add    ecx,0x320
    3752: shr    ecx,0x3
    3755: rep    stos QWORD PTR es:[rdi],rax
    3758: push   r9
    375a: mov    rcx,rdx
    375d: mov    r9,r8
    3760: mov    rdx,rsi
    3763: mov    r8,r11
    3766: mov    esi,0xa8
    376b: mov    rdi,r10
    376e: call   35d0 <mlk_keccak_absorb_once_x4.constprop.0>
    3773: add    rsp,0x18
    3777: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3720,0x3778];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlk_keccak_absorb_once_x4. The result is as for that function on each  *)
(* message, with r = 168 and p = 0x1F as in shake128 in common/fips202.ml,   *)
(* the states being the four consecutive 200-byte parts of the context.      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  time prove
 (`exists f_events.
     forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer
            returnaddress.
       aligned 16 (word pc:int64) /\
       nonoverlapping (st,800) (word_sub stackpointer (word 416),424) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 416),424]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen; word pc,0x82a0]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3720) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                 (read DF s <=> false) /\
                 read (memory :> bytes(m0,mlen)) s = M0 /\
                 read (memory :> bytes(m1,mlen)) s = M1 /\
                 read (memory :> bytes(m2,mlen)) s = M2 /\
                 read (memory :> bytes(m3,mlen)) s = M3 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
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
                    e2 = f_events m0 m1 m2 m3 st mlen pc
                           (word_sub stackpointer (word 416)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 416),424;
                      word(pc + 0x80c0),192]
                     [st,800; word_sub stackpointer (word 416),416]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 416),416)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 416 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (1--12) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC 13 THEN
  MEMSET_DONE_TAC `st:int64` 800 "s13" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (14--21) THEN
  REMOVE_THEN "H_ABSORB" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `168`; `read RDX s`;
       `read RCX s`; `read R8 s`; `read R9 s`; `mlen:num`;
       `M0:num`; `M1:num`; `M2:num`; `M3:num`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] 22 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `st:int64`; `m0:int64`; `m1:int64`;
                          `m2:int64`; `m3:int64`; `mlen:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_ABSORB" safety_th]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (23--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The correctness and safety theorems alone, from the combined one.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        nonoverlapping (st,800) (word_sub stackpointer (word 416),424) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 416),424)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen); (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3720) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
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
                         2 EXP (8 * 168))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 416),416)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`])) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[ALLPAIRS; ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e st m0 m1 m2 m3 mlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       nonoverlapping (st,800) (word_sub stackpointer (word 416),424) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 416),424]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen; word pc,0x82a0]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3720) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m0 m1 m2 m3 st mlen pc
                           (word_sub stackpointer (word 416)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 416),424;
                      word(pc + 0x80c0),192]
                     [st,800; word_sub stackpointer (word 416),416]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 416),416)])`,
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (m,mm) ->
    GHOST_INTRO_TAC mm (subst [m,`m:int64`]
     `read (memory :> bytes(m,mlen)):x86state->num`))
   [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
    `m3:int64`,`M3:num`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;
