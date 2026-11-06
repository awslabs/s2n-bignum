(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-1024 (FIPS 203 Algorithm 20). This is the     *)
(* code for mlkem1024_enc from mlkem-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It gets 32      *)
(* random bytes with randombytes into a buffer on the stack, and returns -3  *)
(* if that fails, and otherwise encapsulates with them as the message with   *)
(* mlkem1024_enc_derand. In both cases it zeroes the buffer. It is verified  *)
(* in the whole image (see libmlkem.ml), using the                           *)
(* theorem for mlkem1024_enc_derand in the image and the contract for        *)
(* randombytes.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/enc_derand_k4_spec.ml";;

(*** The code in the image, from the layout of gcc12_O2_mono:

    mlkem1024_enc:
     +0x0  stp     x19, x20, [sp, #-112]!
     +0x4  mov     x20, x0
  adrp1:
     +0x8  adrp    x3, <page>
     +0xc  ldr     x3, [x3, #4088]
                   // got_stack_chk_guard
    +0x10  stp     x21, x22, [sp, #16]
    +0x14  add     x19, sp, #0x4f
    +0x18  str     x30, [sp, #32]
    +0x1c  and     x19, x19, #0xffffffffffffffe0
    +0x20  mov     x21, x1
    +0x24  mov     x22, x2
    +0x28  ldr     x1, [x3]
    +0x2c  str     x1, [sp, #104]
    +0x30  mov     x1, #0x0
    +0x34  mov     x0, x19
    +0x38  mov     x1, #0x20
    +0x3c  bl      randombytes
  after_randombytes:
    +0x40  cbnz    w0, +0x8c                      -----+
    +0x44  mov     x2, x22                             |
    +0x48  mov     x1, x21                             |
    +0x4c  mov     x0, x20                             |
    +0x50  mov     x3, x19                             |
    +0x54  bl      mlkem1024_enc_derand                |
  join1: after_mlkem1024_enc_derand:                   |
    +0x58  stp     xzr, xzr, [x19]                <--+ |
    +0x5c  stp     xzr, xzr, [x19, #16]              | |
  adrp2:                                             | |
    +0x60  adrp    x1, <page>                        | |
    +0x64  ldr     x1, [x1, #4088]                   | |
                   // got_stack_chk_guard            | |
    +0x68  ldr     x3, [sp, #104]                    | |
    +0x6c  ldr     x2, [x1]                          | |
    +0x70  subs    x3, x3, x2                        | |
    +0x74  mov     x2, #0x0                          | |
    +0x78  b.ne    +0x94                          -+ | |
    +0x7c  ldp     x21, x22, [sp, #16]             | | |
    +0x80  ldr     x30, [sp, #32]                  | | |
    +0x84  ldp     x19, x20, [sp], #112            | | |
  ret:                                             | | |
    +0x88  ret                                     | | |
    +0x8c  mov     w0, #0xfffffffd                <----+
    +0x90  b       join1                          ---+
    +0x94  bl      stack_chk_fail                 <+
 ***)

let MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_randombytes"; layout_range "mlkem1024_enc"];;

let KER4_EXEC = MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The address of the buffer, which is aligned to 32 bytes within the stack  *)
(* frame, the callee, and the message as the random bytes.                   *)
(* ------------------------------------------------------------------------- *)

let KER4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 23167)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 23136 else 23152))`;;

let KER4_BUFFER_ADDRESS = assume_spec KER4_BUFFER_ADDRESS_STMT;;

let KER4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KER4_BUFFER_ADDRESS))
    else NO_TAC);;

let LOCAL_ENC_DERAND_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KER4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let KER4_M = `bytelist_of_num 32 rnd`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset, memcpy and          *)
(* randombytes. Either randombytes succeeds, and then for some message m of  *)
(* 32 bytes (the random bytes) the function behaves as mlkem1024_enc_derand  *)
(* with m: if the encapsulation key ek of 1568 bytes at pk passes the check  *)
(* of FIPS 203, it returns 0 and the shared secret at ss and the ciphertext  *)
(* at ct are those of mlkem_encaps_internal mlkem1024 ek m, and otherwise it *)
(* returns -4. Or randombytes fails and the function returns -3. The theorem *)
(* assumes that SampleNTT terminates for each entry of the matrix and that   *)
(* the stack does not contain address 0, as for mlkem1024_enc_derand. The    *)
(* stack is the 112 bytes of the function and the 23088 used by              *)
(* mlkem1024_enc_derand below them. The proof is by cases on whether the     *)
(* stack pointer is a multiple of 32, which gives the address b of the       *)
(* buffer, and on whether randombytes succeeds.                              *)
(* ------------------------------------------------------------------------- *)

let KER4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `ek:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `mr:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 23200 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 23200):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_randombytes:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_randombytes:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `randombytes_contract mr ea el ev`) (concl th)
    then LABEL_TAC "H_RANDOMBYTES" (REWRITE_RULE[randombytes_contract] th)
    else NO_TAC);;

let KER4_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KER4_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KER4_EXEC (4--8) THEN KER4_BUFFER_TAC THEN
  ARM_STEPS_TAC KER4_EXEC (9--16) THEN
  LIBC_PLT_TAC KER4_EXEC 16 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KER4_EXEC
   [`read X0 s`; `read X1 s`; `read X30 s`] 21 THEN
  ABBREV_TAC `rv = read X0 s21` THEN
  ABBREV_TAC (mk_eq(`rnd:num`,
   subst [KEM_SP b,`a:int64`] `read (memory :> bytes(a,32)) s21`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KER4_EXEC (22--27) THEN KEM_GOT_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP KEM_RANDOM_32 o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KER4_M),`32`))
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    LOCAL_ENC_DERAND_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `ek:byte list`;
      KER4_M; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`;
      `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 28 THEN
    ARM_STEPS_TAC KER4_EXEC (29--31) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER4_EXEC (32--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN EXISTS_TAC KER4_M THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    ARM_STEPS_TAC KER4_EXEC (22--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER4_EXEC (28--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ct ss pk (ek:byte list) guard mf mc mr ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        randombytes_contract mr ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1568 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 23200),23200) /\
        nonoverlapping (pk,1568) (word pc,libmlkem_size) /\
        PAIRWISE nonoverlapping
         [(ct,1568); (ss,32); (word_sub stackpointer (word 23200),23200)] /\
        ALLPAIRS nonoverlapping
         [(ct,1568); (ss,32); (word_sub stackpointer (word 23200),23200)]
         [(pk,1568); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (word(pc + got_randombytes),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem1024_enc) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ct; ss; pk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,1568)) s = num_of_bytelist ek)
             (\s. read PC s = returnaddress /\
                  ((?m. LENGTH m = 32 /\
                        (mlkem_ek_check mlkem1024 ek
                         ==> read (memory :> bytes(ss,32)) s =
                             num_of_bytelist
                              (FST(mlkem_encaps_internal mlkem1024 ek m)) /\
                             read (memory :> bytes(ct,1568)) s =
                             num_of_bytelist
                              (SND(mlkem_encaps_internal mlkem1024 ek m))) /\
                        C_RETURN s =
                        (if mlkem_ek_check mlkem1024 ek then word 0
                         else word 0xfffffffc)) \/
                   C_RETURN s = word 0xfffffffd))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ct,1568); memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 23200),23200)])`;;

let MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset and the safety contracts for memcpy and randombytes. The events    *)
(* depend only on the addresses, on the encapsulation key and on whether     *)
(* randombytes fails, when the result is -3, but not on the random message.  *)
(* They are given by cases on whether the stack pointer is a multiple of 32  *)
(* and on whether the result is -3.                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KER_SAFE_TEMPLATE =
 `\(ct:int64) (ss:int64) (pk:int64) (guard:int64) (mf:int64) (mc:int64)
   (mr:int64) (pc:num) (sp:int64) (ra:int64) (ek:byte list) (r:int64).
   if aligned 32 sp
   then (if r = word 4294967293
         then f_ev_a0 ct ss pk guard mf mc mr pc sp ra
         else f_ev_a1 ct ss pk guard mf mc mr pc sp ra ek)
   else (if r = word 4294967293
         then f_ev_u0 ct ss pk guard mf mc mr pc sp ra
         else f_ev_u1 ct ss pk guard mf mc mr pc sp ra ek)
   :(uarch_event)list`;;

let KER_SAFE_ALLOWED =
  [`pc:num`; `ct:int64`; `ss:int64`; `pk:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `mr:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `ek:byte list`];;

let KER4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `randombytes_safety_contract mr ea el ev`)
           (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[randombytes_safety_contract] th) "H_RANDOMBYTES"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP
         MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
         (CONJ th1 th2)) "H_INNER")
    else NO_TAC) THEN
  CONCRETIZE_F_EVENTS_TAC KER_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 23200):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_randombytes:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_randombytes:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28);;

let KER4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KER4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KER_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KER4_SAFE_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KER4_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KER4_EXEC (4--8) THEN KER4_BUFFER_TAC THEN
  ARM_STEPS_TAC KER4_EXEC (9--16) THEN
  LIBC_PLT_TAC KER4_EXEC 16 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" KER4_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref KER_SAFE_ALLOWED) 21 THEN
  ABBREV_TAC `rv = read X0 s21` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KER4_EXEC (22--27) THEN KEM_GOT_TAC THEN
    KER4_SAFE_CALL_TAC "H_INNER"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X3 s`; `ek:byte list`; `guard:int64`; `pc:num`; `read SP s`;
      `read X30 s`] 28 THEN
    ARM_STEPS_TAC KER4_EXEC (29--31) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER4_EXEC (32--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~((if mlkem_ek_check mlkem1024 ek then word 0 else word 4294967292) =
        (word 4294967293:int64))`
     (fun th -> REWRITE_TAC[th]) THENL
     [COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ARM_STEPS_TAC KER4_EXEC (22--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER4_EXEC (28--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
   memset_full_contract mf ea el ev /\
   memcpy_safety_contract mc ea el ev /\
   randombytes_safety_contract mr ea el ev
   ==> exists f_events.
        forall e ct ss pk (ek:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 1568 /\
          (!i j. i < 4 /\ j < 4
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 23200),23200) /\
          nonoverlapping (pk,1568) (word pc,libmlkem_size) /\
          PAIRWISE nonoverlapping
           [(ct,1568); (ss,32); (word_sub stackpointer (word 23200),23200)] /\
          ALLPAIRS nonoverlapping
           [(ct,1568); (ss,32); (word_sub stackpointer (word 23200),23200)]
           [(pk,1568); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem1024_enc) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ct; ss; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ct ss pk guard mf mc mr pc
                              (word_sub stackpointer (word 23200))
                              returnaddress ek (C_RETURN s) /\
                       memaccess_inbounds e2
                        [pk,1568; ct,1568; ss,32;
                         word_sub stackpointer (word 23200),23200;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; word(pc + got_randombytes),8;
                         ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlk_poly_invntt_tomont_c_consts),32]
                        [ct,1568; ss,32;
                         word_sub stackpointer (word 23200),23200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ct,1568); memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 23200),23200)])`;;

let MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
