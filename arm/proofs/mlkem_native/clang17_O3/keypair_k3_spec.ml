(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of ML-KEM-768 (FIPS 203 Algorithm 19). This is the   *)
(* code for mlkem768_keypair from mlkem-native's portable C implementation *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md). It gets 64  *)
(* random bytes with randombytes into a buffer on the stack, and returns   *)
(* -3 if that fails, and otherwise generates the keys from them as         *)
(* mlkem768_keypair_derand does: the compiler has inlined that function,   *)
(* so this function calls mlkem768_indcpa_keypair_derand, memcpy and       *)
(* mlkem_sha3_256 itself. In both cases it zeroes the buffer. The          *)
(* statements are those of the gcc 12 -O2 image, except for the stack: the *)
(* function saves its registers, aligns the buffer to 32 bytes below them, *)
(* and the frame also includes the 13680 bytes of                           *)
(* mlkem768_indcpa_keypair_derand below the buffer. It is verified in the  *)
(* whole image (see libmlkem.ml), using the theorems for                   *)
(* mlkem768_indcpa_keypair_derand and mlkem_sha3_256 in the image and the  *)
(* contracts for memcpy and randombytes.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/indcpa_keypair_derand_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/sha3_256_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keypair_derand_k3_spec.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    mlkem768_keypair:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: str     x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0x50
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: mov     x19, x1
      +0x20: mov     x21, x0
      +0x24: mov     x0, sp
      +0x28: mov     w1, #0x40
      +0x2c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x30: ldr     x8, [x8]
      +0x34: str     x8, [sp, #72]
      +0x38: bl      <randombytes@plt>
      +0x3c: cbz     w0, <mlkem768_keypair+0x48>
      +0x40: mov     w20, #0xfffffffd
      +0x44: b       <mlkem768_keypair+0xb0>
      +0x48: mov     x2, sp
      +0x4c: mov     x0, x21
      +0x50: mov     x1, x19
      +0x54: bl      <mlkem768_indcpa_keypair_derand>
      +0x58: mov     w20, w0
      +0x5c: cbz     w0, <mlkem768_keypair+0x84>
      +0x60: mov     x0, x21
      +0x64: mov     w1, wzr
      +0x68: mov     w2, #0x320
      +0x6c: bl      <memset@plt>
      +0x70: mov     x0, x19
      +0x74: mov     w1, wzr
      +0x78: mov     w2, #0x660
      +0x7c: bl      <memset@plt>
      +0x80: b       <mlkem768_keypair+0xb0>
      +0x84: add     x0, x19, #0x300
      +0x88: mov     x1, x21
      +0x8c: mov     w2, #0x320
      +0x90: bl      <memcpy@plt>
      +0x94: add     x0, x19, #0x620
      +0x98: mov     x1, x21
      +0x9c: mov     w2, #0x320
      +0xa0: bl      <mlkem_sha3_256>
      +0xa4: ldp     q0, q1, [sp, #32]
      +0xa8: str     q0, [x19, #2368]
      +0xac: str     q1, [x19, #2384]
      +0xb0: movi    v0.2d, #0x0
      +0xb4: mov     x8, sp
      +0xb8: stp     q0, q0, [sp]
      +0xbc: stp     q0, q0, [sp, #32]
      +0xc0: adrp    x8, <page>
      +0xc4: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0xc8: ldr     x9, [sp, #72]
      +0xcc: ldr     x8, [x8]
      +0xd0: cmp     x8, x9
      +0xd4: b.ne    <mlkem768_keypair+0xf0>
      +0xd8: mov     w0, w20
      +0xdc: mov     sp, x29
      +0xe0: ldp     x20, x19, [sp, #32]
      +0xe4: ldr     x21, [sp, #16]
      +0xe8: ldp     x29, x30, [sp], #48
      +0xec: ret
      +0xf0: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "plt_randombytes"; layout_range "plt_memcpy";
    layout_range "mlkem768_keypair"];;

let KR3_EXEC = MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The address of the buffer, which is aligned to 32 bytes within the stack  *)
(* frame, the callee, and the seeds as the random bytes.                     *)
(* ------------------------------------------------------------------------- *)

let KR3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 13696)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 13696 else 13680))`;;

let KR3_BUFFER_ADDRESS = assume_spec KR3_BUFFER_ADDRESS_STMT;;

let KR3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KR3_BUFFER_ADDRESS))
    else NO_TAC);;

let LOCAL_INDCPA_KEYPAIR_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KR3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KR3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHA3_256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let KR3_D = `bytelist_of_num 32 (rnd MOD 2 EXP 256)`;;

let KR3_Z = `bytelist_of_num 32 (rnd DIV 2 EXP 256)`;;

let KR3_PK = subst [KR3_D,`d:byte list`] `FST(kpke_keygen mlkem768 d)`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset, memcpy and          *)
(* randombytes. Either randombytes succeeds and the function returns 0, and  *)
(* then the encapsulation key of 1184 bytes at pk and the decapsulation key   *)
(* of 2400 bytes at sk are those of mlkem_keygen_internal mlkem768 d z in    *)
(* common/fips203/fips203.ml for some d and z of 32 bytes (the random        *)
(* bytes), or it fails and the function returns -3. The theorem assumes that *)
(* SampleNTT terminates for each entry of the matrix for any seed d and that *)
(* the stack does not contain address 0. The stack is the 144 bytes of the   *)
(* function and the 13680 used by mlkem768_indcpa_keypair_derand below them.  *)
(* The proof is by cases on whether the stack pointer is a multiple of 32,  *)
(* which gives the address b of the buffer, and on whether randombytes       *)
(* succeeds.                                                                 *)
(* ------------------------------------------------------------------------- *)

let KR3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `guard:int64`; `mf:int64`; `mc:int64`;
    `mr:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13824 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13824):int64)` THEN
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
     (parse_term("X"^string_of_int n))) (19--29) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `randombytes_contract mr ea el ev`) (concl th)
    then LABEL_TAC "H_RANDOMBYTES" (REWRITE_RULE[randombytes_contract] th)
    else NO_TAC);;

let KR3_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  KK3_MEMCPY_TAC THEN
  ARM_STEPS_TAC KR3_EXEC (1--6) THEN KR3_BUFFER_TAC THEN
  ARM_STEPS_TAC KR3_EXEC (7--7) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KR3_EXEC (8--15) THEN
  LIBC_PLT_TAC KR3_EXEC 15 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KR3_EXEC
   [`read X0 s`; `read X1 s`; `read X30 s`] 20 THEN
  ABBREV_TAC `rv = read X0 s20` THEN
  ABBREV_TAC (mk_eq(`rnd:num`,
   subst [KEM_SP b,`a:int64`] `read (memory :> bytes(a,64)) s20`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KR3_EXEC (21--25) THEN KEM_GOT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                ONCE_DEPTH_CONV NUM_ADD_CONV) o
      MATCH_MP KEM_RANDOM_SPLIT o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_D),`32`),
                          mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_Z),`32`)))
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC KR3_D o check (is_forall o concl)) THEN
    REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN DISCH_TAC THEN
    KEM_HALVES_TAC (KEM_SP (b + 32)) THEN
    MP_TAC(SPEC KR3_D KPKE_KEYGEN_LENGTHS_768) THEN STRIP_TAC THEN
    LOCAL_INDCPA_KEYPAIR_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; KR3_D; `guard:int64`;
      `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
      `read SP s`; `read X30 s`] 26 THEN
    ARM_STEPS_TAC KR3_EXEC (27--32) THEN
    LIBC_PLT_TAC KR3_EXEC 32 THEN
    LIBC_CALL_TAC "H_MEMCPY" KR3_EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`;
      mk_comb(`num_of_bytelist`,KR3_PK); `read X30 s`] 37 THEN
    ARM_STEPS_TAC KR3_EXEC (38--41) THEN
    LOCAL_SHA3_256_TAC
     [`read X0 s`; `read X1 s`; KR3_PK;
      `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 42 THEN
    ARM_STEPS_TAC KR3_EXEC (43--50) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR3_EXEC (51--61) THEN
    KEM_JOIN_TAC `word_add sk (word 2368):int64` KR3_Z "s61" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [KR3_D; KR3_Z] THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN KK3_FINAL_TAC;
    ARM_STEPS_TAC KR3_EXEC (21--28) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR3_EXEC (29--39) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk sk guard mf mc mr ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        randombytes_contract mr ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        (!d. LENGTH d = 32
             ==> !i j. i < 3 /\ j < 3
                       ==> mlkem_samplentt_terminates
                            (APPEND (FST(mlkem_g(APPEND d [word 3])))
                                    [word j; word i])) /\
        PAIRWISE nonoverlapping
         [(pk,1184); (sk,2400); (word_sub stackpointer (word 13824),13824)] /\
        ALLPAIRS nonoverlapping
         [(pk,1184); (sk,2400); (word_sub stackpointer (word 13824),13824)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (word(pc + got_randombytes),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem768_keypair) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  (C_RETURN s = word 0 /\
                   (?d z. LENGTH d = 32 /\ LENGTH z = 32 /\
                          read (memory :> bytes(pk,1184)) s =
                          num_of_bytelist(FST(mlkem_keygen_internal mlkem768 d z)) /\
                          read (memory :> bytes(sk,2400)) s =
                          num_of_bytelist(SND(mlkem_keygen_internal mlkem768 d z))) \/
                   C_RETURN s = word 0xfffffffd))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
                memory :> bytes(word_sub stackpointer (word 13824),13824)])`;;

let MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset and the safety contracts for memcpy and randombytes. The events    *)
(* depend only on the addresses, on whether randombytes fails and, if it     *)
(* does not, on rho, which is the end of the public key by the theorem for   *)
(* mlkem768_keypair_derand. So they are given in terms of the result and of  *)
(* the last 32 bytes of the public key, by cases on whether the stack        *)
(* pointer is a multiple of 32 and on whether the result is 0.               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KR_SAFE_TEMPLATE =
 `\(pk:int64) (sk:int64) (guard:int64) (mf:int64) (mc:int64) (mr:int64)
   (pc:num) (sp:int64) (ra:int64) (r:int64) (n:num).
   if aligned 32 sp
   then (if r = word 0
         then f_ev_a1 pk sk guard mf mc mr pc sp ra (bytelist_of_num 32 n)
         else f_ev_a0 pk sk guard mf mc mr pc sp ra)
   else (if r = word 0
         then f_ev_u1 pk sk guard mf mc mr pc sp ra (bytelist_of_num 32 n)
         else f_ev_u0 pk sk guard mf mc mr pc sp ra)
   :(uarch_event)list`;;

let KR_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `guard:int64`; `mf:int64`;
   `mc:int64`; `mr:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `d:byte list`];;

let KEM_BYTELIST_32_STMT =
  `!l:byte list. LENGTH l = 32 ==> bytelist_of_num 32 (num_of_bytelist l) = l`;;

let KEM_BYTELIST_32 = assume_spec KEM_BYTELIST_32_STMT;;

let KR3_SAFE_INTRO_TAC =
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
         MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
         (CONJ th1 th2)) "H_INDCPA" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memcpy_safety_contract] th2) "H_MEMCPY")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_256_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SHA3_256" THEN
  CONCRETIZE_F_EVENTS_TAC KR_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13824):int64)` THEN
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
     (parse_term("X"^string_of_int n))) (19--29);;

let KR3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,KR3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KR_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KR3_SAFE_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64(word(pc + 196560))) s = f:int64`)
         (concl th)
    then ASSUME_TAC(REWRITE_RULE[WORD_ADD] th) else NO_TAC) THEN
  ARM_STEPS_TAC KR3_EXEC (1--6) THEN KR3_BUFFER_TAC THEN
  ARM_STEPS_TAC KR3_EXEC (7--7) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KR3_EXEC (8--15) THEN
  LIBC_PLT_TAC KR3_EXEC 15 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" KR3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref KR_SAFE_ALLOWED) 20 THEN
  ABBREV_TAC `rv = read X0 s20` THEN
  ABBREV_TAC (mk_eq(`rnd:num`,
   subst [KEM_SP b,`a:int64`] `read (memory :> bytes(a,64)) s20`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KR3_EXEC (21--25) THEN KEM_GOT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                ONCE_DEPTH_CONV NUM_ADD_CONV) o
      MATCH_MP KEM_RANDOM_SPLIT o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    FIRST_ASSUM(MP_TAC o SPEC KR3_D o check (is_forall o concl)) THEN
    REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN DISCH_TAC THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_D),`32`))
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    ABBREV_TAC(mk_eq(`d:byte list`,KR3_D)) THEN
    KR3_SAFE_CALL_TAC "H_INDCPA"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `d:byte list`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
     26 THEN
    ARM_STEPS_TAC KR3_EXEC (27--32) THEN
    LIBC_PLT_TAC KR3_EXEC 32 THEN
    LIBC_SAFE_CALL_TAC "H_MEMCPY" KR3_EXEC
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X30 s`] (ref KR_SAFE_ALLOWED) 37 THEN
    ARM_STEPS_TAC KR3_EXEC (38--41) THEN
    KR3_SAFE_CALL_TAC "H_SHA3_256"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `1184`;
      `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 42 THEN
    ARM_STEPS_TAC KR3_EXEC (43--50) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR3_EXEC (51--61) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    SIMP_TAC[KEM_BYTELIST_32; LENGTH_MLKEM_G] THEN
    REWRITE_TAC[APPEND_NIL] THEN
    ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 3]))` THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ARM_STEPS_TAC KR3_EXEC (21--28) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR3_EXEC (29--39) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
   memset_full_contract mf ea el ev /\
   memcpy_safety_contract mc ea el ev /\
   randombytes_safety_contract mr ea el ev
   ==> exists f_events.
        forall e pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          (!d. LENGTH d = 32
               ==> !i j. i < 3 /\ j < 3
                         ==> mlkem_samplentt_terminates
                              (APPEND (FST(mlkem_g(APPEND d [word 3])))
                                      [word j; word i])) /\
          PAIRWISE nonoverlapping
           [(pk,1184); (sk,2400); (word_sub stackpointer (word 13824),13824)] /\
          ALLPAIRS nonoverlapping
           [(pk,1184); (sk,2400); (word_sub stackpointer (word 13824),13824)]
           [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
            (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem768_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk guard mf mc mr pc
                              (word_sub stackpointer (word 13824))
                              returnaddress (C_RETURN s)
                              (read (memory :> bytes(word_add pk (word 1152),
                                                     32)) s) /\
                       memaccess_inbounds e2
                        [pk,1184; sk,2400;
                         word_sub stackpointer (word 13824),13824;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; word(pc + got_randombytes),8;
                         ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_ntt_consts),
                         mlkem_poly_ntt_consts_size;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size]
                        [pk,1184; sk,2400;
                         word_sub stackpointer (word 13824),13824]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
                  memory :> bytes(word_sub stackpointer (word 13824),13824)])`;;

let MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KEYPAIR_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
