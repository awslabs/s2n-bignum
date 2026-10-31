(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of ML-KEM-512 (FIPS 203 Algorithm 16, which is         *)
(* Algorithm 19 with its random seeds as arguments). This is the code for    *)
(* mlkem512_keypair_derand from mlkem-native's portable C implementation     *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It generates    *)
(* the K-PKE keys from the first 32 bytes d of its argument coins with       *)
(* mlkem512_indcpa_keypair_derand, and writes the decapsulation key as the   *)
(* K-PKE decryption key followed by the encapsulation key, copied with       *)
(* memcpy, its hash H by mlkem_sha3_256 and the last 32 bytes z of coins. If *)
(* mlkem512_indcpa_keypair_derand returned an error, which it never does,    *)
(* the function would zero the keys with memset. It is verified in the whole *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x3c90, using the theorems for mlkem512_indcpa_keypair_derand and         *)
(* mlkem_sha3_256 in the image and the contract for memcpy.                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_indcpa_keypair_derand_k2_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_sha3_256_gcc12_O2.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    3c90: stp     x19, x20, [sp, #-48]!
    3c94: mov     x19, x1
    3c98: stp     x21, x22, [sp, #16]
    3c9c: mov     x22, x2
    3ca0: mov     x21, x0
    3ca4: str     x30, [sp, #32]
    3ca8: bl      3494 <mlkem512_indcpa_keypair_derand>
    3cac: mov     x2, #0x320
    3cb0: mov     w20, w0
    3cb4: cbnz    w0, 3cf4 <mlkem512_keypair_derand+0x64>
    3cb8: mov     x1, x21
    3cbc: add     x0, x19, #0x300
    3cc0: bl      810 <memcpy@plt>
    3cc4: mov     x1, x21
    3cc8: add     x0, x19, #0x620
    3ccc: mov     x2, #0x320
    3cd0: bl      2650 <mlkem_sha3_256>
    3cd4: ldp     q0, q1, [x22, #32]
    3cd8: add     x19, x19, #0x640
    3cdc: mov     w0, w20
    3ce0: stp     q0, q1, [x19]
    3ce4: ldp     x21, x22, [sp, #16]
    3ce8: ldr     x30, [sp, #32]
    3cec: ldp     x19, x20, [sp], #48
    3cf0: ret
    3cf4: mov     x0, x21
    3cf8: mov     w1, #0x0
    3cfc: bl      840 <memset@plt>
    3d00: mov     x2, #0x660
    3d04: mov     x0, x19
    3d08: mov     w1, #0x0
    3d0c: bl      840 <memset@plt>
    3d10: ldp     x21, x22, [sp, #16]
    3d14: mov     w0, w20
    3d18: ldr     x30, [sp, #32]
    3d1c: ldp     x19, x20, [sp], #48
    3d20: ret
 ***)

let MLKEM_NATIVE_KEYPAIR_DERAND_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x810,0x820; 0x3c90,0x3d24];;

let KK2_EXEC = MLKEM_NATIVE_KEYPAIR_DERAND_K2_GCC12_O2_EXEC;;

let KPKE_KEYGEN_LENGTHS_512 = prove
 (`!d. LENGTH(FST(kpke_keygen mlkem512 d)) = 800 /\
       LENGTH(SND(kpke_keygen mlkem512 d)) = 768`,
  REWRITE_TAC[mlkem512; KPKE_KEYGEN_LENGTHS] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The callees, the contract for memcpy, which the function calls through    *)
(* its PLT stub, and the copy of z into the decapsulation key.               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INDCPA_KEYPAIR_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KK2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KK2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let KK2_MEMCPY_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memcpy_contract mc ea el ev`) (concl th)
    then LABEL_TAC "H_MEMCPY" (REWRITE_RULE[memcpy_contract] th)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64(word(pc + 131024))) s = f:int64`)
         (concl th)
    then ASSUME_TAC(REWRITE_RULE[WORD_ADD] th) else NO_TAC);;

let KK2_Z_HALVES_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP KEM_BYTES128_HALVES o check
   (can (term_match []
     `read (memory :> bytes(word_add coins (word 32),32)) s = n`) o
    concl)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KK2_Z_TAC s =
  MP_TAC(SPECL [`word_add sk (word 1600):int64`; `num_of_bytelist z`;
                mk_var(s,`:armstate`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `z:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KK2_FINAL_TAC =
  REWRITE_TAC[mlkem512; MLKEM_KEYGEN_PAIR] THEN REWRITE_TAC[GSYM mlkem512] THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_KEYGEN_LENGTHS_512;
              mlkem_h; LENGTH_SHA3_256] THEN
  REWRITE_TAC[ARITH_RULE `1632 = 768 + 864`; ARITH_RULE `864 = 800 + 64`;
              ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* former for the callees). The seed is d followed by z, 32 bytes each, at   *)
(* coins, and the encapsulation key of 800 bytes at pk and the decapsulation *)
(* key of 1632 bytes at sk are those of mlkem_keygen mlkem512 d z in         *)
(* common/fips203.ml. The theorem assumes that SampleNTT terminates for each *)
(* entry of the matrix and that the stack does not contain address 0, as for *)
(* mlkem512_indcpa_keypair_derand. The stack is the 48 bytes of the function *)
(* and the 9488 used by mlkem512_indcpa_keypair_derand below them.           *)
(* ------------------------------------------------------------------------- *)

let KK2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `z:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 9536 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 9536):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  MP_TAC(SPEC `d:byte list` KPKE_KEYGEN_LENGTHS_512) THEN STRIP_TAC;;

let KK2_MAIN_TAC =
  ENSURES_INIT_TAC "s0" THEN KK2_Z_HALVES_TAC THEN KK2_MEMCPY_TAC THEN
  ARM_STEPS_TAC KK2_EXEC (1--7) THEN
  LOCAL_INDCPA_KEYPAIR_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 8 THEN
  ARM_STEPS_TAC KK2_EXEC (9--14) THEN
  LIBC_PLT_TAC KK2_EXEC 14 THEN
  LIBC_CALL_TAC "H_MEMCPY" KK2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `num_of_bytelist(FST(kpke_keygen mlkem512 d))`; `read X30 s`] 19 THEN
  ARM_STEPS_TAC KK2_EXEC (20--23) THEN
  LOCAL_SHA3_256_TAC
   [`read X0 s`; `read X1 s`; `FST(kpke_keygen mlkem512 d)`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  ARM_STEPS_TAC KK2_EXEC (25--32) THEN KK2_Z_TAC "s32" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KK2_FINAL_TAC;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!pk sk coins (d:byte list) (z:byte list) guard mf mc ea el ev
    pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\ LENGTH z = 32 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 2])))
                            [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 9536),9536) /\
        PAIRWISE nonoverlapping
         [(pk,800); (sk,1632); (word_sub stackpointer (word 9536),9536)] /\
        ALLPAIRS nonoverlapping
         [(pk,800); (sk,1632); (word_sub stackpointer (word 9536),9536)]
         [(coins,64); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x3c90) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk; sk; coins] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                  read (memory :> bytes(word_add coins (word 32),32)) s =
                  num_of_bytelist z)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(pk,800)) s =
                  num_of_bytelist(FST(mlkem_keygen mlkem512 d z)) /\
                  read (memory :> bytes(sk,1632)) s =
                  num_of_bytelist(SND(mlkem_keygen mlkem512 d z)) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,800); memory :> bytes(sk,1632);
                memory :> bytes(word_sub stackpointer (word 9536),9536)])`,
  KK2_INTRO_TAC THEN KK2_MAIN_TAC);;
