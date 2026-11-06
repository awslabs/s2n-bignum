(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a Keccak state, with the padding. This is  *)
(* the code for the static function mlk_keccak_absorb_once from mlkem-       *)
(* native's portable C implementation compiled by gcc 12 with -O2 as one    *)
(* translation unit (see mlkem_native/README.md), with the specifications    *)
(* that it has in the separately compiled gcc12_O2 build. It zeroes the     *)
(* state, XORs in each whole block of r bytes of the message and permutes   *)
(* the state, and then XORs in the rest of the message and the padding, but  *)
(* does not permute the state again. The calls of mlkem_keccakf1600_xor_    *)
(* bytes are inlined as loops and single-byte XORs, which are proved here   *)
(* as lemmas (one for the loop that XORs in a block, one for the loop that  *)
(* XORs in the rest of the message, and one for each of the two bytes of     *)
(* padding), and the permutation is the call of mlk_keccakf1600_permute_c.  *)
(* The lemmas and the function are proved with the events of the constant-   *)
(* time and memory safety proofs together with the correctness statement     *)
(* (the theorem ..._FULL), and the correctness theorem (..._CORRECT) and the *)
(* safety theorem (..._SAFE) are derived from it. There are differences from *)
(* the gcc12_O2 specifications: the message must be nonempty (mlen > 0),     *)
(* since a message shorter than a block goes straight to the loop that XORs  *)
(* in the rest of the message, which does not test for mlen = 0, and r is    *)
(* not zero; the padding byte p is below 128 in all three, which the SAFE    *)
(* theorem needs to be derived from FULL (the callers use 6 and 0x1f); and   *)
(* the frame is that of the ABI, which holds since no caller keeps a         *)
(* caller-saved register across the call. It is verified in the whole image  *)
(* (see libmlkem.ml).                                                        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_permute_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_xor_bytes_proof.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The code in the image:

    mlk_keccak_absorb_once:
     +0x0  movi    v0.4s, #0x0
     +0x4  stp     x19, x20, [sp, #-64]!
     +0x8  mov     x20, x0
     +0xc  stp     x21, x22, [sp, #16]
    +0x10  mov     w22, w1
    +0x14  mov     x21, x2
    +0x18  stp     x23, x24, [sp, #32]
    +0x1c  mov     x24, x22
    +0x20  mov     x23, x3
    +0x24  stp     x25, x30, [sp, #48]
    +0x28  and     w25, w4, #0xff
    +0x2c  stp     q0, q0, [x0]
    +0x30  stp     q0, q0, [x0, #32]
    +0x34  stp     q0, q0, [x0, #64]
    +0x38  stp     q0, q0, [x0, #96]
    +0x3c  stp     q0, q0, [x0, #128]
    +0x40  stp     q0, q0, [x0, #160]
    +0x44  str     xzr, [x0, #192]
    +0x48  cmp     x3, x22
    +0x4c  b.cc    join2
  loop1:
    +0x50  mov     x19, #0x0                  <--+ |
    +0x54  nop                                   | |
  // inlined: keccakf1600_xor_bytes              | |
  loop2: in_keccakf1600_xor_bytes_1:             | |
    +0x58  ldrb    w4, [x20, x19]             <+ | |
    +0x5c  ldrb    w0, [x21, x19]              | | |
    +0x60  eor     w4, w4, w0                  | | |
    +0x64  strb    w4, [x20, x19]              | | |
    +0x68  add     x19, x19, #0x1              | | |
  loop2_test:                                  | | |
    +0x6c  cmp     x19, x22                    | | |
  loop2_back:                                  | | |
    +0x70  b.ne    loop2                      -+ | |
  // inlined: keccakf1600_permute                | |
  loop2_exit: in_keccakf1600_permute:            | |
  in_keccakf1600_permute_part1:                  | |
  in_keccakf1600_xor_bytes_1_end:                | |
    +0x74  mov     x0, x20                       | |
  // inlined: (not inlined)                      | |
  in_keccakf1600_permute_part1_end:              | |
    +0x78  sub     x23, x23, x19                 | |
  // inlined: keccakf1600_permute                | |
  in_keccakf1600_permute_part2:                  | |
    +0x7c  bl      mlk_keccakf1600_permute_c     | |
  // inlined: (not inlined)                      | |
  after_mlk_keccakf1600_permute_c:               | |
  in_keccakf1600_permute_end:                    | |
  in_keccakf1600_permute_part2_end:              | |
    +0x80  add     x21, x21, x19                 | |
  loop1_test:                                    | |
    +0x84  cmp     x23, x19                      | |
  loop1_back:                                    | |
    +0x88  b.cs    loop1                      ---+ |
  loop1_exit:
    +0x8c  cbnz    x23, join2                 -+
  // inlined: keccakf1600_xor_bytes            |
  join1: in_keccakf1600_xor_bytes_2:           |
  in_keccakf1600_xor_bytes_2_part1:            |
    +0x90  ldrb    w0, [x20, x23]             <--+ |
  // inlined: (not inlined)                    | | |
  in_keccakf1600_xor_bytes_2_part1_end:        | | |
    +0x94  sub     w24, w24, #0x1              | | |
  // inlined: keccakf1600_xor_bytes            | | |
  in_keccakf1600_xor_bytes_2_part2:            | | |
    +0x98  eor     w25, w25, w0                | | |
    +0x9c  strb    w25, [x20, x23]             | | |
  in_keccakf1600_xor_bytes_2_end:              | | |
  in_keccakf1600_xor_bytes_2_part2_end:        | | |
  in_keccakf1600_xor_bytes_3:                  | | |
    +0xa0  ldrb    w0, [x20, w24, uxtw]        | | |
    +0xa4  eor     w0, w0, #0xffffff80         | | |
    +0xa8  strb    w0, [x20, w24, uxtw]        | | |
  // inlined: (not inlined)                    | | |
  in_keccakf1600_xor_bytes_3_end:              | | |
    +0xac  ldp     x21, x22, [sp, #16]         | | |
    +0xb0  ldp     x23, x24, [sp, #32]         | | |
    +0xb4  ldp     x25, x30, [sp, #48]         | | |
    +0xb8  ldp     x19, x20, [sp], #64         | | |
  ret:                                         | | |
    +0xbc  ret                                 | | |
  join2:                                       | | |
    +0xc0  mov     w3, w23
    +0xc4  mov     x0, #0x0
  // inlined: keccakf1600_xor_bytes
  loop3: in_keccakf1600_xor_bytes_4:
    +0xc8  ldrb    w1, [x20, x0]              <+ |
    +0xcc  ldrb    w2, [x21, x0]               | |
    +0xd0  eor     w1, w1, w2                  | |
    +0xd4  strb    w1, [x20, x0]               | |
    +0xd8  add     x0, x0, #0x1                | |
  loop3_test:                                  | |
    +0xdc  cmp     x3, x0                      | |
  loop3_back:                                  | |
    +0xe0  b.ne    loop3                      -+ |
  loop3_exit:
    +0xe4  b       join1
 ***)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_keccak_absorb_once"];;

let ABS_EXEC = MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_EXEC;;


(* ------------------------------------------------------------------------- *)
(* The loop that XORs in a block (mlk_keccak_absorb_once_loop2) and the loop *)
(* that XORs in the rest of the message (from join2 to join1) are the same   *)
(* as the loop of mlkem_keccakf1600_xor_bytes, with the bound in a register  *)
(* (X22, or X3 set from X23) and the test of the loop in different order.    *)
(* They are proved by the generator xorF_prove of keccakf1600_xor_bytes.ml   *)
(* for any offset, and then specialized to the offset 0 that they have here. *)
(* ------------------------------------------------------------------------- *)

(*** The loop that XORs in a block, from its head to its exit ***)

let ABS_LA_STMT = xor_full_stmt
  "mlk_keccak_absorb_once_loop2" "mlk_keccak_absorb_once_loop2_exit" "a"
  "read X20 s = word_add a (word off) /\\ read X19 s = word 0 /\\
   read X21 s = d /\\ read X22 s = word len"
  "read X19 s = word len"
  "X0; X4; X19";;

let ABS_LA = xorF_prove ABS_EXEC ABS_LA_STMT
  "mlk_keccak_absorb_once_loop2" "mlk_keccak_absorb_once_loop2_exit"
  (fun i -> "read X20 s = word_add a (word off) /\\ read X19 s = word "^i^" /\\
             read X21 s = d /\\ read X22 s = word len") 0 0 true;;

(*** The loop that XORs in the rest of the message, from join2 to join1 ***)

let ABS_LC_STMT = xor_full_stmt
  "mlk_keccak_absorb_once_join2" "mlk_keccak_absorb_once_join1" "a"
  "read X20 s = word_add a (word off) /\\ read X21 s = d /\\
   read X23 s = word len"
  "read X0 s = word len /\\ read X3 s = word len"
  "X0; X1; X2; X3";;

let ABS_LC = xorF_prove ABS_EXEC ABS_LC_STMT
  "mlk_keccak_absorb_once_loop3" "mlk_keccak_absorb_once_loop3_exit"
  (fun i -> "read X20 s = word_add a (word off) /\\ read X0 s = word "^i^" /\\
             read X21 s = d /\\ read X3 s = word len") 2 1 false;;

let ABS_LA0 = OFF0_PROVE ABS_LA;;
let ABS_LC0 = OFF0_PROVE ABS_LC;;

(* ------------------------------------------------------------------------- *)
(* The padding: byte t of the state XORed with p, then byte r - 1 with 0x80. *)
(* ------------------------------------------------------------------------- *)

let ABS_T1_STMT = `exists f_events.
     forall e st t r p (A:1600 word) pc.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        t < r /\ r <= 200 /\ p < 128 /\
        nonoverlapping (st,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once_join1) /\
                  read X20 s = st /\ read X23 s = word t /\
                  read X24 s = word r /\ read X25 s = word p /\
                  read (memory :> wbytes st) s = A /\
                  read events s = e)
             (\s. read PC s =
                  word (pc + mlk_keccak_absorb_once_in_keccakf1600_xor_bytes_3) /\
                  read X24 s = word (r - 1) /\
                  read (memory :> wbytes st) s =
                  word_xor A (word(2 EXP (8 * t) * p)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events st t pc /\
                     memaccess_inbounds e2 [st,200] [st,200]))
             (MAYCHANGE [PC; X0; X24; X25] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(st,200)])`;;

let ABS_T1 = prove(ABS_T1_STMT,
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `st:int64`; `t:num`; `r:num`; `p:num`; `A:1600 word`;
                       `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; READ_MEMORY_WBYTES_1600;
              fst ABS_EXEC] THEN
  STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP XOR_BYTES_OF_STATE) THEN
  SUBGOAL_THEN `t < 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      ASSUME_TAC(MP (SPEC `t:num` th) (ASSUME `t < 200`)) THEN
      ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `t:num` th)
    else failwith "XOR_BYTES_RESTRICT_RULE") THEN
  ARM_STEPS_TAC ABS_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`st:int64`; `A:1600 word`; `t:num`; `1`; `p:num`;
                 `s4:armstate`] XOR_BYTES_FINAL2) THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `p:num`; `t:num`; `0`; `j:num`]
                 XOR_BYTES_STEP) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; EXP; MOD_1; MULT_CLAUSES; WORD_XOR_0;
                DIV_1] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `p MOD 256 = p` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `j:num = t` THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC] THEN
  SUBGOAL_THEN `word p:byte = word_zx(word_zx(word p:int64):int32)`
   SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ZX_BYTE_SMALL THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> SPEC_TAC(`word p:int64`,`u:int64`) THEN
                 SPEC_TAC(`word_subword (A:1600 word) (8 * t,8):byte`,
                          `x:byte`)) THEN
  REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
  DISCHARGE_SAFETY_PROPERTY_TAC]);;

let ABS_T2_STMT = `exists f_events.
     forall e st k (A:1600 word) pc.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        k < 200 /\
        nonoverlapping (st,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s =
                  word (pc + mlk_keccak_absorb_once_in_keccakf1600_xor_bytes_3) /\
                  read X20 s = st /\ read X24 s = word k /\
                  read (memory :> wbytes st) s = A /\
                  read events s = e)
             (\s. read PC s =
                  word (pc + mlk_keccak_absorb_once_in_keccakf1600_xor_bytes_3_end) /\
                  read (memory :> wbytes st) s =
                  word_xor A (word(2 EXP (8 * k) * 128)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events st k pc /\
                     memaccess_inbounds e2 [st,200] [st,200]))
             (MAYCHANGE [PC; X0] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(st,200)])`;;

let ABS_T2 = prove(ABS_T2_STMT,
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `st:int64`; `k:num`; `A:1600 word`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; READ_MEMORY_WBYTES_1600;
              fst ABS_EXEC] THEN
  STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP XOR_BYTES_OF_STATE) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      ASSUME_TAC(MP (SPEC `k:num` th) (ASSUME `k < 200`)) THEN
      ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `k:num` th)
    else failwith "XOR_BYTES_RESTRICT_RULE") THEN
  MP_TAC(SPEC `k:num` VAL_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  ARM_STEPS_TAC ABS_EXEC (1--1) THEN ARGS_32_TAC [`k:num`] THEN
  ARM_STEPS_TAC ABS_EXEC (2--3) THEN ARGS_32_TAC [`k:num`] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`st:int64`; `A:1600 word`; `k:num`; `1`; `128`;
                 `s3:armstate`] XOR_BYTES_FINAL2) THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `128`; `k:num`; `0`; `j:num`]
                 XOR_BYTES_STEP) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; EXP; MOD_1; MULT_CLAUSES; WORD_XOR_0;
                DIV_1] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `j:num = k` THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC] THEN
  W(fun (_,w) -> SPEC_TAC(`word_subword (A:1600 word) (8 * k,8):byte`,
                          `x:byte`)) THEN
  GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
  DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The state after the padding, as in the specification.                     *)
(* ------------------------------------------------------------------------- *)

let LTMUL = prove
 (`!E Mr p. Mr < E /\ p < 128 ==> Mr + E * p < E * 128`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `E * (p + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_ASSOC] THEN ASM_ARITH_TAC;
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]);;

let TAIL_NUM = prove
 (`!K:1600 word Mr t r p.
        0 < r /\ t < r /\ r <= 200 /\ p < 128 /\ Mr < 2 EXP (8 * t)
        ==> word_xor (word_xor (word_xor K (word Mr)) (word(2 EXP (8 * t) * p)))
                     (word(2 EXP (8 * (r - 1)) * 128)) =
            word_xor K
             (word(Mr + 2 EXP (8 * t) *
                   (if t = r - 1 then p + 128
                    else p + 2 EXP (8 * (r - t - 1)) * 128)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!(K:1600 word) a b c.
                  word_xor (word_xor (word_xor K a) b) c =
                  word_xor K (word_xor (word_xor a b) c)`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(INST_TYPE [`:1600`,`:N`]
    (SPECL [`Mr:num`; `p:num`; `8 * t`] WORD_XOR_DISJOINT_ADD)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `t = r - 1` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[] THEN
    MP_TAC(INST_TYPE [`:1600`,`:N`]
      (SPECL [`Mr + 2 EXP (8 * t) * p`; `1`; `8 * t + 7`]
             WORD_XOR_DISJOINT_ADD)) THEN
    REWRITE_TAC[EXP_ADD; MULT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL [MATCH_MP_TAC LTMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    MP_TAC(INST_TYPE [`:1600`,`:N`]
      (SPECL [`Mr + 2 EXP (8 * t) * p`; `128`; `8 * (r - 1)`]
             WORD_XOR_DISJOINT_ADD)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `Mr + 2 EXP (8 * t) * p < 2 EXP (8 * t) * 128` MP_TAC THENL
       [MATCH_MP_TAC LTMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `2 EXP (8 * t) * 128 <= 2 EXP (8 * (r - 1))` MP_TAC THENL
       [SUBGOAL_THEN `2 EXP (8 * t) * 128 <= 2 EXP (8 * t) * 2 EXP 8`
          MP_TAC THENL
         [REWRITE_TAC[LE_MULT_LCANCEL] THEN CONV_TAC NUM_REDUCE_CONV;
          ALL_TAC] THEN
        REWRITE_TAC[GSYM EXP_ADD] THEN
        SUBGOAL_THEN `2 EXP (8 * t + 8) <= 2 EXP (8 * (r - 1))` MP_TAC THENL
         [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; ARITH_TAC];
        ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
       `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
       SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ARITH_TAC]]);;

let FINAL_EQ = prove
 (`!K:1600 word M mlen r p.
        0 < r /\ r <= 200 /\ p < 128 /\ M < 2 EXP (8 * mlen)
        ==> word_xor (word_xor (word_xor K (word (M DIV 2 EXP (8 * r * mlen DIV r))))
                      (word(2 EXP (8 * (mlen MOD r)) * p)))
                     (word(2 EXP (8 * (r - 1)) * 128)) =
            word_xor K
             (word(((M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen))
                    DIV 2 EXP (8 * r * mlen DIV r)) MOD 2 EXP (8 * r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `num_of_bytelist(keccak_pad r p mlen)`; `mlen:num`;
                `r:num`] KECCAK_BLOCK_LAST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC KECCAK_PAD_BOUND THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `p < 128 ==> p < 128`] THEN
  MP_TAC(SPECL [`K:1600 word`; `M DIV 2 EXP (8 * r * mlen DIV r)`;
                `mlen MOD r`; `r:num`; `p:num`] TAIL_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] MOD_LT_EQ) THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    SUBGOAL_THEN `r * mlen DIV r + mlen MOD r = mlen`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the arguments, the blocks and the byte of padding.           *)
(* ------------------------------------------------------------------------- *)

let ABSORB_BLOCK_BOUND = prove
 (`!mlen r i. 0 < r /\ i < mlen DIV r ==> r * i + r <= mlen`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC RAND_CONV [th])
    ASSUME_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + c`) THEN
  REWRITE_TAC[ARITH_RULE `r * i + r = (i + 1) * r`; LE_MULT_RCANCEL] THEN
  ASM_ARITH_TAC);;

let ABSORB_MOD_EQ = prove
 (`!mlen r. mlen - r * mlen DIV r = mlen MOD r`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] (CONJUNCT2 DIVISION_SIMP)) THEN
  ARITH_TAC);;

let ABSORB_LOOP_TEST = prove
 (`!mlen r i. 0 < r /\ r * i + r <= mlen
              ==> (r <= mlen - r * (i + 1) <=> i + 1 < mlen DIV r)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`; LE_RDIV_EQ;
               ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ASM_ARITH_TAC);;

(*** The byte p, zero-extended to 32 bits, masked with 0xff and extended ***)

let P8 = prove
 (`!p. p < 256
       ==> word_zx(word_and (word_zx(word p:int64):int32) (word 255)):int64 =
           word p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word p:int64 = word_zx(word p:byte)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8;
                DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `p < 256 ==> p < 18446744073709551616`];
    ALL_TAC] THEN
  SUBGOAL_THEN `word p:int64 = word_zx(word_zx(word p:byte):int32)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `p < 256 ==> p < 4294967296 /\ p < 18446744073709551616`];
    ALL_TAC] THEN
  W(fun (_,w) -> SPEC_TAC(`word p:byte`,`x:byte`)) THEN GEN_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(*** The state set to zero by the 13 stores, as bytes ***)

let KECCAK_ZERO_STATE_TAC =
  let zl = mk_list(replicate `word 0:int64` 25,`:int64`) in
  let zth = prove
   (mk_eq(`0`,mk_comb(`num_of_wordlist:int64 list->num`,zl)),
    REWRITE_TAC[num_of_wordlist; VAL_WORD_0] THEN ARITH_TAC) in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes128 a) s = word 0`) (concl th)
    then CONV_RULE(READ_MEMORY_SPLIT_CONV 1 THENC
                   ONCE_DEPTH_CONV WORD_REDUCE_CONV) th
    else th) THEN
  GEN_REWRITE_TAC RAND_CONV [zth] THEN
  CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN ASM_REWRITE_TAC[];;

(*** A part of a buffer cannot overlap what the whole buffer does not ***)

let NONOVERLAPPING_SUBRANGE = prove
 (`!(s:int64) sn m n k l.
        nonoverlapping (s,sn) (m,n) /\ k + l <= n
        ==> nonoverlapping (s,sn) (word_add m (word k),l)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`s:int64`; `sn:num`; `m:int64`; `n:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  REWRITE_TAC[CONTAINED] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST
   [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    EXISTS_TAC `k + i` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]]);;


(* ------------------------------------------------------------------------- *)
(* The proof of FULL, in parts. The parts are the entry to the end of the    *)
(* XORs (the label join1), and the padding to the return. The first part has *)
(* the case of a short message, which goes to join2 to XOR in the message    *)
(* (and then to join1), and that of a message of at least a block, where the *)
(* loop over the blocks is followed by the XOR of the rest of the message,   *)
(* if any. The events are given by a template with the parts, as in the      *)
(* gcc12_O2 proof, whose unknown parts are found by unification.             *)
(* ------------------------------------------------------------------------- *)

let ABS_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `r:num`; `m:int64`; `mlen:num`; `p:num`; `M:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25`;;

(*** What holds in the code after the XORs of the message, at join1 and
     join2, and at the end of the loop over the blocks ***)

let ABS_COMMON = "read X20 s = st /\\
        read X24 s = word r /\\ read X25 s = word p /\\
        read SP s = word_add stackpointer (word 192) /\\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s = x19_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 200))) s = x20_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s = x21_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 216))) s = x22_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s = x23_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s = x24_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 240))) s = x25_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 248))) s = returnaddress /\\
        read (memory :> bytes(m,mlen)) s = M";;

let ABS_MID_J1 = parse_term ("\\s. M < 2 EXP (8 * mlen) /\\
        read X23 s = word (mlen MOD r) /\\ " ^ ABS_COMMON ^ " /\\
        read (memory :> wbytes st) s =
        word_xor (keccak_absorb r P (mlen DIV r))
                 (word (M DIV 2 EXP (8 * r * mlen DIV r)))");;

let ABS_MID_J2 = parse_term ("\\s. M < 2 EXP (8 * mlen) /\\ ~(mlen MOD r = 0) /\\
        read X21 s = word_add m (word (r * (mlen DIV r))) /\\
        read X23 s = word (mlen MOD r) /\\ " ^ ABS_COMMON ^ " /\\
        read (memory :> wbytes st) s = keccak_absorb r P (mlen DIV r)");;

let ABS_MID_LX = parse_term ("\\s. M < 2 EXP (8 * mlen) /\\
        read X21 s = word_add m (word (r * (mlen DIV r))) /\\
        read X23 s = word (mlen MOD r) /\\ " ^ ABS_COMMON ^ " /\\
        read (memory :> wbytes st) s = keccak_absorb r P (mlen DIV r)");;

let ABS_INV = parse_term ("\\k s. M < 2 EXP (8 * mlen) /\\
        read X21 s = word_add m (word (r * k)) /\\
        read X22 s = word r /\\ read X23 s = word (mlen - r * k) /\\ " ^
        ABS_COMMON ^ " /\\
        read (memory :> wbytes st) s = keccak_absorb r P k");;


let ABS_TEMPLATE =
 `\(m:int64) (st:int64) (r:num) (mlen:num) (pc:num) (stackpointer:int64)
   (returnaddress:int64).
   APPEND (f_ev_pad m st r mlen pc stackpointer returnaddress)
    (if mlen < r
     then APPEND (f_ev_l3s m st r mlen pc stackpointer returnaddress)
                 (f_ev_short m st r mlen pc stackpointer returnaddress)
     else APPEND
           (APPEND
             (if mlen MOD r = 0 then []
              else f_ev_l3 m st r mlen pc stackpointer returnaddress)
             (if mlen MOD r = 0
              then f_ev_cb0 m st r mlen pc stackpointer returnaddress
              else f_ev_cb1 m st r mlen pc stackpointer returnaddress))
          (APPEND (f_ev_epil m st r mlen pc stackpointer returnaddress)
            (APPEND
              (ENUMERATEL (mlen DIV r)
                (\i. f_ev_loop m st r mlen pc stackpointer returnaddress i))
              (f_ev_prol m st r mlen pc stackpointer returnaddress))))
   :(uarch_event)list`;;

let ABS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC ABS_LA0 "H_LA" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC ABS_LC0 "H_LC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC ABS_T1 "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC ABS_T2 "H_T2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC ABS_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  ABS_SETUP_TAC;;


let has_wbytes th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = "wbytes"))
      (concl th);;

let ABS_VARS =
  [`pc:num`; `m:int64`; `st:int64`; `r:num`; `mlen:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

let ABS_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  ((MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL [
    REFL_TAC;
    SAFE_UNIFY_REFL_TAC allowed_vars_e pfx
  ]) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx));;

let ABS_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ABS_EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL
        [FULL_UNIFY_F_EVENTS_TAC ORELSE
         (REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
         ALL_TAC])
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let ABS_SUB name ilist vars n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,ABS_EXEC,0x0,
       mlkem_native_libmlkem_gcc12_O2_mono_mc,th)
      ilist n THENL
     [ABS_EXISTS_E2_TAC (ref vars); LABEL_TAC name th]);;

(*** The entry of a message shorter than a block: the state is zeroed and the
     code jumps to join2 ***)

let ABS_ENTRY_S_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes (m,mlen)) s0 = M` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  ARM_STEPS_TAC ABS_EXEC (1--19) THEN ARGS_32_TAC [`r:num`] THEN
  MP_TAC(SPEC `p:num` P8) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARM_STEPS_TAC ABS_EXEC (20--20) THEN
  SUBGOAL_THEN `val(word mlen:int64) = mlen /\ val(word r:int64) = r`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[keccak_absorb; READ_MEMORY_WBYTES_1600; VAL_WORD_0] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [KECCAK_ZERO_STATE_TAC; ABS_DISCHARGE_TAC];;

(*** From join2 to join1: the XOR of the rest of the message ***)

let ABS_J2_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `mlen = r * (mlen DIV r) + mlen MOD r /\ mlen MOD r < r`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mlen MOD r <= 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val (st:int64),200)
      (val (word_add (m:int64) (word (r * (mlen DIV r)))),mlen MOD r)`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`st:int64`; `200`; `m:int64`; `mlen:num`;
                   `r * (mlen DIV r)`; `mlen MOD r`] NONOVERLAPPING_SUBRANGE) THEN
    REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC];
                    DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val (st:int64),200) (pc,libmlkem_size)`
   ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * (mlen DIV r)`;
                `mlen MOD r`; `s0:armstate`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC];
                  DISCH_TAC] THEN
  ABS_SUB "H_LC"
   [`e:(uarch_event)list`; `st:int64`;
    `word_add (m:int64) (word (r * (mlen DIV r)))`; `mlen MOD r`;
    `keccak_absorb r P (mlen DIV r)`;
    `(M DIV 2 EXP (8 * r * mlen DIV r)) MOD 2 EXP (8 * mlen MOD r)`;
    `pc:num`] ABS_VARS 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(M DIV 2 EXP (8 * r * mlen DIV r)) MOD 2 EXP (8 * mlen MOD r) =
    M DIV 2 EXP (8 * r * mlen DIV r)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    SUBGOAL_THEN `r * mlen DIV r + mlen MOD r = mlen`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABS_DISCHARGE_TAC;;

(*** The loop over the whole blocks: the entry ***)

let ABS_LINIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes (m,mlen)) s0 = M` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  ARM_STEPS_TAC ABS_EXEC (1--19) THEN ARGS_32_TAC [`r:num`] THEN
  MP_TAC(SPEC `p:num` P8) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARM_STEPS_TAC ABS_EXEC (20--20) THEN
  SUBGOAL_THEN `val(word mlen:int64) = mlen /\ val(word r:int64) = r`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
  REWRITE_TAC[keccak_absorb; READ_MEMORY_WBYTES_1600; VAL_WORD_0] THEN
  CONJ_TAC THENL [KECCAK_ZERO_STATE_TAC; ABS_DISCHARGE_TAC];;

(*** The body of the loop: XOR in a block, permute, and the test ***)

let ABS_LBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val (st:int64),200)
      (val (word_add (m:int64) (word (r * i))),r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`st:int64`; `200`; `m:int64`; `mlen:num`; `r * i`; `r:num`]
                  NONOVERLAPPING_SUBRANGE) THEN
    REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC];
                    DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val (st:int64),200) (pc,libmlkem_size)`
   ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * i`; `r:num`;
                `s0:armstate`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC];
                  DISCH_TAC] THEN
  ARM_STEPS_TAC ABS_EXEC (1--2) THEN
  ABS_SUB "H_LA"
   [`e:(uarch_event)list`; `st:int64`; `word_add (m:int64) (word (r * i))`;
    `r:num`; `keccak_absorb r P i`;
    `(M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`; `pc:num`]
   (ABS_VARS @ [`i:num`]) 3 THEN
  ARM_STEPS_TAC ABS_EXEC (4--6) THEN
  ABS_SUB "H_PERMUTE"
   [`e:(uarch_event)list`; `read X0 s`;
    `word_xor (keccak_absorb r P i)
              (word ((M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r))):1600 word`;
    `pc:num`; `read SP s`; `read X30 s`]
   (ABS_VARS @ [`i:num`]) 7 THEN
  ARM_STEPS_TAC ABS_EXEC (8--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_sub (word (mlen - r * i)) (word r):int64 =
    word (mlen - r * (i + 1))` ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `val(word r:int64) = r /\
    val(word (mlen - r * (i + 1)):int64) = mlen - r * (i + 1)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                                  FIRST_ASSUM ACCEPT_TAC];
                  DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
    REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `P:num`
      then SUBST1_TAC(SYM th) else failwith "") THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
    UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
    ABS_DISCHARGE_TAC];;

let ABS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r` `pc + mlk_keccak_absorb_once_loop1`
    `pc + mlk_keccak_absorb_once_loop1_exit` ABS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];
    ABS_LINIT_TAC;
    ABS_LBODY_TAC;
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    ABS_DISCHARGE_TAC];;

(*** After the loop: the rest of the message, if there is any ***)

let ABS_LX_TAC =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_CASES_TAC `mlen MOD r = 0` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[th; APPEND_NIL; APPEND]) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC ABS_EXEC (1--1) THEN
    SUBGOAL_THEN `r * (mlen DIV r) = mlen` ASSUME_TAC THENL
     [MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
      ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `M DIV 2 EXP (8 * r * mlen DIV r) = 0` ASSUME_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0; ASSUME `mlen MOD r = 0`]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0] THEN
    ABS_DISCHARGE_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th; APPEND_NIL; APPEND; GSYM APPEND_ASSOC]) THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_join2` ABS_MID_J2 THEN
  CONJ_TAC THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC ABS_EXEC (1--1) THEN
    SUBGOAL_THEN `val(word (mlen MOD r):int64) = mlen MOD r`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`] MOD_LT_EQ) THEN
      ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABS_DISCHARGE_TAC;
    ABS_J2_TAC];;

(*** The padding: byte t, then byte r - 1 ***)

let ABS_PART2_TAC =
  SUBGOAL_THEN `mlen MOD r < r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `0 < r ==> ~(r = 0)`]; ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ABS_SUB "H_T1"
   [`e:(uarch_event)list`; `st:int64`; `mlen MOD r`; `r:num`; `p:num`;
    `word_xor (keccak_absorb r P (mlen DIV r))
              (word (M DIV 2 EXP (8 * r * mlen DIV r))):1600 word`;
    `pc:num`] ABS_VARS 1 THEN
  SUBGOAL_THEN `r - 1 < 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABS_SUB "H_T2"
   [`e:(uarch_event)list`; `st:int64`; `r - 1`;
    `word_xor (word_xor (keccak_absorb r P (mlen DIV r))
                        (word (M DIV 2 EXP (8 * r * mlen DIV r))))
              (word (2 EXP (8 * mlen MOD r) * p)):1600 word`;
    `pc:num`] ABS_VARS 2 THEN
  ARM_STEPS_TAC ABS_EXEC (3--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      if has_wbytes th then
        ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
      else failwith "") THEN
    MP_TAC(SPECL [`keccak_absorb r P (mlen DIV r)`; `M:num`; `mlen:num`;
                  `r:num`; `p:num`] FINAL_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ABS_DISCHARGE_TAC];;


let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e st r m mlen p M pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       0 < r /\ r <= 200 /\ p < 128 /\ 0 < mlen /\
       PAIRWISE nonoverlapping
        [(st,200); (m,mlen); (word_sub stackpointer (word 256),256)] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [(st,200); (word_sub stackpointer (word 256),256)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                 read (memory :> bytes(m,mlen)) s = M /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb r
                    (M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad r p mlen))
                    (mlen DIV r))
                  (word((M + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad r p mlen)) DIV
                        2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st r mlen pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`,
  ABS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_join1`
   ABS_MID_J1 THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_join2`
        ABS_MID_J2 THEN
      CONJ_TAC THENL [ABS_ENTRY_S_TAC; ABS_J2_TAC];
      ENSURES_EVENTS_SEQUENCE_TAC
       `pc + mlk_keccak_absorb_once_loop1_exit` ABS_MID_LX THEN
      CONJ_TAC THENL [ABS_LOOP_TAC; ABS_LX_TAC]];
    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN ABS_PART2_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, as in gcc12_O2 but for a nonempty message, and   *)
(* the safety theorem, both from FULL.                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st r m mlen p M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        0 < r /\ r <= 200 /\ p < 128 /\ 0 < mlen /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 256),256)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(st,200); (word_sub stackpointer (word 256),256)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                  read (memory :> bytes(m,mlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad r p mlen))
                     (mlen DIV r))
                   (word((M + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad r p mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 256),256)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `f:int64->int64->num->num->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `r:num`; `m:int64`; `mlen:num`;
    `p:num`; `M:num`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e st r m mlen p pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       0 < r /\ r <= 200 /\ p < 128 /\ 0 < mlen /\
       PAIRWISE nonoverlapping
        [(st,200); (m,mlen); (word_sub stackpointer (word 256),256)] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [(st,200); (word_sub stackpointer (word 256),256)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlk_keccak_absorb_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st r mlen pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 256),256;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 256),256]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 256),256)])`,
  MP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `M:num` `read (memory :> bytes(m,mlen))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `r:num`; `m:int64`; `mlen:num`;
    `p:num`; `M:num`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
