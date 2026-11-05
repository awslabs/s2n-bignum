(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a Keccak state, with the padding. This is  *)
(* the code for the static function mlk_keccak_absorb_once from mlkem-       *)
(* native's portable C implementation compiled by gcc 12 with -O2 as one    *)
(* translation unit (see mlkem_native/README.md), with the specification     *)
(* that it has in the separately compiled gcc12_O2 build. It zeroes the     *)
(* state, XORs in each whole block of r bytes of the message and permutes   *)
(* the state, and then XORs in the rest of the message and the padding, but  *)
(* does not permute the state again. The calls of mlkem_keccakf1600_xor_    *)
(* bytes are inlined as loops and single-byte XORs, which are proved here   *)
(* as lemmas (one for the loop that XORs in a block, one for the loop that  *)
(* XORs in the rest of the message, and one for each of the two bytes of     *)
(* padding), and the permutation is the call of mlk_keccakf1600_permute_c.  *)
(* There are two differences from the gcc12_O2 specification: the message    *)
(* must be nonempty (mlen > 0), since a message shorter than a block goes    *)
(* straight to the loop that XORs in the rest of the message, which does    *)
(* not test for mlen = 0, and r is not zero; and the frame is that of the    *)
(* ABI, which holds since no caller keeps a caller-saved register across    *)
(* the call. It is verified in the whole image (see libmlkem.ml).            *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_permute.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_xor_bytes.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

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
(* as the loop of mlkem_keccakf1600_xor_bytes, with offset 0, with the       *)
(* bound in a register (X22, or X3 set from X23) and the test of the loop   *)
(* in different order. They are proved by one function, from the lemma       *)
(* statement function of keccakf1600x4_xor_bytes.ml, here repeated.          *)
(* ------------------------------------------------------------------------- *)

let xor_lemma_stmt from_lab to_lab st_addr pre post regs =
  parse_term (Printf.sprintf
   "!(a:int64) (d:int64) off len (S:1600 word) m pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        off + len <= 200 /\\ ~(len = 0) /\\
        ALL (nonoverlapping (%s,200)) [(word pc,libmlkem_size); (d,len)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
                  read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> wbytes (%s)) s = S /\\
                  read (memory :> bytes(d,len)) s = m)
             (\\s. read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> wbytes (%s)) s =
                  word_xor S (word(2 EXP (8 * off) * m)))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(%s,200)])"
   st_addr from_lab pre st_addr to_lab post st_addr regs st_addr);;

let xorC_prove exec stmt lab1 lab2 inv_regs init_n exit_n flip =
  let sn = Printf.sprintf "s%d" exit_n in
  let flagtm = if flip then
   "~(val(word_sub (word_add (word i) (word 1)) (word len):int64) = 0) <=> i + 1 < len"
   else "~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=> i + 1 < len" in
  prove(stmt,
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`; `off:num`; `len:num`;
                       `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst exec] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `len:num` (parse_term ("pc + "^lab1))
   (parse_term ("pc + "^lab2))
   (parse_term (Printf.sprintf
   "\\i s. %s /\\
          read (memory :> bytes(d,len)) s = m /\\
          !j. j < 200
              ==> read (memory :> bytes8(word_add a (word j))) s =
                  word_subword
                   (word_xor (S:1600 word)
                     (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                   (8 * j,8)" (inv_regs "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Entry: only the bytes of the state ***)

    ENSURES_INIT_TAC "s0" THEN
    (if init_n > 0 then
       ARM_STEPS_TAC exec (1--init_n) THEN ARGS_32_TAC [`len:num`]
     else ALL_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0; word_subword] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES8_OF_NUM THEN
    EXISTS_TAC `200` THEN ASM_REWRITE_TAC[];

    (*** The loop body, for byte off + i of the state, and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `off + i < 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `bytes8` (concl th) then
        ASSUME_TAC(MP (SPEC `off + i` th) (ASSUME `off + i < 200`)) THEN
        ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `off + i` th)
      else failwith "XOR_BYTES_RESTRICT_RULE") THEN
    MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC exec (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (parse_term flagtm)
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB; GSYM WORD_ADD] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[XOR_BYTES_STEP] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (_,w) -> SPEC_TAC(lhand(rand w),`b1:byte`) THEN
                   SPEC_TAC(rand(rand w),`b2:byte`)) THEN
    REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));

    (*** The loop exit, with the whole state ***)

    ENSURES_INIT_TAC "s0" THEN
    (if exit_n > 0 then ARM_STEPS_TAC exec (1--exit_n) else ALL_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    MP_TAC(ISPECL [`a:int64`; `S:1600 word`; `off:num`; `len:num`; `d:int64`;
                   `m:num`; parse_term (sn^":armstate")] XOR_BYTES_FINAL) THEN
    ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600]]);;

(*** The loop that XORs in a block, from its head to its exit ***)

let ABS_LA_STMT = xor_lemma_stmt
  "mlk_keccak_absorb_once_loop2" "mlk_keccak_absorb_once_loop2_exit" "a"
  "read X20 s = word_add a (word off) /\\ read X19 s = word 0 /\\
   read X21 s = d /\\ read X22 s = word len"
  "read X19 s = word len"
  "X0; X4; X19";;

let ABS_LA = xorC_prove ABS_EXEC ABS_LA_STMT
  "mlk_keccak_absorb_once_loop2" "mlk_keccak_absorb_once_loop2_exit"
  (fun i -> "read X20 s = word_add a (word off) /\\ read X19 s = word "^i^" /\\
             read X21 s = d /\\ read X22 s = word len") 0 0 true;;

(*** The loop that XORs in the rest of the message, from join2 to join1 ***)

let ABS_LC_STMT = xor_lemma_stmt
  "mlk_keccak_absorb_once_join2" "mlk_keccak_absorb_once_join1" "a"
  "read X20 s = word_add a (word off) /\\ read X21 s = d /\\
   read X23 s = word len"
  "read X0 s = word len /\\ read X3 s = word len"
  "X0; X1; X2; X3";;

let ABS_LC = xorC_prove ABS_EXEC ABS_LC_STMT
  "mlk_keccak_absorb_once_loop3" "mlk_keccak_absorb_once_loop3_exit"
  (fun i -> "read X20 s = word_add a (word off) /\\ read X0 s = word "^i^" /\\
             read X21 s = d /\\ read X3 s = word len") 2 1 false;;

(* ------------------------------------------------------------------------- *)
(* The padding: byte t of the state XORed with p, then byte r - 1 with 0x80. *)
(* ------------------------------------------------------------------------- *)

let ABS_T1_STMT = `!st t r p (A:1600 word) pc.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        t < r /\ r <= 200 /\ p < 128 /\
        nonoverlapping (st,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once_join1) /\
                  read X20 s = st /\ read X23 s = word t /\
                  read X24 s = word r /\ read X25 s = word p /\
                  read (memory :> wbytes st) s = A)
             (\s. read PC s =
                  word (pc + mlk_keccak_absorb_once_in_keccakf1600_xor_bytes_3) /\
                  read X24 s = word (r - 1) /\
                  read (memory :> wbytes st) s =
                  word_xor A (word(2 EXP (8 * t) * p)))
             (MAYCHANGE [PC; X0; X24; X25] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(st,200)])`;;

let ABS_T1 = prove(ABS_T1_STMT,
  MAP_EVERY X_GEN_TAC [`st:int64`; `t:num`; `r:num`; `p:num`; `A:1600 word`;
                       `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; READ_MEMORY_WBYTES_1600;
              fst ABS_EXEC] THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
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
  MP_TAC(ISPECL [`st:int64`; `A:1600 word`; `t:num`; `1`; `p:num`;
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
  REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let ABS_T2_STMT = `!st k (A:1600 word) pc.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        k < 200 /\
        nonoverlapping (st,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s =
                  word (pc + mlk_keccak_absorb_once_in_keccakf1600_xor_bytes_3) /\
                  read X20 s = st /\ read X24 s = word k /\
                  read (memory :> wbytes st) s = A)
             (\s. read PC s =
                  word (pc + mlk_keccak_absorb_once_in_keccakf1600_xor_bytes_3_end) /\
                  read (memory :> wbytes st) s =
                  word_xor A (word(2 EXP (8 * k) * 128)))
             (MAYCHANGE [PC; X0] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(st,200)])`;;

let ABS_T2 = prove(ABS_T2_STMT,
  MAP_EVERY X_GEN_TAC [`st:int64`; `k:num`; `A:1600 word`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; READ_MEMORY_WBYTES_1600;
              fst ABS_EXEC] THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP XOR_BYTES_OF_STATE) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      ASSUME_TAC(MP (SPEC `k:num` th) (ASSUME `k < 200`)) THEN
      ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `k:num` th)
    else failwith "XOR_BYTES_RESTRICT_RULE") THEN
  MP_TAC(SPEC `k:num` VAL_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  ARM_STEPS_TAC ABS_EXEC (1--1) THEN ARGS_32_TAC [`k:num`] THEN
  ARM_STEPS_TAC ABS_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`st:int64`; `A:1600 word`; `k:num`; `1`; `128`;
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
  GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

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
(* The two loops with the offset 0 of the XOR, which they have here.         *)
(* ------------------------------------------------------------------------- *)

let ABS_LA0 = GENL
 [`a:int64`; `d:int64`; `len:num`; `S:1600 word`; `m:num`; `pc:num`]
 (REWRITE_RULE[WORD_ADD_0; ADD_CLAUSES; EXP; MULT_CLAUSES]
   (SPECL [`a:int64`; `d:int64`; `0`; `len:num`; `S:1600 word`; `m:num`;
           `pc:num`] ABS_LA));;

let ABS_LC0 = GENL
 [`a:int64`; `d:int64`; `len:num`; `S:1600 word`; `m:num`; `pc:num`]
 (REWRITE_RULE[WORD_ADD_0; ADD_CLAUSES; EXP; MULT_CLAUSES]
   (SPECL [`a:int64`; `d:int64`; `0`; `len:num`; `S:1600 word`; `m:num`;
           `pc:num`] ABS_LC));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, in parts. The statement is that of gcc12_O2 with       *)
(* mlen > 0. The parts are the entry to the end of the XORs (the label       *)
(* join1), and the padding to the return. The first part has the case of a   *)
(* short message, which goes to join2 to XOR in the message (and then to     *)
(* join1), and that of a message of at least a block, where the loop over    *)
(* the blocks is followed by the XOR of the rest of the message, if any.     *)
(* ------------------------------------------------------------------------- *)

let ABS_SUB lemma n ilist =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,ABS_EXEC,0x0,
    mlkem_native_libmlkem_gcc12_O2_mono_mc,lemma) ilist n;;

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

(*** The entry of a message shorter than a block: the state is zeroed and the
     code jumps to join2 ***)

let ABS_ENTRY_S_TAC =
  ENSURES_INIT_TAC "s0" THEN
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
  CONJ_TAC THENL [ASM_ARITH_TAC; KECCAK_ZERO_STATE_TAC];;

(*** From join2 to join1: the XOR of the rest of the message ***)

let ABS_J2_TAC =
  ENSURES_INIT_TAC "s0" THEN
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
  ABS_SUB ABS_LC0 1
   [`st:int64`; `word_add (m:int64) (word (r * (mlen DIV r)))`; `mlen MOD r`;
    `keccak_absorb r P (mlen DIV r)`;
    `(M DIV 2 EXP (8 * r * mlen DIV r)) MOD 2 EXP (8 * mlen MOD r)`;
    `pc:num`] THEN
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
  ASM_REWRITE_TAC[];;

(*** The loop over the whole blocks: the entry ***)

let ABS_LINIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
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
  KECCAK_ZERO_STATE_TAC;;

(*** The body of the loop: XOR in a block, permute, and the test ***)

let ABS_LBODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
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
  ABS_SUB ABS_LA0 3
   [`st:int64`; `word_add (m:int64) (word (r * i))`; `r:num`;
    `keccak_absorb r P i`; `(M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
    `pc:num`] THEN
  ARM_STEPS_TAC ABS_EXEC (4--6) THEN
  ABS_SUB MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_F1600 7
   [`read X0 s`;
    `word_xor (keccak_absorb r P i)
              (word ((M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r))):1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] THEN
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
    UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC];;

(*** After the loop: the rest of the message, if there is any ***)

let ABS_LX_TAC =
  ASM_CASES_TAC `mlen MOD r = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN
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
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_join2` ABS_MID_J2 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC ABS_EXEC (1--1) THEN
    SUBGOAL_THEN `val(word (mlen MOD r):int64) = mlen MOD r`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`] MOD_LT_EQ) THEN
      ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ABS_J2_TAC];;

(*** The padding: byte t, then byte r - 1 ***)

let has_wbytes th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = "wbytes"))
      (concl th);;

let ABS_PART2_TAC =
  SUBGOAL_THEN `mlen MOD r < r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `0 < r ==> ~(r = 0)`]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ABS_SUB ABS_T1 1
   [`st:int64`; `mlen MOD r`; `r:num`; `p:num`;
    `word_xor (keccak_absorb r P (mlen DIV r))
              (word (M DIV 2 EXP (8 * r * mlen DIV r))):1600 word`;
    `pc:num`] THEN
  SUBGOAL_THEN `r - 1 < 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABS_SUB ABS_T2 2
   [`st:int64`; `r - 1`;
    `word_xor (word_xor (keccak_absorb r P (mlen DIV r))
                        (word (M DIV 2 EXP (8 * r * mlen DIV r))))
              (word (2 EXP (8 * mlen MOD r) * p)):1600 word`;
    `pc:num`] THEN
  ARM_STEPS_TAC ABS_EXEC (3--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    if has_wbytes th then
      ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
    else failwith "") THEN
  MP_TAC(SPECL [`keccak_absorb r P (mlen DIV r)`; `M:num`; `mlen:num`;
                `r:num`; `p:num`] FINAL_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);;

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
  ABS_SETUP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_join1` ABS_MID_J1 THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THENL
     [ENSURES_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_join2` ABS_MID_J2 THEN
      CONJ_TAC THENL [ABS_ENTRY_S_TAC; ABS_J2_TAC];
      ENSURES_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_loop1_exit`
        ABS_MID_LX THEN
      CONJ_TAC THENL
       [ENSURES_WHILE_UP2_TAC `mlen DIV r` `pc + mlk_keccak_absorb_once_loop1`
          `pc + mlk_keccak_absorb_once_loop1_exit` ABS_INV THEN
        REPEAT CONJ_TAC THENL
         [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];
          ABS_LINIT_TAC;
          ABS_LBODY_TAC;
          ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC[ABSORB_MOD_EQ]];
        ABS_LX_TAC]];
    ABS_PART2_TAC]);;
