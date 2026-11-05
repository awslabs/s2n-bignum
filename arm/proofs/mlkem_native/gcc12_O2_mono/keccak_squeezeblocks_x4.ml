(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from four Keccak states. This is the code for the  *)
(* static function mlk_keccak_squeezeblocks_x4 from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 as one translation unit      *)
(* (see mlkem_native/README.md). In the separately compiled gcc12_O2 build   *)
(* it exists only as mlkem_shake128x4_squeezeblocks (rate 168), and its      *)
(* specification here is that of that function with the rate r a parameter,  *)
(* as the 7th argument: for each of nblocks blocks it permutes the four      *)
(* states and extracts the first r bytes of each. The four permutations are  *)
(* calls of mlk_keccakf1600_permute_c, and the four extractions (of the      *)
(* function mlkem_keccakf1600_extract_bytes) are inlined as loops. Unlike    *)
(* mlkem_keccakf1600_extract_bytes, they do not test for len = 0, so r must  *)
(* be nonzero here. Each loop is proved as a lemma, with the specification   *)
(* of the extraction for its state, from its head to the head of the next    *)
(* loop, and the function follows from them. It is verified in the whole     *)
(* image (see libmlkem.ml).                                                  *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_permute.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_xor_bytes.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_keccak_squeezeblocks_x4:
     +0x0  cbz     x4, ret2
     +0x4  stp     x19, x20, [sp, #-96]!
     +0x8  mov     x20, x1
     +0xc  mov     x19, x0
    +0x10  stp     x21, x22, [sp, #16]
    +0x14  mov     x22, x3
    +0x18  mov     x21, x2
    +0x1c  stp     x23, x24, [sp, #32]
    +0x20  mov     x23, x5
    +0x24  add     x24, x5, #0x258
    +0x28  stp     x25, x26, [sp, #48]
    +0x2c  mov     w26, w6
    +0x30  add     x25, x5, #0x190
    +0x34  stp     x27, x28, [sp, #64]
    +0x38  mov     x27, x4
    +0x3c  add     x28, x5, #0xc8
    +0x40  str     x30, [sp, #80]
    +0x44  nop
  loop1:
    +0x48  mov     x0, x23
    +0x4c  bl      mlk_keccakf1600_permute_c
    +0x50  mov     x0, x28
    +0x54  bl      mlk_keccakf1600_permute_c
    +0x58  mov     x0, x25
    +0x5c  bl      mlk_keccakf1600_permute_c
    +0x60  mov     x0, x24
    +0x64  bl      mlk_keccakf1600_permute_c
    +0x68  mov     x0, #0x0
    +0x6c  nop
  loop2:
    +0x70  ldrb    w1, [x23, x0]
    +0x74  mov     x2, x0
    +0x78  strb    w1, [x19, x0]
    +0x7c  add     x0, x0, #0x1
  loop2_test:
    +0x80  cmp     x26, x0
    +0x84  b.ne    loop2
  loop2_exit:
    +0x88  mov     x1, #0x0
    +0x8c  nop
  loop3:
    +0x90  ldrb    w6, [x28, x1]
    +0x94  cmp     x2, x1
    +0x98  strb    w6, [x20, x1]
  loop3_test:
    +0x9c  add     x1, x1, #0x1
    +0xa0  b.ne    loop3
  loop3_exit:
    +0xa4  mov     x1, #0x0
  loop4:
    +0xa8  ldrb    w6, [x25, x1]
    +0xac  cmp     x2, x1
    +0xb0  strb    w6, [x21, x1]
  loop4_test:
    +0xb4  add     x1, x1, #0x1
    +0xb8  b.ne    loop4
  loop4_exit:
    +0xbc  mov     x1, #0x0
  loop5:
    +0xc0  ldrb    w6, [x24, x1]
    +0xc4  cmp     x2, x1
    +0xc8  strb    w6, [x22, x1]
  loop5_test:
    +0xcc  add     x1, x1, #0x1
    +0xd0  b.ne    loop5
  loop5_exit:
    +0xd4  add     x22, x22, x0
    +0xd8  add     x21, x21, x0
    +0xdc  add     x20, x20, x0
    +0xe0  add     x19, x19, x0
  loop1_test:
    +0xe4  subs    x27, x27, #0x1
    +0xe8  b.ne    loop1
  loop1_exit:
    +0xec  ldp     x21, x22, [sp, #16]
    +0xf0  ldp     x23, x24, [sp, #32]
    +0xf4  ldp     x25, x26, [sp, #48]
    +0xf8  ldp     x27, x28, [sp, #64]
    +0xfc  ldr     x30, [sp, #80]
   +0x100  ldp     x19, x20, [sp], #96
  ret1:
   +0x104  ret
  ret2:
   +0x108  ret
 ***)

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_keccak_squeezeblocks_x4"];;

let SQ_EXEC = MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the four inlined extraction loops. Each copies the first   *)
(* len bytes of the state at a to d: the bytes of the state are those of the *)
(* number val S, and those written are val S MOD 2 EXP (8 * len). The loops  *)
(* are stated by one function from the labels, the registers read and        *)
(* written, and proved by another. The first loop leaves the last index in   *)
(* X2, which the others compare with; the setup of the next loop is part of  *)
(* the lemma for the previous one.                                           *)
(* ------------------------------------------------------------------------- *)

let sq_lemma_stmt from_lab to_lab pre post regs =
  parse_term (Printf.sprintf
   "!(a:int64) (d:int64) len (S:1600 word) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        len <= 200 /\\ ~(len = 0) /\\
        ALL (nonoverlapping (d,len)) [(word pc,libmlkem_size); (a,200)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
                  read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> wbytes a) s = S)
             (\\s. read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> bytes(d,len)) s = val S MOD 2 EXP (8 * len))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(d,len)])"
   from_lab pre to_lab post regs);;

(*** nbody: the instructions of the loop body, flag: the loop test is
     cmp x26, x0 after the increment (the first loop), nexit: the
     instructions between the loop and the next label ***)

let sq_prove stmt lab1 lab2 inv_regs nbody first nexit =
  let flagtm = if first then
   "~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=> i + 1 < len"
   else "~(val(word_sub (word (len - 1)) (word i):int64) = 0) <=> i + 1 < len" in
  let sn = Printf.sprintf "s%d" nexit in
  prove(stmt,
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`; `len:num`; `S:1600 word`;
                       `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst SQ_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `len:num` (parse_term ("pc + "^lab1))
   (parse_term ("pc + "^lab2))
   (parse_term (Printf.sprintf
   "\\i s. %s /\\
          read (memory :> bytes(a,200)) s = val (S:1600 word) /\\
          read (memory :> bytes(d,i)) s = val S MOD 2 EXP (8 * i)"
   (inv_regs "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Entry: nothing has been written ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];

    (*** The loop body, copying byte i of the state, and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `i:num`;
                  `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC SQ_EXEC (1--nbody) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (parse_term flagtm) SUBST_ALL_TAC THENL
     [(if first then
        REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD;
                    DIMINDEX_64] THEN
        SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC
      else
        MATCH_MP_TAC XOR_LAST_FLAG THEN ASM_REWRITE_TAC[] THEN
        SIMPLE_ARITH_TAC);
      ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB; GSYM WORD_ADD] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `~(i + 1 = 0)`] THEN NO_TAC;
      REWRITE_TAC[WORD_ADD; READ_MEMORY_BYTES_SNOC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_16;
                  DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8 /\ 4294967296 = 2 EXP 32 /\
                              18446744073709551616 = 2 EXP 64`;
                  MOD_MOD_EXP_MIN] THEN
      CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
      REWRITE_TAC[MULT_CLAUSES; MOD_MULT_MOD; ADD_SYM]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    (if nexit > 0 then ARM_STEPS_TAC SQ_EXEC (1--nexit) else ALL_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(ASM_MESON_TAC[])]);;

(*** The first loop, with the setup of the second ***)

let SQ_L2_STMT = sq_lemma_stmt
  "mlk_keccak_squeezeblocks_x4_loop2" "mlk_keccak_squeezeblocks_x4_loop3"
  "read X0 s = word 0 /\\ read X19 s = d /\\ read X23 s = a /\\
   read X26 s = word len"
  "read X0 s = word len /\\ read X1 s = word 0 /\\ read X2 s = word (len - 1)"
  "X0; X1; X2";;

let SQ_L2 = sq_prove SQ_L2_STMT
  "mlk_keccak_squeezeblocks_x4_loop2" "mlk_keccak_squeezeblocks_x4_loop2_exit"
  (fun i -> "read X0 s = word "^i^" /\\
             (~("^i^" = 0) ==> read X2 s = word ("^i^" - 1)) /\\
             read X19 s = d /\\ read X23 s = a /\\ read X26 s = word len")
  6 true 2;;

(*** The other three loops ***)

let SQ_L3_STMT = sq_lemma_stmt
  "mlk_keccak_squeezeblocks_x4_loop3" "mlk_keccak_squeezeblocks_x4_loop4"
  "read X1 s = word 0 /\\ read X2 s = word (len - 1) /\\ read X20 s = d /\\
   read X28 s = a"
  "read X1 s = word 0"
  "X1; X6";;

let SQ_L3 = sq_prove SQ_L3_STMT
  "mlk_keccak_squeezeblocks_x4_loop3" "mlk_keccak_squeezeblocks_x4_loop3_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X20 s = d /\\ read X28 s = a")
  5 false 1;;

let SQ_L4_STMT = sq_lemma_stmt
  "mlk_keccak_squeezeblocks_x4_loop4" "mlk_keccak_squeezeblocks_x4_loop5"
  "read X1 s = word 0 /\\ read X2 s = word (len - 1) /\\ read X21 s = d /\\
   read X25 s = a"
  "read X1 s = word 0"
  "X1; X6";;

let SQ_L4 = sq_prove SQ_L4_STMT
  "mlk_keccak_squeezeblocks_x4_loop4" "mlk_keccak_squeezeblocks_x4_loop4_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X21 s = d /\\ read X25 s = a")
  5 false 1;;

let SQ_L5_STMT = sq_lemma_stmt
  "mlk_keccak_squeezeblocks_x4_loop5" "mlk_keccak_squeezeblocks_x4_loop5_exit"
  "read X1 s = word 0 /\\ read X2 s = word (len - 1) /\\ read X22 s = d /\\
   read X24 s = a"
  "read X1 s = word len"
  "X1; X6";;

let SQ_L5 = sq_prove SQ_L5_STMT
  "mlk_keccak_squeezeblocks_x4_loop5" "mlk_keccak_squeezeblocks_x4_loop5_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X22 s = d /\\ read X24 s = a")
  5 false 0;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_shake128x4_squeezeblocks, for each of the *)
(* four states S, block i of its output, as a number, is the first r bytes   *)
(* of keccak_squeeze (i + 1) S, and the state becomes keccak_squeeze nblocks *)
(* S. The stack is the 96 bytes of the function and the 192 used by          *)
(* mlk_keccakf1600_permute_c below them.                                     *)
(* ------------------------------------------------------------------------- *)

let SQ_SUB lemma ilist n =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,SQ_EXEC,0x0,
    mlkem_native_libmlkem_gcc12_O2_mono_mc,lemma) ilist n;;

let SQ_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let LE_MUL_SELF = prove
 (`!r n. 0 < r ==> n <= r * n`,
  REPEAT STRIP_TAC THEN TRANS_TAC LE_TRANS `1 * n` THEN CONJ_TAC THENL
   [ARITH_TAC; REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC]);;

let SQ_BOUND_TAC =
  SUBGOAL_THEN `800 + r * nblocks <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nblocks < 18446744073709551616` ASSUME_TAC THENL
   [MP_TAC(SPECL [`r:num`; `nblocks:num`] LE_MUL_SELF) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word nblocks:int64) = nblocks` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let SQ_PRESERVED_TAC =
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28`;;

let SQ_NONZERO_TAC =
  let t1 = `val(word nblocks:int64) = nblocks` and t2 = `~(nblocks = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

let SQ_COUNTER_TAC =
  SUBGOAL_THEN `word_sub (word (nblocks - i)) (word 1):int64 =
                word(nblocks - (i + 1))` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(nblocks - (i + 1)):int64) = nblocks - (i + 1)`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(nblocks - (i + 1) = 0) <=> i + 1 < nblocks`
  SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC];;

let SQ_PERMUTE =
  MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_F1600;;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!out0 out1 out2 out3 nblocks st r
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        PAIRWISE nonoverlapping
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_squeezeblocks_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st;
                               word r] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out1,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out2,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out3,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * r)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,r * nblocks);
                memory :> bytes(out1,r * nblocks);
                memory :> bytes(out2,r * nblocks);
                memory :> bytes(out3,r * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 288),288)])`,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `nblocks:num`;
    `st:int64`; `r:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN

  (*** The case nblocks = 0, where nothing is done ***)

  ASM_CASES_TAC `nblocks = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];
    ALL_TAC] THEN
  SQ_BOUND_TAC THEN SQ_PRESERVED_TAC THEN

  (*** The loop, with i blocks done ***)

  ENSURES_WHILE_UP2_TAC `nblocks:num`
   `pc + mlk_keccak_squeezeblocks_x4_loop1`
   `pc + mlk_keccak_squeezeblocks_x4_loop1_exit`
   `\i s. read X19 s = word_add out0 (word(r * i)) /\
          read X20 s = word_add out1 (word(r * i)) /\
          read X21 s = word_add out2 (word(r * i)) /\
          read X22 s = word_add out3 (word(r * i)) /\
          read X23 s = st /\
          read X24 s = word_add st (word 600) /\
          read X25 s = word_add st (word 400) /\
          read X26 s = word r /\
          read X27 s = word(nblocks - i) /\
          read X28 s = word_add st (word 200) /\
          read SP s = word_add stackpointer (word 192) /\
          read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 200))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x27_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x28_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          returnaddress /\
          read (memory :> bytes(out0,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S0) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out1,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S1) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out2,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S2) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out3,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S3) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(st,200)) s =
          val(keccak_squeeze i (S0:1600 word)) /\
          read (memory :> bytes(word_add st (word 200),200)) s =
          val(keccak_squeeze i (S1:1600 word)) /\
          read (memory :> bytes(word_add st (word 400),200)) s =
          val(keccak_squeeze i (S2:1600 word)) /\
          read (memory :> bytes(word_add st (word 600),200)) s =
          val(keccak_squeeze i (S3:1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SQ_EXEC (1--1) THEN
    SQ_NONZERO_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (2--18) THEN ARGS_32_TAC [`r:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];

    (*** The loop body: four permutations, four extractions, the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `r * i + r <= r * nblocks` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`; LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (4--5) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (7--8) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (10--11) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC SQ_EXEC (13--14) THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L2 [`read X23 s`; `read X19 s`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S0:1600 word))`;
                  `pc:num`] 15 THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L3 [`word_add (st:int64) (word 200)`;
                  `word_add (out1:int64) (word (r * i))`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S1:1600 word))`;
                  `pc:num`] 16 THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L4 [`word_add (st:int64) (word 400)`;
                  `word_add (out2:int64) (word (r * i))`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S2:1600 word))`;
                  `pc:num`] 17 THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L5 [`word_add (st:int64) (word 600)`;
                  `word_add (out3:int64) (word (r * i))`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S3:1600 word))`;
                  `pc:num`] 18 THEN
    ARM_STEPS_TAC SQ_EXEC (19--24) THEN
    SQ_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
        REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
        NO_TAC);

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SQ_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the extraction loops with the events (constant time and    *)
(* memory safety), combined with the correctness, as for the XOR loops.      *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let sq_full_stmt from_lab to_lab pre post regs =
  parse_term (Printf.sprintf
   "exists f_events.
      forall e (a:int64) (d:int64) len (S:1600 word) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        len <= 200 /\\ ~(len = 0) /\\
        ALL (nonoverlapping (d,len)) [(word pc,libmlkem_size); (a,200)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
                  read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> wbytes a) s = S /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> bytes(d,len)) s = val S MOD 2 EXP (8 * len) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a d len pc /\\
                     memaccess_inbounds e2 [a,200; d,len] [d,len]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(d,len)])"
   from_lab pre to_lab post regs);;

let sqF_prove stmt lab1 lab2 inv_regs nbody first nexit =
  let flagtm = if first then
   "~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=> i + 1 < len"
   else "~(val(word_sub (word (len - 1)) (word i):int64) = 0) <=> i + 1 < len" in
  prove(stmt,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (d:int64) (len:num) (pc:num).
      APPEND (f_ev_epil a d len pc)
        (APPEND (ENUMERATEL len (\i. f_ev_loop a d len pc i))
                (f_ev_prol a d len pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`; `len:num`; `S:1600 word`;
                       `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst SQ_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` (parse_term ("pc + "^lab1))
   (parse_term ("pc + "^lab2))
   (parse_term (Printf.sprintf
   "\\i s. %s /\\
          read (memory :> bytes(a,200)) s = val (S:1600 word) /\\
          read (memory :> bytes(d,i)) s = val S MOD 2 EXP (8 * i)"
   (inv_regs "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Entry: nothing has been written ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, copying byte i of the state, and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `i:num`;
                  `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC SQ_EXEC (1--nbody) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (parse_term flagtm) SUBST_ALL_TAC THENL
     [(if first then
        REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD;
                    DIMINDEX_64] THEN
        SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC
      else
        MATCH_MP_TAC XOR_LAST_FLAG THEN ASM_REWRITE_TAC[] THEN
        SIMPLE_ARITH_TAC);
      ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB; GSYM WORD_ADD] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `~(i + 1 = 0)`] THEN NO_TAC;
      REWRITE_TAC[WORD_ADD; READ_MEMORY_BYTES_SNOC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_16;
                  DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8 /\ 4294967296 = 2 EXP 32 /\
                              18446744073709551616 = 2 EXP 64`;
                  MOD_MOD_EXP_MIN] THEN
      CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
      REWRITE_TAC[MULT_CLAUSES; MOD_MULT_MOD; ADD_SYM] THEN NO_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop exit ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    (if nexit > 0 then ARM_STEPS_TAC SQ_EXEC (1--nexit) else ALL_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ((CONJ_TAC THENL [ASM_MESON_TAC[]; DISCHARGE_SAFETY_PROPERTY_TAC]) ORELSE
     DISCHARGE_SAFETY_PROPERTY_TAC)]);;

let SQ_F2_STMT = sq_full_stmt
  "mlk_keccak_squeezeblocks_x4_loop2" "mlk_keccak_squeezeblocks_x4_loop3"
  "read X0 s = word 0 /\\ read X19 s = d /\\ read X23 s = a /\\
   read X26 s = word len"
  "read X0 s = word len /\\ read X1 s = word 0 /\\ read X2 s = word (len - 1)"
  "X0; X1; X2";;

let SQ_F2 = sqF_prove SQ_F2_STMT
  "mlk_keccak_squeezeblocks_x4_loop2" "mlk_keccak_squeezeblocks_x4_loop2_exit"
  (fun i -> "read X0 s = word "^i^" /\\
             (~("^i^" = 0) ==> read X2 s = word ("^i^" - 1)) /\\
             read X19 s = d /\\ read X23 s = a /\\ read X26 s = word len")
  6 true 2;;

let SQ_F3_STMT = sq_full_stmt
  "mlk_keccak_squeezeblocks_x4_loop3" "mlk_keccak_squeezeblocks_x4_loop4"
  "read X1 s = word 0 /\\ read X2 s = word (len - 1) /\\ read X20 s = d /\\
   read X28 s = a"
  "read X1 s = word 0"
  "X1; X6";;

let SQ_F3 = sqF_prove SQ_F3_STMT
  "mlk_keccak_squeezeblocks_x4_loop3" "mlk_keccak_squeezeblocks_x4_loop3_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X20 s = d /\\ read X28 s = a")
  5 false 1;;

let SQ_F4_STMT = sq_full_stmt
  "mlk_keccak_squeezeblocks_x4_loop4" "mlk_keccak_squeezeblocks_x4_loop5"
  "read X1 s = word 0 /\\ read X2 s = word (len - 1) /\\ read X21 s = d /\\
   read X25 s = a"
  "read X1 s = word 0"
  "X1; X6";;

let SQ_F4 = sqF_prove SQ_F4_STMT
  "mlk_keccak_squeezeblocks_x4_loop4" "mlk_keccak_squeezeblocks_x4_loop4_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X21 s = d /\\ read X25 s = a")
  5 false 1;;

let SQ_F5_STMT = sq_full_stmt
  "mlk_keccak_squeezeblocks_x4_loop5" "mlk_keccak_squeezeblocks_x4_loop5_exit"
  "read X1 s = word 0 /\\ read X2 s = word (len - 1) /\\ read X22 s = d /\\
   read X24 s = a"
  "read X1 s = word len"
  "X1; X6";;

let SQ_F5 = sqF_prove SQ_F5_STMT
  "mlk_keccak_squeezeblocks_x4_loop5" "mlk_keccak_squeezeblocks_x4_loop5_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X22 s = d /\\ read X24 s = a")
  5 false 0;;

let SQ_PERMUTE_FULL =
  MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_F1600;;

let SQ_FULL_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,SQ_EXEC,0x0,
       mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`;
        `nblocks:num`; `st:int64`; `r:num`; `pc:num`; `stackpointer:int64`;
        `returnaddress:int64`; `i:num`;
        `f_ev_loop:int64->int64->int64->int64->num->int64->num->num->int64->
                   int64->num->(uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
  forall e out0 out1 out2 out3 nblocks st r
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        PAIRWISE nonoverlapping
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_squeezeblocks_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st;
                               word r] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out1,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out2,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out3,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * r)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3 /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out0 out1 out2 out3 nblocks st r pc
                            (word_sub stackpointer (word 288)) returnaddress /\
                     memaccess_inbounds e2
                      [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
                       out3,r * nblocks; st,800;
                       word_sub stackpointer (word 288),288;
                       word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                      [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
                       out3,r * nblocks; st,800;
                       word_sub stackpointer (word 288),288]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,r * nblocks);
                memory :> bytes(out1,r * nblocks);
                memory :> bytes(out2,r * nblocks);
                memory :> bytes(out3,r * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 288),288)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_PERMUTE_FULL "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F2 "H_L2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F3 "H_L3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F4 "H_L4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F5 "H_L5" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out0:int64) (out1:int64) (out2:int64) (out3:int64) (nblocks:num)
      (st:int64) (r:num) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out0 out1 out2 out3 nblocks st r pc stackpointer
                     returnaddress
      else APPEND (f_ev_epil out0 out1 out2 out3 nblocks st r pc stackpointer
                             returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out0 out1 out2 out3 nblocks st r pc
                               stackpointer returnaddress i))
              (f_ev_prol out0 out1 out2 out3 nblocks st r pc stackpointer
                         returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst SQ_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SQ_BOUND_TAC THEN SQ_PRESERVED_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num`
   `pc + mlk_keccak_squeezeblocks_x4_loop1`
   `pc + mlk_keccak_squeezeblocks_x4_loop1_exit`
   `\i s. read X19 s = word_add out0 (word(r * i)) /\
          read X20 s = word_add out1 (word(r * i)) /\
          read X21 s = word_add out2 (word(r * i)) /\
          read X22 s = word_add out3 (word(r * i)) /\
          read X23 s = st /\
          read X24 s = word_add st (word 600) /\
          read X25 s = word_add st (word 400) /\
          read X26 s = word r /\
          read X27 s = word(nblocks - i) /\
          read X28 s = word_add st (word 200) /\
          read SP s = word_add stackpointer (word 192) /\
          read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 200))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x27_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x28_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          returnaddress /\
          read (memory :> bytes(out0,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S0) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out1,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S1) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out2,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S2) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out3,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S3) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(st,200)) s =
          val(keccak_squeeze i (S0:1600 word)) /\
          read (memory :> bytes(word_add st (word 200),200)) s =
          val(keccak_squeeze i (S1:1600 word)) /\
          read (memory :> bytes(word_add st (word 400),200)) s =
          val(keccak_squeeze i (S2:1600 word)) /\
          read (memory :> bytes(word_add st (word 600),200)) s =
          val(keccak_squeeze i (S3:1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--1) THEN
    SQ_NONZERO_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (2--18) THEN ARGS_32_TAC [`r:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `r * i + r <= r * nblocks` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`; LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (4--5) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (7--8) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (10--11) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC SQ_EXEC (13--14) THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L2"
      [`e:(uarch_event)list`; `read X23 s`; `read X19 s`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S0:1600 word))`; `pc:num`] 15 THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L3"
      [`e:(uarch_event)list`; `word_add (st:int64) (word 200)`;
       `word_add (out1:int64) (word (r * i))`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S1:1600 word))`; `pc:num`] 16 THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L4"
      [`e:(uarch_event)list`; `word_add (st:int64) (word 400)`;
       `word_add (out2:int64) (word (r * i))`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S2:1600 word))`; `pc:num`] 17 THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L5"
      [`e:(uarch_event)list`; `word_add (st:int64) (word 600)`;
       `word_add (out3:int64) (word (r * i))`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S3:1600 word))`; `pc:num`] 18 THEN
    ARM_STEPS_TAC SQ_EXEC (19--24) THEN
    SQ_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN NO_TAC;
      REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
        REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
        NO_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The theorem of constant time and memory safety, from the combined one.    *)
(* ------------------------------------------------------------------------- *)

(*** Weakening the pre- and postconditions of an ensures ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e out0 out1 out2 out3 nblocks st r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        PAIRWISE nonoverlapping
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_squeezeblocks_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st;
                               word r] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out0 out1 out2 out3 nblocks st r pc
                            (word_sub stackpointer (word 288)) returnaddress /\
                     memaccess_inbounds e2
                      [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
                       out3,r * nblocks; st,800;
                       word_sub stackpointer (word 288),288;
                       word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                      [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
                       out3,r * nblocks; st,800;
                       word_sub stackpointer (word 288),288]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,r * nblocks);
                memory :> bytes(out1,r * nblocks);
                memory :> bytes(out2,r * nblocks);
                memory :> bytes(out3,r * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 288),288)])`,
  MP_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `S0:1600 word`
   `read (memory :> wbytes st):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S1:1600 word`
   `read (memory :> wbytes (word_add st (word 200))):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S2:1600 word`
   `read (memory :> wbytes (word_add st (word 400))):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S3:1600 word`
   `read (memory :> wbytes (word_add st (word 600))):armstate->1600 word` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `r:num`; `S0:1600 word`;
    `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
