(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into four Keccak states. This is the code for                *)
(* mlk_keccakf1600x4_xor_bytes_c from mlkem-native's portable C              *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md). It is what mlkem_keccakf1600x4_xor_bytes is in   *)
(* the separately compiled gcc12_O2 build, with the specification of that    *)
(* function, with three differences. The compiler has inlined the four       *)
(* calls of mlkem_keccakf1600_xor_bytes into it as four loops, which do not  *)
(* test for len = 0 (all its callers pass a nonzero len), so len must be     *)
(* nonzero here. The code is a leaf function without a stack frame. And it   *)
(* writes only the registers X0-X3 and X5-X9 (and the flags), so the frame   *)
(* is that exact list rather than the one of the ABI: its caller, in         *)
(* mlk_keccak_absorb_once_x4, keeps X4 and X10-X13 across the calls.         *)
(* Each loop is proved as a lemma, with the specification of                 *)
(* mlkem_keccakf1600_xor_bytes for its state, and the function follows from  *)
(* the four lemmas. It is verified in the whole image (see libmlkem.ml).     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_xor_bytes.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_keccakf1600x4_xor_bytes_c:
     +0x0  add     x5, x0, w5, uxtw
  // inlined: keccakf1600_xor_bytes
  in_keccakf1600_xor_bytes_1:
     +0x4  mov     w6, w6
     +0x8  mov     x7, #0x0
     +0xc  nop
  loop1:
    +0x10  ldrb    w0, [x5, x7]
    +0x14  mov     x8, x7
    +0x18  ldrb    w9, [x1, x7]
    +0x1c  eor     w0, w0, w9
    +0x20  strb    w0, [x5, x7]
    +0x24  add     x7, x7, #0x1
  loop1_test:
    +0x28  cmp     x6, x7
  loop1_back:
    +0x2c  b.ne    loop1
  loop1_exit:
    +0x30  add     x7, x5, #0xc8
    +0x34  mov     x1, #0x0
  loop2: in_keccakf1600_xor_bytes_1_end:
  in_keccakf1600_xor_bytes_2:
    +0x38  ldrb    w6, [x7, x1]
    +0x3c  cmp     x8, x1
    +0x40  ldrb    w9, [x2, x1]
    +0x44  eor     w6, w6, w9
    +0x48  strb    w6, [x7, x1]
  loop2_test:
    +0x4c  add     x1, x1, #0x1
  loop2_back:
    +0x50  b.ne    loop2
  loop2_exit:
    +0x54  add     x6, x5, #0x190
    +0x58  mov     x1, #0x0
    +0x5c  nop
  loop3: in_keccakf1600_xor_bytes_2_end:
  in_keccakf1600_xor_bytes_3:
    +0x60  ldrb    w2, [x6, x1]
    +0x64  cmp     x8, x1
    +0x68  ldrb    w7, [x3, x1]
    +0x6c  eor     w2, w2, w7
    +0x70  strb    w2, [x6, x1]
  loop3_test:
    +0x74  add     x1, x1, #0x1
  loop3_back:
    +0x78  b.ne    loop3
  loop3_exit:
    +0x7c  add     x5, x5, #0x258
    +0x80  mov     x0, #0x0
    +0x84  nop
  loop4: in_keccakf1600_xor_bytes_3_end:
  in_keccakf1600_xor_bytes_4:
    +0x88  ldrb    w2, [x5, x0]
    +0x8c  cmp     x8, x0
    +0x90  ldrb    w3, [x4, x0]
    +0x94  eor     w2, w2, w3
    +0x98  strb    w2, [x5, x0]
  loop4_test:
    +0x9c  add     x0, x0, #0x1
  loop4_back:
    +0xa0  b.ne    loop4
  // inlined: (not inlined)
  loop4_exit: ret:
  in_keccakf1600_xor_bytes_4_end:
    +0xa4  ret
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_keccakf1600x4_xor_bytes_c"];;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the four loops. The first goes from the entry of the       *)
(* function to the end of the first loop, which keeps the last index in X8.  *)
(* The others go from the head of a loop, with the pointer to its state      *)
(* already computed, to the head of the next loop (or the return), and       *)
(* compare the counter with X8. They are stated by one function from the     *)
(* labels, the registers read and written and the address of the state, and  *)
(* the last three are proved by one function. The state of the loop is at    *)
(* a + 200 * k, and X5 keeps a + off, from which the pointers are computed.  *)
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

(*** The first loop ***)

let XOR_LOOP1_STMT = xor_lemma_stmt
  "mlk_keccakf1600x4_xor_bytes_c" "mlk_keccakf1600x4_xor_bytes_c_loop1_exit"
  "a"
  "read X0 s = a /\\ read X1 s = d /\\ read X5 s = word off /\\
                  read X6 s = word len"
  "read X5 s = word_add a (word off) /\\ read X6 s = word len /\\
                  read X7 s = word len /\\ read X8 s = word (len - 1)"
  "X0; X5; X6; X7; X8; X9";;

let X4X_EXEC = MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_EXEC;;

let XOR_LOOP1 = prove(XOR_LOOP1_STMT,
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`; `off:num`; `len:num`;
                       `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst X4X_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `len:num` `pc + mlk_keccakf1600x4_xor_bytes_c_loop1`
   `pc + mlk_keccakf1600x4_xor_bytes_c_loop1_exit`
   `\i s. read X5 s = word_add a (word off) /\ read X1 s = d /\
          read X6 s = word len /\ read X7 s = word i /\
          (~(i = 0) ==> read X8 s = word (i - 1)) /\
          read (memory :> bytes(d,len)) s = m /\
          !j. j < 200
              ==> read (memory :> bytes8(word_add a (word j))) s =
                  word_subword
                   (word_xor (S:1600 word)
                     (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                   (8 * j,8)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Entry: the argument registers, and the zero-extended off and len ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC X4X_EXEC (1--4) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
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
    ARM_STEPS_TAC X4X_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=>
      i + 1 < len`
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

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:int64`; `S:1600 word`; `off:num`; `len:num`; `d:int64`;
                   `m:num`; `s0:armstate`] XOR_BYTES_FINAL) THEN
    ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600]]);;

(*** The other loops: the state is at a + k, and X5 holds a + off ***)

let xorB_prove stmt lab1 lab2 k inv_regs nexit =
  let st_addr = Printf.sprintf "word_add a (word %s):int64" k in
  let sn = Printf.sprintf "s%d" nexit in
  let kk = Printf.sprintf "%s + (off + i) = off + %s + i" k k in
  prove(stmt,
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`; `off:num`; `len:num`;
                       `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst X4X_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `len:num` (parse_term ("pc + "^lab1))
   (parse_term ("pc + "^lab2))
   (parse_term (Printf.sprintf
   "\\i s. %s /\\
          read (memory :> bytes(d,len)) s = m /\\
          !j. j < 200
              ==> read (memory :> bytes8(word_add a (word (%s + j)))) s =
                  word_subword
                   (word_xor (S:1600 word)
                     (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                   (8 * j,8)" (inv_regs "i") k)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** At the head of the loop already: only the bytes of the state ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0; word_subword] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [parse_term st_addr; `200`; `val(S:1600 word)`; `j:num`;
                   `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];

    (*** The loop body, for byte off + i of the state, and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `off + i < 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `bytes8` (concl th) then
        ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term kk)]
          (MP (SPEC `off + i` th) (ASSUME `off + i < 200`))) THEN
        ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `off + i` th)
      else failwith "XOR_BYTES_RESTRICT_RULE") THEN
    MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC X4X_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word (len - 1)) (word i):int64) = 0) <=> i + 1 < len`
    SUBST_ALL_TAC THENL
     [MATCH_MP_TAC XOR_LAST_FLAG THEN ASM_REWRITE_TAC[] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[XOR_BYTES_STEP] THEN
    ASM_CASES_TAC `j = off + i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[ARITH_RULE (parse_term kk)] THEN
      ASM_REWRITE_TAC[] THEN
      W(fun (_,w) -> SPEC_TAC(lhand(rand w),`b1:byte`) THEN
                     SPEC_TAC(rand(rand w),`b2:byte`)) THEN
      REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
      ASM_SIMP_TAC[]];

    (*** The loop exit, with the whole state ***)

    ENSURES_INIT_TAC "s0" THEN
    (if nexit > 0 then ARM_STEPS_TAC X4X_EXEC (1--nexit) else ALL_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [parse_term st_addr; `S:1600 word`; `off:num`; `len:num`;
                   `d:int64`; `m:num`; parse_term (sn^":armstate")]
                  XOR_BYTES_FINAL) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600]]);;

let XOR_LOOP2_STMT = xor_lemma_stmt
  "mlk_keccakf1600x4_xor_bytes_c_loop2" "mlk_keccakf1600x4_xor_bytes_c_loop3"
  "word_add a (word 200)"
  "read X7 s = word_add (word_add a (word off)) (word 200) /\\
   read X1 s = word 0 /\\ read X5 s = word_add a (word off) /\\
   read X2 s = d /\\ read X8 s = word (len - 1)"
  "read X1 s = word 0 /\\ read X5 s = word_add a (word off) /\\
   read X6 s = word_add (word_add a (word off)) (word 400) /\\
   read X8 s = word (len - 1)"
  "X1; X6; X7; X9";;

let XOR_LOOP2 = xorB_prove XOR_LOOP2_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop2"
  "mlk_keccakf1600x4_xor_bytes_c_loop2_exit" "200"
  (fun i -> "read X7 s = word_add (word_add a (word off)) (word 200) /\\
             read X1 s = word "^i^" /\\ read X5 s = word_add a (word off) /\\
             read X2 s = d /\\ read X8 s = word (len - 1)") 3;;

let XOR_LOOP3_STMT = xor_lemma_stmt
  "mlk_keccakf1600x4_xor_bytes_c_loop3" "mlk_keccakf1600x4_xor_bytes_c_loop4"
  "word_add a (word 400)"
  "read X6 s = word_add (word_add a (word off)) (word 400) /\\
   read X1 s = word 0 /\\ read X5 s = word_add a (word off) /\\
   read X3 s = d /\\ read X8 s = word (len - 1)"
  "read X0 s = word 0 /\\
   read X5 s = word_add (word_add a (word off)) (word 600)"
  "X0; X1; X2; X5; X7";;

let XOR_LOOP3 = xorB_prove XOR_LOOP3_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop3"
  "mlk_keccakf1600x4_xor_bytes_c_loop3_exit" "400"
  (fun i -> "read X6 s = word_add (word_add a (word off)) (word 400) /\\
             read X1 s = word "^i^" /\\ read X5 s = word_add a (word off) /\\
             read X3 s = d /\\ read X8 s = word (len - 1)") 3;;

let XOR_LOOP4_STMT = xor_lemma_stmt
  "mlk_keccakf1600x4_xor_bytes_c_loop4" "mlk_keccakf1600x4_xor_bytes_c_loop4_exit"
  "word_add a (word 600)"
  "read X5 s = word_add (word_add a (word off)) (word 600) /\\
   read X0 s = word 0 /\\ read X4 s = d /\\ read X8 s = word (len - 1)"
  "read X0 s = word len"
  "X0; X2; X3";;

let XOR_LOOP4 = xorB_prove XOR_LOOP4_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop4"
  "mlk_keccakf1600x4_xor_bytes_c_loop4_exit" "600"
  (fun i -> "read X5 s = word_add (word_add a (word off)) (word 600) /\\
             read X0 s = word "^i^" /\\ read X4 s = d /\\
             read X8 s = word (len - 1)") 0;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states, each a 1600-bit word as for           *)
(* mlkem_keccakf1600_xor_bytes, are consecutive in memory. The data for the  *)
(* states, which are only read, may overlap, e.g. all be the same.           *)
(* ------------------------------------------------------------------------- *)

(*** The pointers X5 + 200 etc. in the form that the lemmas state them ***)

let X4X_ADDR_THMS = map (fun k ->
  prove(subst [mk_small_numeral k,`k:num`]
   `word_add (word_add a (word off)) (word k):int64 =
    word_add a (word (off + k))`,
   REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC])) [200; 400; 600];;

let X4X_LOOP_TAC lemma n dv sv mv =
  RULE_ASSUM_TAC(REWRITE_RULE X4X_ADDR_THMS) THEN
  KECCAK_STATE_WBYTES_TAC sv THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,X4X_EXEC,0x0,
    mlkem_native_libmlkem_gcc12_O2_mono_mc,lemma)
   [`a:int64`; dv; `off:num`; `len:num`; sv; mv; `pc:num`] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) m0 m1 m2 m3 pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\ ~(len = 0) /\
        ALLPAIRS nonoverlapping
         [(a,800)]
         [(word pc,libmlkem_size); (d0,len); (d1,len); (d2,len); (d3,len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccakf1600x4_xor_bytes_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                  read (memory :> bytes(d0,len)) s = m0 /\
                  read (memory :> bytes(d1,len)) s = m1 /\
                  read (memory :> bytes(d2,len)) s = m2 /\
                  read (memory :> bytes(d3,len)) s = m3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s =
                  word_xor S0 (word(2 EXP (8 * off) * m0)) /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  word_xor S1 (word(2 EXP (8 * off) * m1)) /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  word_xor S2 (word(2 EXP (8 * off) * m2)) /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  word_xor S3 (word(2 EXP (8 * off) * m3)))
             (MAYCHANGE [PC; X0; X1; X2; X3; X5; X6; X7; X8; X9] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,800)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X4X_LOOP_TAC XOR_LOOP1 1 `d0:int64` `S0:1600 word` `m0:num` THEN
  ARM_STEPS_TAC X4X_EXEC (2--3) THEN
  X4X_LOOP_TAC XOR_LOOP2 4 `d1:int64` `S1:1600 word` `m1:num` THEN
  X4X_LOOP_TAC XOR_LOOP3 5 `d2:int64` `S2:1600 word` `m2:num` THEN
  X4X_LOOP_TAC XOR_LOOP4 6 `d3:int64` `S3:1600 word` `m3:num` THEN
  ARM_STEPS_TAC X4X_EXEC (7--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
