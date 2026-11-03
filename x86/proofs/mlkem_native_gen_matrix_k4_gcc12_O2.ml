(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generation of the ML-KEM-1024 matrix from a seed. This is the code for    *)
(* mlkem1024_gen_matrix from mlkem-native's portable C implementation        *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which copies    *)
(* the seed of 32 bytes into four buffers of 64 bytes on the stack, and then *)
(* for each row of the matrix appends the two indices of each of its four    *)
(* entries to it in a loop and samples them with mlkem_poly_rej_uniform_x4,  *)
(* and zeroes the buffers. It is verified in the whole image (see            *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x1020, using  *)
(* the theorem for mlkem_poly_rej_uniform_x4 at 0x60e0 in the image.         *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_rej_uniform_x4_gcc12_O2.ml";;

(*** The code in the image:

    1020: push   rbp
    1021: mov    rbp,rsp
    1024: push   r15
    1026: push   r14
    1028: mov    r14d,edx
    102b: push   r13
    102d: mov    r13,rdi
    1030: push   r12
    1032: push   rbx
    1033: and    rsp,0xffffffffffffffe0
    1037: sub    rsp,0x100
    103e: movdqu xmm1,XMMWORD PTR [rsi]
    1042: movdqu xmm0,XMMWORD PTR [rsi+0x10]
    1047: mov    r15,rsp
    104a: lea    r12,[rsp+0x100]
    1052: mov    rax,r15
    1055: movaps XMMWORD PTR [rax],xmm1
    1058: add    rax,0x40
    105c: movaps XMMWORD PTR [rax-0x30],xmm0
    1060: cmp    rax,r12
    1063: jne    1055 <mlkem1024_gen_matrix+0x35>
    1065: xor    ebx,ebx
    1067: mov    rax,r15
    106a: mov    esi,ebx
    106c: mov    edx,esi
    106e: mov    ecx,esi
    1070: and    edx,0x3
    1073: shr    ecx,0x2
    1076: test   r14d,r14d
    1079: mov    edi,edx
    107b: cmovne edx,ecx
    107e: cmovne ecx,edi
    1081: add    rax,0x40
    1085: add    esi,0x1
    1088: mov    BYTE PTR [rax-0x20],dl
    108b: mov    BYTE PTR [rax-0x1f],cl
    108e: cmp    rax,r12
    1091: jne    106c <mlkem1024_gen_matrix+0x4c>
    1093: lea    eax,[rbx+0x3]
    1096: mov    edi,ebx
    1098: mov    r8,r15
    109b: shr    eax,0x2
    109e: shr    edi,0x2
    10a1: shl    rax,0xb
    10a5: shl    rdi,0xb
    10a9: lea    rcx,[r13+rax*1+0x600]
    10b1: lea    eax,[rbx+0x2]
    10b4: add    rdi,r13
    10b7: shr    eax,0x2
    10ba: shl    rax,0xb
    10be: lea    rdx,[r13+rax*1+0x400]
    10c6: lea    eax,[rbx+0x1]
    10c9: add    ebx,0x4
    10cc: shr    eax,0x2
    10cf: shl    rax,0xb
    10d3: lea    rsi,[r13+rax*1+0x200]
    10db: call   60e0 <mlkem_poly_rej_uniform_x4>
    10e0: cmp    ebx,0x10
    10e3: jne    1067 <mlkem1024_gen_matrix+0x47>
    10e5: xor    eax,eax
    10e7: mov    rdi,r15
    10ea: mov    ecx,0x20
    10ef: rep    stos QWORD PTR es:[rdi],rax
    10f2: lea    rsp,[rbp-0x28]
    10f6: pop    rbx
    10f7: pop    r12
    10f9: pop    r13
    10fb: pop    r14
    10fd: pop    r15
    10ff: pop    rbp
    1100: ret
 ***)

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x1020,0x1101];;

(* ------------------------------------------------------------------------- *)
(* The seed is loaded as two 128-bit words, and stored with the two indices  *)
(* of an entry in a buffer of 64 bytes, as 34 bytes for SHAKE128.            *)
(* ------------------------------------------------------------------------- *)

let GENMAT_BYTES128_HALVES = prove
 (`!a:int64 n s:x86state.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GENMAT_BYTES_32_OF_HALVES = prove
 (`!a:int64 n s:x86state.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory s`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `16`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 340282366920938463463374607431768211456 <
                340282366920938463463374607431768211456`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `n < 2 EXP 256` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

let GENMAT_BYTES2 = prove
 (`(!a s:x86state.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes16 a) s)) /\
   (!a s:x86state.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes8 a) s) +
        256 * val(read (memory :> bytes8(word_add a (word 1))) s))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE; BYTES8_WBYTES; VAL_READ_WBYTES;
                DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let GENMAT_INPUT = prove
 (`!a:int64 (rho:byte list) x y s:x86state.
        LENGTH rho = 32 /\ x < 256 /\ y < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist rho MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist rho DIV 2 EXP 128) /\
        read (memory :> bytes(word_add a (word 32),2)) s = x + 256 * y
        ==> LENGTH(APPEND rho [word x:byte; word y]) = 34 /\
            read (memory :> bytes(a,34)) s =
            num_of_bytelist(APPEND rho [word x; word y])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,32)) s = num_of_bytelist rho`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GENMAT_BYTES_32_OF_HALVES THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The four buffers are aligned to 32 bytes within the stack frame, by AND   *)
(* with -32 after the pushes of RBP, R15, R14, R13, R12 and RBX, so their    *)
(* address depends on the stack pointer. The proof uses a variable bot for   *)
(* the address 3424 bytes below them, the bottom of the stack of             *)
(* mlkem_poly_rej_uniform_x4, which is stackpointer + (32 - k) for k =       *)
(* val(stackpointer + 3712) MOD 32, where stackpointer is the bottom of the  *)
(* 3760 bytes of the stack below the return address, with the facts about    *)
(* its alignment and the overlaps of the frame. The addresses in the frame   *)
(* are then bot plus a constant, in the form of the memory addresses of the  *)
(* simulation, to which GENMAT_NORM_TAC also puts the values in registers,   *)
(* and GENMAT_SP n is the address n bytes into the buffers.                  *)
(* ------------------------------------------------------------------------- *)

let GENMAT_FRAME_ADDRESS = prove
 (`!a:int64.
        word_sub (word_and (word_add a (word 3712))
                           (word 18446744073709551584))
                 (word 256) =
        word_add a (word(3456 - val(word_add a (word 3712)) MOD 32))`,
  let lemma = prove
   (`!x:int64. word_and x (word 18446744073709551584) =
               word_sub x (word(val x MOD 32))`,
    GEN_TAC THEN
    SUBGOAL_THEN `val(x:int64) MOD 32 = val(word_and x (word 31):int64)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];
      REWRITE_TAC[WORD_VAL] THEN
      W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]) in
  GEN_TAC THEN REWRITE_TAC[lemma] THEN
  MP_TAC(SPECL [`val(word_add a (word 3712):int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`val(word_add a (word 3712):int64) MOD 32`,`k:num`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`3456`,`x:num`; `k:num`,`y:num`]
    (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k < 32` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

let GENMAT_ALIGNED_16 = prove
 (`!x:int64. aligned 16 x <=> word_and x (word 15) = word 0`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`]);;

let GENMAT_BOT_TAC =
  ABBREV_TAC
   `bot = word_sub (word_and (word_add stackpointer (word 3712))
                             (word 18446744073709551584))
                   (word 3680):int64` THEN
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 3712))
             (word 18446744073709551584):int64 =
    word_add bot (word 3680)`
  ASSUME_TAC THENL [EXPAND_TAC "bot" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (bot:int64)` ASSUME_TAC THENL
   [EXPAND_TAC "bot" THEN REWRITE_TAC[GENMAT_ALIGNED_16] THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bot:int64 =
    word_add stackpointer
     (word(32 - val(word_add stackpointer (word 3712)) MOD 32))`
  ASSUME_TAC THENL
   [EXPAND_TAC "bot" THEN
    SUBGOAL_THEN
     `word_sub (word_and (word_add stackpointer (word 3712))
                         (word 18446744073709551584)) (word 3680):int64 =
      word_sub (word_sub (word_and (word_add stackpointer (word 3712))
                         (word 18446744073709551584)) (word 256))
               (word 3424)`
    SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[GENMAT_FRAME_ADDRESS] THEN
    MP_TAC(SPECL [`val(word_add stackpointer (word 3712):int64)`; `32`]
      MOD_LT_EQ) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`val(word_add stackpointer (word 3712):int64) MOD 32`,
             `d:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `3456 - d = (32 - d) + 3424` SUBST1_TAC THENL
     [UNDISCH_TAC `d < 32` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `bot:int64`));;

let GENMAT4_NONOV_TAC =
  SUBGOAL_THEN `val(word_add stackpointer (word 3712):int64) MOD 32 < 32`
   ASSUME_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun bth ->
    if is_eq(concl bth) && lhs(concl bth) = `bot:int64`
    then
      ASSUME_TAC(SYM bth) THEN
      MAP_EVERY (fun r ->
        SUBGOAL_THEN
         (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                          `bot:int64,3680`),r)) ASSUME_TAC THENL
         [REWRITE_TAC[bth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       [`a:int64,8192`; `seed:int64,32`; `word pc:int64,0x82a0`;
        `word_add stackpointer (word 3712):int64,56`]
    else NO_TAC);;

let GENMAT4_FRAME_TAC =
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [RSP] ,,
    (MAYCHANGE [RIP] ,,
     MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
     MAYCHANGE
      [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10;
       ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20;
       ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30;
       ZMM31] ,,
     MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
     MAYCHANGE [events]) ,,
    MAYCHANGE
     [memory :> bytes(a,8192); memory :> bytes(bot:int64,3680);
      memory :> bytes(word_add stackpointer (word 3712),48)]` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `bot:int64`
      then REWRITE_TAC[th] else NO_TAC) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC];;

let GENMAT4_SETUP_TAC =
  GENMAT_BOT_TAC THEN GENMAT4_FRAME_TAC THEN GENMAT4_NONOV_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let GENMAT_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let GENMAT_SP c =
  mk_comb(`word_add (bot:int64)`,
          mk_comb(`word:num->int64`,mk_small_numeral(3424 + c)));;

(* ------------------------------------------------------------------------- *)
(* Some forms in the simulation: the comparisons of two addresses in the     *)
(* frame, which decide the loop that copies the seed and the loop that       *)
(* stores the indices for a row, and the values stored from the low halves   *)
(* of the YMM registers, the upper halves of which are kept as their initial *)
(* values.                                                                   *)
(* ------------------------------------------------------------------------- *)

let GENMAT_PTR_SUB = prove
 (`!x:int64 a b. word_sub (word_add x (word a)) (word_add x (word b)) =
                 word_sub (word a) (word b)`,
  CONV_TAC WORD_RULE);;

let GENMAT_PTR_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th) &&
       can (find_term (fun t -> is_const t && name_of t = "word_sub"))
           (concl th)
    then CONV_RULE(REWRITE_CONV[GENMAT_PTR_SUB] THENC
                   DEPTH_CONV WORD_NUM_RED_CONV THENC NUM_REDUCE_CONV) th
    else th);;

let GENMAT_SUBWORD_JOIN = prove
 (`!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`,
  CONV_TAC WORD_BLAST);;

let GENMAT_SSE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GENMAT_SUBWORD_JOIN]);;

(*** The first address of a row as a + 2048 * i, not 2048 * i + a ***)

let GENMAT4_RDI_TAC =
  let th = prove
   (`!n. word_add (word n) (a:int64) = word_add a (word n)`,
    REWRITE_TAC[WORD_ADD_SYM]) in
  RULE_ASSUM_TAC(fun th' ->
    if can (term_match [] `read RDI s = word_add (word n) (a:int64)`)
           (concl th')
    then (try GEN_REWRITE_RULE RAND_CONV [th] th' with Failure _ -> th')
    else th');;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is 32 bytes at seed, given as a list of bytes *)
(* rho. Entry (i,j) of the matrix, the polynomial at a + 512 * (4 * i + j),  *)
(* is sampled from shake128 of rho followed by the bytes j and i, as for the *)
(* matrix in FIPS 203, or by i and j if transposed (as a 32-bit integer) is  *)
(* nonzero, which gives the transposed matrix. As for                        *)
(* mlkem_poly_rej_uniform, the theorem has the hypothesis that for some k    *)
(* there are at least 256 samples within the first 504 + 168 * k bytes of    *)
(* shake128 for each entry. The proof is by cases on whether transposed is   *)
(* zero, which decides the CMOVs in the loop for the indices, and the        *)
(* simulation goes through all the iterations of the loops. The stack is the *)
(* 3760 bytes below the return address, for the six saved registers, up to   *)
(* 31 bytes for the alignment, the 256 bytes of the buffers and the 3424     *)
(* used by mlkem_poly_rej_uniform_x4 below them.                             *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLY_REJ_UNIFORM_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup ***)

let GENMAT4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `seed:int64`; `rho:byte list`; `transposed:int64`; `k:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3760 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

(*** The inputs to SHAKE128 in the buffers ***)

let GENMAT_SEED x y =
  let b n = mk_comb(`word:num->byte`,mk_small_numeral n) in
  mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,`rho:byte list`),
          mk_list([b x; b y],`:byte`));;

let GENMAT_ADDR_CONV =
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC NUM_REDUCE_CONV;;

let GENMAT_INPUT_TAC =
  let th = CONV_RULE NUM_REDUCE_CONV GENMAT_INPUT in
  fun off x y s ->
    let sl = GENMAT_SP off and a32 = GENMAT_SP(off + 32) in
    let n = mk_small_numeral(x + 256 * y) in
    SUBGOAL_THEN
     (mk_eq(list_mk_comb(`read:(x86state,num)component->x86state->num`,
                         [mk_comb(`(:>) memory:(int64->byte,num)component->
                                   (x86state,num)component`,
                                  mk_comb(`bytes:int64#num->
                                           (int64->byte,num)component`,
                                          mk_pair(a32,`2`)));
                          s]),n))
    ASSUME_TAC THENL
     [(REWRITE_TAC[CONJUNCT1 GENMAT_BYTES2] THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) ORELSE
      (REWRITE_TAC[CONJUNCT2 GENMAT_BYTES2] THEN CONV_TAC GENMAT_ADDR_CONV THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
       CONV_TAC NUM_REDUCE_CONV);
      ALL_TAC] THEN
    MP_TAC(SPECL [sl; `rho:byte list`; mk_small_numeral x;
                  mk_small_numeral y; s] th) THEN
    ANTS_TAC THENL
     [CONV_TAC GENMAT_ADDR_CONV THEN ASM_REWRITE_TAC[];
      STRIP_TAC];;

let GENMAT_HYP_TAC i j =
  W(fun (asl,_) ->
    let cth = find (fun th ->
      concl th = `word_zx(transposed:int64):int32 = word 0` ||
      concl th = `~(word_zx(transposed:int64):int32 = word 0)`)
      (map snd asl)
    and hth = find (fun th ->
      match concl th with
        Comb(Const("!",_),Abs(Var("i",_),_)) -> true | _ -> false)
      (map snd asl) in
    let th1 = SPECL [mk_small_numeral i; mk_small_numeral j] hth in
    let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
    ASSUME_TAC(REWRITE_RULE[cth] th2));;

(*** The results, in the form of the specification ***)

let GENMAT_TOBYTES_TAC =
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
    MATCH_MP REJ_BYTES16_OF_WORDLIST o check
     (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
      concl)));;

let GENMAT_FINAL1_TAC =
  W(fun (_,w) ->
    let l = rand w in
    let lth = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l),`256`) in
    SUBGOAL_THEN lth ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                  ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME lth)] THEN
    MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN REWRITE_TAC[ASSUME lth] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[]);;

let GENMAT_FINAL_TAC =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  GENMAT_FINAL1_TAC;;

(*** The simulation in each case, transposed or not ***)

let GENMAT4_CASE_TAC tr =
  let st n = mk_var("s"^string_of_int n,`:x86state`) in
  let xy e = let i = e / 4 and j = e mod 4 in if tr then (i,j) else (j,i) in
  let seed e = let x,y = xy e in GENMAT_SEED x y in
  let rest = [`k:num`; `pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let args5 = [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
               `read R8 s`] in
  (if tr then
     SUBGOAL_THEN
      `~(val(word_zx(word_zx(word_zx(transposed:int64):int32):int64):
             int32) = 0)`
     ASSUME_TAC THENL
      [REWRITE_TAC[VAL_EQ_0] THEN
       UNDISCH_TAC `~(word_zx(transposed:int64):int32 = word 0)` THEN
       CONV_TAC WORD_BLAST;
       ALL_TAC]
   else ALL_TAC) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The four copies of the seed ***)

  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (1--10) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 3712))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (11--16) THEN
  GENMAT_NORM_TAC THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((17 + 5 * m)--(19 + 5 * m)) THEN
    GENMAT_NORM_TAC THEN GENMAT_SSE_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC [20 + 5 * m] THEN
    GENMAT_PTR_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC [21 + 5 * m])
   (0--3) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC [37] THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 4) (e mod 4)) (0--15) THEN

  (*** Each row of four entries, the indices and the call ***)

  MAP_EVERY (fun g ->
    let s0 = 38 + 80 * g in
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (s0--(s0 + 1)) THEN
    MAP_EVERY (fun m ->
      X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
       ((s0 + 2 + 14 * m)--(s0 + 14 + 14 * m)) THEN
      GENMAT_NORM_TAC THEN GENMAT_PTR_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
       [s0 + 15 + 14 * m])
     (0--3) THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((s0 + 58)--(s0 + 76)) THEN
    GENMAT_NORM_TAC THEN GENMAT4_RDI_TAC THEN
    MAP_EVERY (fun m -> let x,y = xy (4 * g + m) in
                        GENMAT_INPUT_TAC (64 * m) x y (st(s0 + 76)))
     (0--3) THEN
    LOCAL_POLY_REJ_UNIFORM_X4_TAC
     (args5 @ map seed ((4 * g)--(4 * g + 3)) @ rest) (s0 + 77) THEN
    GENMAT_NORM_TAC THEN GENMAT_TOBYTES_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((s0 + 78)--(s0 + 79)))
   (0--3) THEN

  (*** Zeroing the buffers and the return ***)

  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (358--369) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN GENMAT_FINAL_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a seed (rho:byte list) transposed k pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH rho = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                           (MAP (word_zx:12 word->16 word)
                             (wordlist_of_num (336 + 112 * k)
                               (num_of_bytelist
                                 (list_of_seq
                                   (shake128
                                     (APPEND rho
                                       (if word_zx transposed = (word 0:int32)
                                        then [word j; word i]
                                        else [word i; word j])))
                                   (504 + 168 * k))))))) /\
        nonoverlapping (a,8192) (word_sub stackpointer (word 3760),3768) /\
        ALLPAIRS nonoverlapping
         [(a,8192); (word_sub stackpointer (word 3760),3768)]
         [(seed,32); (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x1020) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed; transposed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist rho)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i j. i < 4 /\ j < 4
                        ==> wordlist_from_memory
                             (word_add a (word(512 * (4 * i + j))),256) s =
                            SUB_LIST(0,256)
                             (FILTER (\x. val x < 3329)
                               (MAP (word_zx:12 word->16 word)
                                 (wordlist_of_num (336 + 112 * k)
                                   (num_of_bytelist
                                     (list_of_seq
                                       (shake128
                                         (APPEND rho
                                           (if word_zx transposed =
                                               (word 0:int32)
                                            then [word j; word i]
                                            else [word i; word j])))
                                       (504 + 168 * k)))))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,8192);
                memory :> bytes(word_sub stackpointer (word 3760),3760)])`,
  GENMAT4_INTRO_TAC THEN GENMAT4_SETUP_TAC THEN
  ASM_CASES_TAC `word_zx(transposed:int64):int32 = word 0` THENL
   [GENMAT4_CASE_TAC false; GENMAT4_CASE_TAC true]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses, rho and the flag, through the samples of each entry, which are *)
(* public. They are given by cases on the flag, which gives the order of the *)
(* indices, and the address bot is expanded in them at the end by            *)
(* GENMAT_UNBOT_TAC, since it is not an argument of the template.            *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let GENMAT_SAFE_TEMPLATE =
 `\(a:int64) (seed:int64) (rho:byte list) (transposed:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   if word_zx transposed = (word 0:int32)
   then f_ev_n a seed rho transposed pc stackpointer returnaddress
   else f_ev_t a seed rho transposed pc stackpointer returnaddress
   :(uarch_event)list`;;

let GENMAT_SAFE_ALLOWED =
  [`pc:num`; `a:int64`; `seed:int64`; `rho:byte list`; `transposed:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let GENMAT4_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_X4" THEN
  CONCRETIZE_F_EVENTS_TAC GENMAT_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GENMAT4_INTRO_TAC THEN GENMAT4_SETUP_TAC;;

let GENMAT4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GENMAT_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let GENMAT_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64` &&
       is_binary "word_add" (lhs(concl th))
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

let GENMAT4_SAFE_CASE_TAC tr =
  let st n = mk_var("s"^string_of_int n,`:x86state`) in
  let xy e = let i = e / 4 and j = e mod 4 in if tr then (i,j) else (j,i) in
  let seed e = let x,y = xy e in GENMAT_SEED x y in
  let rest = [`k:num`; `pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let args5 = [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
               `read RDX s`; `read RCX s`; `read R8 s`] in
  (if tr then
     SUBGOAL_THEN
      `~(val(word_zx(word_zx(word_zx(transposed:int64):int32):int64):
             int32) = 0)`
     ASSUME_TAC THENL
      [REWRITE_TAC[VAL_EQ_0] THEN
       UNDISCH_TAC `~(word_zx(transposed:int64):int32 = word 0)` THEN
       CONV_TAC WORD_BLAST;
       ALL_TAC]
   else ALL_TAC) THEN
  FIRST_ASSUM(fun th ->
    if concl th = `word_zx(transposed:int64):int32 = word 0` ||
       concl th = `~(word_zx(transposed:int64):int32 = word 0)`
    then REWRITE_TAC[th] else NO_TAC) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (1--10) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 3712))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (11--16) THEN
  GENMAT_NORM_TAC THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((17 + 5 * m)--(19 + 5 * m)) THEN
    GENMAT_NORM_TAC THEN GENMAT_SSE_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC [20 + 5 * m] THEN
    GENMAT_PTR_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC [21 + 5 * m])
   (0--3) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC [37] THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 4) (e mod 4)) (0--15) THEN
  MAP_EVERY (fun g ->
    let s0 = 38 + 80 * g in
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (s0--(s0 + 1)) THEN
    MAP_EVERY (fun m ->
      X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
       ((s0 + 2 + 14 * m)--(s0 + 14 + 14 * m)) THEN
      GENMAT_NORM_TAC THEN GENMAT_PTR_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
       [s0 + 15 + 14 * m])
     (0--3) THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((s0 + 58)--(s0 + 76)) THEN
    GENMAT_NORM_TAC THEN GENMAT4_RDI_TAC THEN
    MAP_EVERY (fun m -> let x,y = xy (4 * g + m) in
                        GENMAT_INPUT_TAC (64 * m) x y (st(s0 + 76)))
     (0--3) THEN
    GENMAT4_SAFE_CALL_TAC "H_X4"
     (args5 @ map seed ((4 * g)--(4 * g + 3)) @ rest) (s0 + 77) THEN
    GENMAT_NORM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC
     ((s0 + 78)--(s0 + 79)))
   (0--3) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_EXEC (358--369) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  GENMAT_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
   forall e a seed (rho:byte list) transposed k pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH rho = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                           (MAP (word_zx:12 word->16 word)
                             (wordlist_of_num (336 + 112 * k)
                               (num_of_bytelist
                                 (list_of_seq
                                   (shake128
                                     (APPEND rho
                                       (if word_zx transposed = (word 0:int32)
                                        then [word j; word i]
                                        else [word i; word j])))
                                   (504 + 168 * k))))))) /\
        nonoverlapping (a,8192) (word_sub stackpointer (word 3760),3768) /\
        ALLPAIRS nonoverlapping
         [(a,8192); (word_sub stackpointer (word 3760),3768)]
         [(seed,32); (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x1020) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed; transposed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist rho /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a seed rho transposed pc
                            (word_sub stackpointer (word 3760))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; a,8192;
                       word_sub stackpointer (word 3760),3768;
                       word(pc + 0x80c0),192]
                      [a,8192; word_sub stackpointer (word 3760),3760]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,8192);
                memory :> bytes(word_sub stackpointer (word 3760),3760)])`,
  GENMAT4_SAFE_INTRO_TAC THEN
  ASM_CASES_TAC `word_zx(transposed:int64):int32 = word 0` THENL
   [GENMAT4_SAFE_CASE_TAC false; GENMAT4_SAFE_CASE_TAC true]);;
