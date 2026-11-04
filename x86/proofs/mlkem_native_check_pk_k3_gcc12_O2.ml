(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The modulus check of an ML-KEM-768 encapsulation key. This is the code    *)
(* for mlkem768_check_pk from mlkem-native's portable C implementation       *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which decodes   *)
(* the vector of the key from its first 1152 bytes into a buffer on the      *)
(* stack, reduces it, encodes it again into another buffer, compares the     *)
(* result in constant time with the key, and zeroes the buffers. Its code is *)
(* that of mlkem512_check_pk apart from the sizes. It is verified in the     *)
(* whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at       *)
(* address 0x6cc0, using the theorems for mlkem768_polyvec_frombytes at      *)
(* 0x7530, mlkem768_polyvec_reduce at 0x76f0 and mlkem768_polyvec_tobytes at *)
(* 0x74f0 in the image.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_polyvec_frombytes_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_reduce_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_tobytes_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;
needs "x86/proofs/consttime.ml";;

(*** The code in the image:

    6cc0: push   rbp
    6cc1: mov    rsi,rdi
    6cc4: mov    rbp,rsp
    6cc7: push   r13
    6cc9: mov    r13,rdi
    6ccc: push   r12
    6cce: push   rbx
    6ccf: and    rsp,0xffffffffffffffe0
    6cd3: sub    rsp,0xa80
    6cda: lea    rbx,[rsp+0x480]
    6ce2: mov    r12,rsp
    6ce5: mov    rdi,rbx
    6ce8: call   7530 <mlkem768_polyvec_frombytes>
    6ced: mov    rdi,rbx
    6cf0: call   76f0 <mlkem768_polyvec_reduce>
    6cf5: mov    rsi,rbx
    6cf8: mov    rdi,r12
    6cfb: call   74f0 <mlkem768_polyvec_tobytes>
    6d00: pxor   xmm2,xmm2
    6d04: xor    eax,eax
    6d06: movdqa xmm0,xmm2
    6d0a: nop    WORD PTR [rax+rax*1+0x0]
    6d10: movdqu xmm1,XMMWORD PTR [r13+rax*1+0x0]
    6d17: pxor   xmm1,XMMWORD PTR [r12+rax*1]
    6d1d: add    rax,0x10
    6d21: por    xmm0,xmm1
    6d25: pxor   xmm2,xmm1
    6d29: cmp    rax,0x480
    6d2f: jne    6d10 <mlkem768_check_pk+0x50>
    6d31: movdqa xmm1,xmm2
    6d35: psrldq xmm1,0x8
    6d3a: pxor   xmm2,xmm1
    6d3e: movdqa xmm1,xmm2
    6d42: psrldq xmm1,0x4
    6d47: pxor   xmm2,xmm1
    6d4b: movdqa xmm1,xmm2
    6d4f: psrldq xmm1,0x2
    6d54: pxor   xmm2,xmm1
    6d58: movdqa xmm1,xmm2
    6d5c: psrldq xmm1,0x1
    6d61: pxor   xmm2,xmm1
    6d65: movdqa xmm1,xmm0
    6d69: psrldq xmm1,0x8
    6d6e: movd   edx,xmm2
    6d72: por    xmm0,xmm1
    6d76: movdqa xmm1,xmm0
    6d7a: psrldq xmm1,0x4
    6d7f: por    xmm0,xmm1
    6d83: movdqa xmm1,xmm0
    6d87: psrldq xmm1,0x2
    6d8c: por    xmm0,xmm1
    6d90: movdqa xmm1,xmm0
    6d94: psrldq xmm1,0x1
    6d99: por    xmm0,xmm1
    6d9d: movd   eax,xmm0
    6da1: movzx  eax,al
    6da4: neg    eax
    6da6: sar    eax,0x10
    6da9: xor    eax,edx
    6dab: cmp    al,dl
    6dad: mov    rdi,r12
    6db0: mov    ecx,0x90
    6db5: sete   dl
    6db8: xor    eax,eax
    6dba: rep    stos QWORD PTR es:[rdi],rax
    6dbd: movzx  edx,dl
    6dc0: lea    edx,[rdx*4-0x4]
    6dc7: mov    ecx,0xc0
    6dcc: mov    rdi,rbx
    6dcf: rep    stos QWORD PTR es:[rdi],rax
    6dd2: lea    rsp,[rbp-0x18]
    6dd6: mov    eax,edx
    6dd8: pop    rbx
    6dd9: pop    r12
    6ddb: pop    r13
    6ddd: pop    rbp
    6dde: ret
 ***)

let MLKEM_NATIVE_CHECK_PK_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x6cc0,0x6ddf];;

(* ------------------------------------------------------------------------- *)
(* The reduced vector, as a list of 16-bit coefficients for the encoding,    *)
(* and the equivalence of its encoding with the key with the 12-bit fields   *)
(* of the key being below 3329.                                              *)
(* ------------------------------------------------------------------------- *)

let CHECK_PK_BYTES16_LIST = prove
 (`!a n (f:num->int16) s:x86state.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                list_of_seq; num_of_wordlist];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE; list_of_seq] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              NUM_OF_WORDLIST_SING; DIMINDEX_16] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let CHECK_PK_IVAL_WORD = prove
 (`!f. f < 32768 ==> ival(word f:int16) = &f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `f < 32768 ==> f < 65536`]);;

let CHECK_PK_REDUCED = prove
 (`!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word f:int16) = &f` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CHECK_PK_IVAL_WORD THEN UNDISCH_TAC `f < 2 EXP 12` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_REM]) THEN
  ONCE_REWRITE_TAC[GSYM IVAL_EQ] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CHECK_PK_IVAL_WORD THEN
  MP_TAC(SPECL [`f:num`; `3329`] MOD_LT_EQ) THEN ARITH_TAC);;

let CHECK_PK_LIST_PROPS = prove
 (`!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM ALL_EL] THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; VAL_WORD; DIMINDEX_16] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`(g:num->num) i`; `3329`] MOD_LT_EQ) THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 3329 ==> x < 65536`] THEN ARITH_TAC);;

let CHECK_PK_REENCODE = prove
 (`!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF] THEN
  SUBGOAL_THEN
   `!x. word_zx(word(x MOD 3329):int16):12 word = word(x MOD 3329)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `x MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 65536`];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`; LENGTH_LIST_OF_SEQ]
     (ISPECL [`list_of_seq (\x. word((n DIV 2 EXP (12 * x)) MOD 2 EXP 12 MOD
                                     3329):12 word) l`; `i:num`]
             NUM_OF_WORDLIST_EL)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> is_eq(concl th) && lhs(concl th) = `n:num`)) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SPEC_TAC(`(n DIV 2 EXP (12 * i)) MOD 4096`,`d:num`) THEN GEN_TAC THEN
    MP_TAC(ARITH_RULE `d MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4096`] THEN MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`]
    (ISPECL [`l:num`; `n:num`]
      (INST_TYPE [`:12`,`:N`] NUM_OF_WORDLIST_OF_NUM_EQ_SELF))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th] THEN
                       ASSUME_TAC th) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_WORDLIST_OF_NUM; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC(ISPECL [`wordlist_of_num l n:(12 word)list`; `i:num`]
                EL_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_MOD_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The comparison, 16 bytes at a time in the low halves of YMM registers:    *)
(* the bytes of the key and of the encoding XORed together are ORed into one *)
(* accumulator (and XORed into another, which does not affect the result),   *)
(* which is zero if and only if the prefixes so far are equal. The result is *)
(* computed from the bytes of the accumulators ORed (and XORed) together, as *)
(* for mlkem512_check_sk.                                                    *)
(* ------------------------------------------------------------------------- *)

let CHECK_PK_BYTES128 = prove
 (`!a l k n s:x86state.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `128 * k = 8 * 16 * k`; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_MOD; MOD_MOD_REFL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let CHECK_PK_MOD_STEP = prove
 (`!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `128 * (k + 1) = 128 * k + 128`; EXP_ADD] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LEXICOGRAPHIC_EQ o lhand o snd) THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

let CHECK_PK_OR_STEP = prove
 (`!q:int128 a b.
        word_or q
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456))) =
        word 0 <=>
        q = word 0 /\ a MOD 2 EXP 128 = b MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let CHECK_PK_BYTE_MOD = prove
 (`!x:N word. word(val x MOD 256):M word = word_zx(word_zx x:byte)`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  MP_TAC(SPEC `val(x:N word)` (ARITH_RULE `!n. n MOD 256 < 256`)) THEN
  SIMP_TAC[MOD_LT]);;

let CHECK_PK_SUBWORD_JOIN = prove
 (`!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, by AND with   *)
(* -32 after the pushes of RBP, R13, R12 and RBX, with RBP as a frame        *)
(* pointer. As for mlkem512_check_sk, the proof uses a variable bot for the  *)
(* address 40 bytes below the buffers, the bottom of the stacks of the       *)
(* callees, which is stackpointer + delta for delta = 32 -                   *)
(* val(stackpointer + 2760) MOD 32, where stackpointer is the bottom of the  *)
(* 2792 bytes of the stack below the return address, with the facts about    *)
(* the frame proved by BITBLAST through the form of delta as a word,         *)
(* CHECK_PK_DELTA. The encoding is then at bot + 40 and the vector at        *)
(* bot + 1192. The comparison uses SSE instructions, which keep the upper    *)
(* halves of the YMM registers, so those are given names after the calls.    *)
(* ------------------------------------------------------------------------- *)

let CHECK_PK_DELTA = prove
 (`!x:int64. 32 - val x MOD 32 =
             val(word_sub (word 32) (word_and x (word 31)):int64)`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(word_and (x:int64) (word 31)) = val x MOD 32`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`val(x:int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let CHECK_PK_BOT_TAC =
  ABBREV_TAC
   `delta = 32 - val(word_add (stackpointer:int64) (word 2760)) MOD 32` THEN
  SUBGOAL_THEN `delta <= 32` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bot = word_add (stackpointer:int64) (word delta)` THEN
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 2760))
             (word 18446744073709551584):int64 =
    word_add bot (word 2728)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN
    REWRITE_TAC[CHECK_PK_DELTA] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC];;

let CHECK_PK_NONOV_TAC =
  FIRST_ASSUM(fun bth ->
    if is_eq(concl bth) && rhs(concl bth) = `bot:int64`
    then
      MAP_EVERY (fun r ->
        SUBGOAL_THEN
         (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                          `bot:int64,2728`),r)) ASSUME_TAC THENL
         [REWRITE_TAC[SYM bth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       [`pk:int64,1152`; `word pc:int64,0x82a0`;
        `word_add stackpointer (word 2760):int64,40`]
    else NO_TAC);;

let CHECK_PK_FRAME_TAC =
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
     [memory :> bytes(bot:int64,2728);
      memory :> bytes(word_add stackpointer (word 2760),32)]` THEN
  CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC];;

let CHECK_PK_SETUP_TAC =
  CHECK_PK_BOT_TAC THEN CHECK_PK_FRAME_TAC THEN CHECK_PK_NONOV_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13`;;

let CHECK_PK_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let CHECK_PK_RSP_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 2760))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

let CHECK_PK_YMM_TAC st =
  MAP_EVERY (fun (v,r) ->
    ABBREV_TAC(mk_eq(mk_var(v,`:int256`),
      list_mk_comb(`read:(x86state,int256)component->x86state->int256`,
                   [r; st]))))
   [("y0",`YMM0`); ("y1",`YMM1`); ("y2",`YMM2`)];;

(* ------------------------------------------------------------------------- *)
(* The proofs. CHECK_PK_TAC does the three proofs below, with a flag for the *)
(* events and one for the data, which are not needed for the safety proof.   *)
(* The calls use the theorems for the callees of the same kind, assumed as   *)
(* usual for the safety and combined ones, and at the end of each part of    *)
(* the proof the frame variables are expanded in the events by               *)
(* CHECK_PK_UNBOT_TAC, since they are not arguments of f_events. The         *)
(* invariant of the loop has the counter and the frame, and with the data    *)
(* also the value of the accumulator in terms of the prefixes of the key and *)
(* of the encoding.                                                          *)
(* ------------------------------------------------------------------------- *)

(*** The calls ***)

let CHECK_PK_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `bot:int64`];;

let CHECK_PK_CALL_TAC exec (events,data) (th,name) (args,d) n =
  let ilist =
    (if events then [`e:(uarch_event)list`] else []) @ args @
    (if data then [d] else []) @
    [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] in
  if not events then
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mc,exec,
      0x0,mlkem_native_libmlkem_gcc12_O2_mc,th) ilist n
  else
    REMOVE_THEN name (fun safety_th ->
      X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mlkem_native_libmlkem_gcc12_O2_mc,exec,
         0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
        ilist n THENL
       [EXISTS_E2_TAC (ref CHECK_PK_SAFE_ALLOWED);
        LABEL_TAC name safety_th]);;

let CHECK_PK_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `delta:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

(*** The facts in the loop, with the saved registers ***)

let CHECK_PK_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              768`;;

let CHECK_PK_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                768))`;;

let CHECK_PK_FRAME =
 `read R13 s = pk /\
  read R12 s = word_add bot (word 40) /\
  read RBX s = word_add bot (word 1192) /\
  read RBP s = word_add stackpointer (word 2784) /\
  read (memory :> bytes64 (word_add stackpointer (word 2760))) s =
  rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2768))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2776))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2784))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2792))) s =
  returnaddress /\
  ~read DF s`;;

let CHECK_PK_INV data =
  list_mk_abs([`i:num`; `s:x86state`],
   list_mk_conj([`read RAX s = word(16 * i)`; CHECK_PK_FRAME] @
    (if data then
      [vsubst [CHECK_PK_M,`M:num`]
        `read (memory :> bytes(pk,1152)) s = n /\
         read (memory :> bytes(word_add bot (word 40),1152)) s = M /\
         (word_subword (read YMM0 s) (0,128):int128 = word 0 <=>
          n MOD 2 EXP (128 * i) = M MOD 2 EXP (128 * i))`]
     else [])));;

(*** Decoding, reducing and encoding the vector, up to the loop ***)

let CHECK_PK_LIST_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:x86state`]
   `read (memory :> bytes(word_add bot (word 1192),1536)) s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 768)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1536 = 2 * 768`] THEN
    MATCH_MP_TAC CHECK_PK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECK_PK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let CHECK_PK_PART1_TAC exec (events,data) =
  let call = CHECK_PK_CALL_TAC exec (events,data) in
  (if events then REWRITE_TAC(!simulation_precanon_thms) else ALL_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC exec (1--8) THEN CHECK_PK_RSP_TAC THEN
  X86_STEPS_TAC exec (9--13) THEN CHECK_PK_NORM_TAC THEN
  call (MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT,
        "H_FROMBYTES")
   ([`read RDI s`; `read RSI s`],`n:num`) 14 THEN
  CHECK_PK_NORM_TAC THEN
  X86_STEPS_TAC exec (15--16) THEN
  call (MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT,
        "H_REDUCE")
   ([`read RDI s`],
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`) 17 THEN
  CHECK_PK_NORM_TAC THEN
  (if data then CHECK_PK_LIST_TAC `s17:x86state` else ALL_TAC) THEN
  X86_STEPS_TAC exec (18--20) THEN
  call (MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT,
        "H_TOBYTES")
   ([`read RDI s`; `read RSI s`],CHECK_PK_L) 21 THEN
  (if data then RULE_ASSUM_TAC(REWRITE_RULE[CHECK_PK_LIST_PROPS])
   else ALL_TAC) THEN
  CHECK_PK_NORM_TAC THEN CHECK_PK_YMM_TAC `s21:x86state` THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC exec [k] THEN SIMD_SIMPLIFY_TAC[])
   (22--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; CHECK_PK_SUBWORD_JOIN] THEN
  (if events then CHECK_PK_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC
   else ALL_TAC);;

(*** The loop body, comparing 16 more bytes ***)

let CHECK_PK_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 72 ==> 16 * i + 16 <= 1152`)
               (ASSUME `i < 72`)
  and pth = ARITH_RULE `16 * i = 1 * 16 * i` in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1152`) && vv = v ->
          let lth = SPECL [a; `1152`; `i:num`; v; s] CHECK_PK_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (ONCE_REWRITE_RULE[pth] (MP lth (CONJ th bth))))
    | _ -> NO_TAC);;

let CHECK_PK_BODY_TAC exec (events,data) =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  (if data then ABBREV_TAC(mk_eq(`mm:num`,CHECK_PK_M)) else ALL_TAC) THEN
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  (if events then REWRITE_TAC(!simulation_precanon_thms) else ALL_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  (if events then TRY STRIP_EXISTS_ASSUM_TAC else ALL_TAC) THEN
  (if data then
     CHECK_PK_CHUNK_TAC `pk:int64` `n:num` THEN
     CHECK_PK_CHUNK_TAC `word_add bot (word 40):int64` `mm:num`
   else ALL_TAC) THEN
  VAL_INT64_TAC `16 * i` THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC exec [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--7) THEN
  SUBGOAL_THEN
   `~(val(word_add (word (16 * i)) (word 18446744073709550480):int64) = 0) <=>
    i + 1 < 72`
  SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_ADD_CASES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < 72` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (if data then
     (if events then CONJ_TAC THENL [ALL_TAC; CHECK_PK_UNBOT_TAC THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
         (fun th -> is_eq(concl th) && rhs(concl th) = `mm:num`)) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC]
      else ALL_TAC) THEN
     ASM_REWRITE_TAC[CHECK_PK_SUBWORD_JOIN; CHECK_PK_OR_STEP;
                     CHECK_PK_MOD_STEP]
   else CHECK_PK_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** The result from the accumulators, the zeroing, the return ***)

let CHECK_PK_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `1152`; mk_comb(`read memory:x86state->int64->byte`,s)]
           READ_BYTES_BOUND);;

let CHECK_PK_DONE_TAC =
  SUBGOAL_THEN
   `(word_subword (y0:int256) (0,128):int128 = word 0) <=>
    !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) &&
         lhand(concl th) = `word_subword (y0:int256) (0,128):int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(CHECK_PK_BOUND `pk:int64` `s0:x86state`) THEN
    MP_TAC(CHECK_PK_BOUND `word_add bot (word 40):int64` `s0:x86state`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 1152 = 128 * 72`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(CHECK_PK_M,`mm:num`))) THEN
    MATCH_MP_TAC CHECK_PK_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 768 = 128 * 72`];
    ALL_TAC];;

let CHECK_PK_RESULT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) &&
       lhand(concl th) = `word_subword (y0:int256) (0,128):int128 = word 0`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  REWRITE_TAC[CHECK_PK_BYTE_MOD; GSYM word_zx; VAL_EQ_0;
              CHECK_PK_SUBWORD_JOIN] THEN
  SPEC_TAC(`word_subword (y2:int256) (0,128):int128`,`x:int128`) THEN
  SPEC_TAC(`word_subword (y0:int256) (0,128):int128`,`q:int128`) THEN
  REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

let CHECK_PK_EXIT_TAC exec (events,data) =
  REWRITE_TAC[] THEN
  (if data then ABBREV_TAC(mk_eq(`mm:num`,CHECK_PK_M)) else ALL_TAC) THEN
  GHOST_INTRO_TAC `y0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `y1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `y2:int256` `read YMM2` THEN
  (if events then REWRITE_TAC(!simulation_precanon_thms) else ALL_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  (if events then TRY STRIP_EXISTS_ASSUM_TAC else ALL_TAC) THEN
  (if data then CHECK_PK_DONE_TAC else ALL_TAC) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC exec [k] THEN SIMD_SIMPLIFY_TAC[])
   (1--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (if data then
     (if events then CONJ_TAC THENL [ALL_TAC; CHECK_PK_UNBOT_TAC THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
         (fun th -> is_eq(concl th) && rhs(concl th) = `mm:num`)) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC]
      else ALL_TAC) THEN
     CHECK_PK_RESULT_TAC
   else CHECK_PK_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** The whole proofs ***)

let CHECK_PK_INTRO_TAC =
  MAP_EVERY X_GEN_TAC [`pk:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2792 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let CHECK_PK_SAFE_INTRO_TAC exec full =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (if full then
      MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL
    else MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (if full then
      MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL
    else MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (if full then
      MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL
    else MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     APPEND (f_ev_epil pk pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 72 (\i. f_ev_loop pk pc stackpointer returnaddress i))
        (f_ev_prol pk pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   ([`pk:int64`] @ (if full then [`n:num`] else []) @ [`pc:num`]) THEN
  WORD_FORALL_OFFSET_TAC 2792 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let CHECK_PK_TAC (events,data) =
  let exec = MLKEM_NATIVE_CHECK_PK_K3_GCC12_O2_EXEC in
  (if events then CHECK_PK_SAFE_INTRO_TAC exec data
   else CHECK_PK_INTRO_TAC) THEN
  CHECK_PK_SETUP_TAC THEN
  (if events then ENSURES_EVENTS_WHILE_UP2_TAC else ENSURES_WHILE_UP2_TAC)
   `72` `pc + 0x6d10` `pc + 0x6d31` (CHECK_PK_INV data) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CHECK_PK_PART1_TAC exec (events,data);
    CHECK_PK_BODY_TAC exec (events,data);
    CHECK_PK_EXIT_TAC exec (events,data)];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The first 1152 bytes of the key at pk are a number n,  *)
(* and the result is 0 if all the 768 12-bit fields of n are below 3329,     *)
(* which is the modulus check of FIPS 203, and -4 otherwise. The stack is    *)
(* the 2792 bytes below the return address, for the four saved registers, up *)
(* to 31 bytes for the alignment, the 2688 bytes of the buffers and the 40   *)
(* used by the callees below them.                                           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = time prove
 (`!pk n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    nonoverlapping (pk,1152) (word_sub stackpointer (word 2792),2800) /\
    nonoverlapping (word_sub stackpointer (word 2792),2800) (word pc,0x82a0)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x6cc0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,1152)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s =
              (if !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(word_sub stackpointer (word 2792),2792)])`,
  CHECK_PK_TAC (false,true));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, and the combined theorem with      *)
(* correctness, for mlkem768_enc_derand, which branches on the result. The   *)
(* events depend only on the address of the key, the stack and the image:    *)
(* the comparison is in constant time and the result is computed without a   *)
(* branch.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e pk pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    nonoverlapping (pk,1152) (word_sub stackpointer (word 2792),2800) /\
    nonoverlapping (word_sub stackpointer (word 2792),2800) (word pc,0x82a0)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x6cc0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk] s /\
              (read DF s <=> false) /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk pc (word_sub stackpointer (word 2792))
                               returnaddress /\
                 memaccess_inbounds e2
                  [pk,1152; word_sub stackpointer (word 2792),2800]
                  [word_sub stackpointer (word 2792),2792]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(word_sub stackpointer (word 2792),2792)])`,
  CHECK_PK_TAC (true,false));;

let MLKEM_NATIVE_CHECK_PK_K3_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  time prove
 (`exists f_events.
   forall e pk n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    nonoverlapping (pk,1152) (word_sub stackpointer (word 2792),2800) /\
    nonoverlapping (word_sub stackpointer (word 2792),2800) (word pc,0x82a0)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x6cc0) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,1152)) s = n /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s =
              (if !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk pc (word_sub stackpointer (word 2792))
                               returnaddress /\
                 memaccess_inbounds e2
                  [pk,1152; word_sub stackpointer (word 2792),2800]
                  [word_sub stackpointer (word 2792),2792]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(word_sub stackpointer (word 2792),2792)])`,
  CHECK_PK_TAC (true,true));;
