(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four noise polynomials with eta = 2 from a seed and nonces.   *)
(* This is the code for mlkem768_poly_getnoise_eta1_4x from mlkem-native's   *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which computes 128 bytes of SHAKE256 of the seed *)
(* and each of the four nonces into buffers on the stack with                *)
(* mlkem_shake256x4, applies mlkem_poly_cbd2 to them, skipping the fourth    *)
(* polynomial if its pointer is null, and zeroes the buffers. It is verified *)
(* in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is   *)
(* at address 0x7790, using the theorems for mlkem_shake256x4 at 0x3870 and  *)
(* mlkem_poly_cbd2 at 0x63b0 in the image.                                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_shake256x4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_cbd2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    7790: lea    r10,[rsp+0x8]
    7795: and    rsp,0xffffffffffffffe0
    7799: push   QWORD PTR [r10-0x8]
    779d: push   rbp
    779e: mov    rbp,rsp
    77a1: push   r15
    77a3: push   r14
    77a5: lea    r15,[rbp-0x330]
    77ac: lea    r14,[rbp-0x130]
    77b3: push   r13
    77b5: lea    r13,[rbp-0xb0]
    77bc: push   r12
    77be: mov    r12,rcx
    77c1: push   r10
    77c3: push   rbx
    77c4: lea    rbx,[rbp-0x230]
    77cb: sub    rsp,0x320
    77d2: mov    r11d,DWORD PTR [r10]
    77d5: mov    ecx,DWORD PTR [r10+0x8]
    77d9: mov    QWORD PTR [rbp-0x348],rdx
    77e0: movdqu xmm1,XMMWORD PTR [r8]
    77e5: mov    edx,DWORD PTR [r10+0x10]
    77e9: mov    QWORD PTR [rbp-0x338],rdi
    77f0: lea    rdi,[rbp-0x2b0]
    77f7: movdqu xmm0,XMMWORD PTR [r8+0x10]
    77fd: mov    QWORD PTR [rbp-0x340],rsi
    7804: lea    r8,[rbp-0x270]
    780b: lea    rsi,[rbp-0x2f0]
    7812: mov    BYTE PTR [rbp-0x2d0],r11b
    7819: lea    r10,[rbp-0x1b0]
    7820: movaps XMMWORD PTR [rbp-0x330],xmm1
    7827: movaps XMMWORD PTR [rbp-0x320],xmm0
    782e: movaps XMMWORD PTR [rbp-0x2f0],xmm1
    7835: movaps XMMWORD PTR [rbp-0x2e0],xmm0
    783c: movaps XMMWORD PTR [rbp-0x2b0],xmm1
    7843: movaps XMMWORD PTR [rbp-0x2a0],xmm0
    784a: movaps XMMWORD PTR [rbp-0x270],xmm1
    7851: movaps XMMWORD PTR [rbp-0x260],xmm0
    7858: mov    BYTE PTR [rbp-0x310],r9b
    785f: mov    r9,r15
    7862: mov    BYTE PTR [rbp-0x290],cl
    7868: mov    rcx,r13
    786b: mov    BYTE PTR [rbp-0x250],dl
    7871: mov    rdx,r14
    7874: push   0x21
    7876: push   r8
    7878: mov    r8d,0x80
    787e: push   rdi
    787f: mov    rdi,rbx
    7882: push   rsi
    7883: mov    rsi,r10
    7886: mov    QWORD PTR [rbp-0x350],r10
    788d: call   3870 <mlkem_shake256x4>
    7892: mov    rdi,QWORD PTR [rbp-0x338]
    7899: add    rsp,0x20
    789d: mov    rsi,rbx
    78a0: call   63b0 <mlkem_poly_cbd2>
    78a5: mov    rsi,QWORD PTR [rbp-0x350]
    78ac: mov    rdi,QWORD PTR [rbp-0x340]
    78b3: call   63b0 <mlkem_poly_cbd2>
    78b8: mov    rdi,QWORD PTR [rbp-0x348]
    78bf: mov    rsi,r14
    78c2: call   63b0 <mlkem_poly_cbd2>
    78c7: test   r12,r12
    78ca: je     78d7 <mlkem768_poly_getnoise_eta1_4x+0x147>
    78cc: mov    rsi,r13
    78cf: mov    rdi,r12
    78d2: call   63b0 <mlkem_poly_cbd2>
    78d7: xor    eax,eax
    78d9: mov    rdi,rbx
    78dc: mov    ecx,0x40
    78e1: rep    stos QWORD PTR es:[rdi],rax
    78e4: mov    ecx,0x20
    78e9: mov    rdi,r15
    78ec: rep    stos QWORD PTR es:[rdi],rax
    78ef: lea    rsp,[rbp-0x30]
    78f3: pop    rbx
    78f4: pop    r10
    78f6: pop    r12
    78f8: pop    r13
    78fa: pop    r14
    78fc: pop    r15
    78fe: pop    rbp
    78ff: lea    rsp,[r10-0x8]
    7903: ret
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x7790,0x7904];;

(* ------------------------------------------------------------------------- *)
(* The seed is loaded as two 128-bit words, and stored with the nonce in a   *)
(* buffer of 64 bytes, as the 33 bytes of the input to SHAKE256. The nonces  *)
(* after the first are on the stack, as 64-bit words of which the function   *)
(* reads the low 32 bits. The stores are from the low halves of YMM          *)
(* registers, whose upper halves are kept as their initial values.           *)
(* ------------------------------------------------------------------------- *)

let GETNOISE_BYTES128_HALVES = prove
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

let GETNOISE_BYTES_32_OF_HALVES = prove
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

let GETNOISE_INPUT = prove
 (`!a:int64 (sd:byte list) b s:x86state.
        LENGTH sd = 32 /\
        read (memory :> bytes(a,32)) s = num_of_bytelist sd /\
        read (memory :> bytes8(word_add a (word 32))) s = b
        ==> LENGTH(APPEND sd [b]) = 33 /\
            read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND sd [b])`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `33 = 32 + 1`; READ_MEMORY_BYTES_SNOC] THEN
  ASM_REWRITE_TAC[num_of_bytelist] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let GETNOISE_SUBWORD_JOIN = prove
 (`!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`,
  CONV_TAC WORD_BLAST);;

let GETNOISE_SSE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GETNOISE_SUBWORD_JOIN]);;

let READ_MEMORY_BYTES32_OF_BYTES64_ZX = prove
 (`!a:int64 x s:x86state.
        read (memory :> bytes64 a) s = x
        ==> read (memory :> bytes32 a) s = word_zx x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  REWRITE_TAC[BYTES64_WBYTES; BYTES32_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_64; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP (8 * 4)`; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The function aligns the stack pointer itself to 32 bytes, by AND with -32 *)
(* at the start, keeping the address of its arguments on the stack in R10,   *)
(* and then pushes a copy of the return address and the saved registers, and *)
(* later the arguments of mlkem_shake256x4 below its frame. The proof uses a *)
(* variable bot for the bottom of the stack of mlkem_shake256x4, 2848 bytes  *)
(* below the aligned stack pointer, which is stackpointer + delta for delta  *)
(* = 32 - val(stackpointer + 2880) MOD 32, where stackpointer is the bottom  *)
(* of the 2880 bytes of the stack below the return address. The facts about  *)
(* the frame are proved by BITBLAST through the form of delta as a word,     *)
(* GETNOISE_DELTA, and the addresses in the frame are bot plus a constant,   *)
(* as GETNOISE_NORM_TAC puts them: the four inputs to SHAKE256 at bot +      *)
(* 2016, 64 bytes apart, and its outputs at bot + 2272, 128 bytes apart. The *)
(* setup takes as a parameter whether there is a fourth result, whose region *)
(* has size 0 if its pointer is null.                                        *)
(* ------------------------------------------------------------------------- *)

let GETNOISE_ALIGNED_16 = prove
 (`!x:int64. aligned 16 x <=> word_and x (word 15) = word 0`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`]);;

let GETNOISE_DELTA = prove
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

let GETNOISE4_BOT_TAC n =
  let nt = mk_small_numeral n and at = mk_small_numeral(n - 32) in
  ABBREV_TAC(vsubst [nt,`n:num`]
   `delta = 32 - val(word_add (stackpointer:int64) (word n)) MOD 32`) THEN
  SUBGOAL_THEN `delta <= 32` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bot = word_add (stackpointer:int64) (word delta)` THEN
  SUBGOAL_THEN (vsubst [nt,`n:num`; at,`a:num`]
   `word_and (word_add stackpointer (word n))
             (word 18446744073709551584):int64 =
    word_add bot (word a) /\
    aligned 16 (bot:int64)`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GETNOISE_ALIGNED_16] THEN
    MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN
    REWRITE_TAC[GETNOISE_DELTA] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC];;

let GETNOISE4_NONOV_TAC n full =
  FIRST_ASSUM(fun bth ->
    if is_eq(concl bth) && rhs(concl bth) = `bot:int64`
    then
      MAP_EVERY (fun r ->
        SUBGOAL_THEN
         (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                          mk_pair(`bot:int64`,mk_small_numeral(n - 32))),r))
         ASSUME_TAC THENL
         [REWRITE_TAC[SYM bth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       ([`r0:int64,512`; `r1:int64,512`; `r2:int64,512`] @
        (if full then [`r3:int64,512`] else []) @
        [`seed:int64,32`; `word pc:int64,0x82a0`;
         mk_pair(mk_comb(`word_add (stackpointer:int64)`,
                         mk_comb(`word:num->int64`,mk_small_numeral n)),
                 `32`)])
    else NO_TAC);;

let GETNOISE4_FRAME_TAC n full =
  let r3s = if full then [`memory :> bytes(r3:int64,512)`] else [] in
  let fr = mk_flist
   ([`memory :> bytes(r0:int64,512)`; `memory :> bytes(r1:int64,512)`;
     `memory :> bytes(r2:int64,512)`] @ r3s @
    [vsubst [mk_small_numeral(n - 32),`n:num`]
       `memory :> bytes(bot:int64,n)`]) in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   (vsubst [fr,`l:((x86state,num)component)list`]
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
    MAYCHANGE (l:((x86state,num)component)list)`) THEN
  CONJ_TAC THENL [EXPAND_TAC "bot" THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC];;

let GETNOISE4_SETUP_TAC n full =
  GETNOISE4_BOT_TAC n THEN GETNOISE4_FRAME_TAC n full THEN
  GETNOISE4_NONOV_TAC n full THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let GETNOISE_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let GETNOISE_ADDR_CONV =
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC NUM_REDUCE_CONV;;

let GETNOISE4_STACKNORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let GETNOISE4_RSP_TAC n =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             (vsubst [mk_small_numeral n,`n:num`]
               `word_and (word_add stackpointer (word n))
                         (word 18446744073709551584):int64 = x`))
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is 32 bytes at seed, given as a list of bytes *)
(* sd, and the nonces are the low bytes of the sixth argument and of the     *)
(* seventh to ninth, on the stack. For each polynomial, as for               *)
(* mlkem1024_poly_getnoise_eta2 but with eta = 2, the result is              *)
(* mlkem_poly_cbd2 applied to the first 128 bytes of shake256 of the seed    *)
(* followed by the nonce, except that if the fourth pointer is null there is *)
(* no fourth result. The proof is by cases on whether it is null, which also *)
(* decides the branch before the fourth call of mlkem_poly_cbd2. The stack   *)
(* is the 2880 bytes below the return address, for up to 31 bytes for the    *)
(* alignment, the copy of the return address and the seven saved registers,  *)
(* the 800 bytes of the buffers and of the saved pointers, and the 1984 used *)
(* by mlkem_shake256x4 with its arguments on the stack below them, and the   *)
(* arguments on the stack are the 24 bytes above the return address.         *)
(* ------------------------------------------------------------------------- *)

let GETNOISE4_INTRO_TAC n =
  MAP_EVERY X_GEN_TAC
   [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
    `sd:byte list`; `nonce0:int64`; `nonce1:int64`; `nonce2:int64`;
    `nonce3:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let GETNOISE4_CASES_TAC =
  ASM_CASES_TAC `r3:int64 = word 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]);
    RULE_ASSUM_TAC(fun th ->
      if concl th = `~(r3:int64 = word 0)` then th
      else REWRITE_RULE[ASSUME `~(r3:int64 = word 0)`] th) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(val(r3:int64) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC]];;

let LOCAL_SHAKE256X4_TAC exec =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,exec,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD_TAC exec th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,exec,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,th);;

(*** The inputs to SHAKE256 and the results ***)

let GETNOISE4_N outlen nonce =
  vsubst [nonce,`nonce:int64`; mk_small_numeral outlen,`l:num`]
   `num_of_bytelist(list_of_seq
     (shake256(APPEND (sd:byte list) [word_zx(nonce:int64)])) l)`;;

let GETNOISE4_INP nonce =
  vsubst [nonce,`nonce:int64`] `APPEND (sd:byte list) [word_zx(nonce:int64)]`;;

let GETNOISE4_ARGS_TAC n =
  MAP_EVERY (fun k ->
    let a = mk_comb(`word_add (stackpointer:int64)`,
                    mk_comb(`word:num->int64`,mk_small_numeral(n + 8 * k))) in
    FIRST_ASSUM(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),
                  Comb(Comb(Const("read",_),
                            Comb(Comb(Const(":>",_),Const("memory",_)),
                                 Comb(Const("bytes64",_),aa))),_)),_)
          when aa = a ->
          ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES32_OF_BYTES64_ZX th)
      | _ -> NO_TAC))
   (1--3);;

let GETNOISE4_INPUT_TAC s k nonce =
  let a = mk_comb(`word_add (bot:int64)`,
                  mk_comb(`word:num->int64`,
                          mk_small_numeral(2016 + 64 * k))) in
  MP_TAC(SPECL [a; `num_of_bytelist(sd:byte list)`; s]
               GETNOISE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC GETNOISE_ADDR_CONV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `sd:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [a; `sd:byte list`;
                mk_comb(`word_zx:int64->byte`,nonce); s] GETNOISE_INPUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC GETNOISE_ADDR_CONV THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes8 a) s = x`) (concl th) &&
         free_in (mk_comb(`word_add (bot:int64)`,
                          mk_comb(`word:num->int64`,
                                  mk_small_numeral(2048 + 64 * k))))
                 (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    CONV_TAC WORD_BLAST;
    STRIP_TAC];;

(*** The simulation in each case, with the parameters for each k ***)

let GETNOISE4_CASE_TAC (exec,n,outlen,cbdth) full =
  let cbd k nonce =
    LOCAL_CBD_TAC exec cbdth
     [`read RDI s`; `read RSI s`; GETNOISE4_N outlen nonce; `pc:num`;
      `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] k in
  GETNOISE4_SETUP_TAC n full THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  ENSURES_INIT_TAC "s0" THEN GETNOISE4_STACKNORM_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GETNOISE_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN GETNOISE4_ARGS_TAC n THEN

  (*** The inputs to SHAKE256 for the four nonces ***)

  X86_STEPS_TAC exec (1--2) THEN GETNOISE4_RSP_TAC n THEN
  X86_STEPS_TAC exec (3--17) THEN GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (18--53) THEN GETNOISE_NORM_TAC THEN GETNOISE_SSE_TAC THEN
  MAP_EVERY (fun (k,nonce) -> GETNOISE4_INPUT_TAC `s53:x86state` k nonce)
   [0,`nonce0:int64`; 1,`nonce1:int64`; 2,`nonce2:int64`; 3,`nonce3:int64`]
  THEN

  (*** The calls ***)

  LOCAL_SHAKE256X4_TAC exec
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
    mk_small_numeral outlen; `read R9 s`; `word_add bot (word 2080):int64`;
    `word_add bot (word 2144):int64`; `word_add bot (word 2208):int64`;
    `33`; GETNOISE4_INP `nonce0:int64`; GETNOISE4_INP `nonce1:int64`;
    GETNOISE4_INP `nonce2:int64`; GETNOISE4_INP `nonce3:int64`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 54 THEN
  GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (55--58) THEN cbd 59 `nonce0:int64` THEN
  X86_STEPS_TAC exec (60--62) THEN cbd 63 `nonce1:int64` THEN
  X86_STEPS_TAC exec (64--66) THEN cbd 67 `nonce2:int64` THEN
  X86_STEPS_TAC exec (68--69) THEN
  (if full then X86_STEPS_TAC exec (70--72) THEN cbd 73 `nonce3:int64`
   else ALL_TAC) THEN

  (*** Zeroing the buffers and the return ***)

  let e = if full then 74 else 70 in
  X86_STEPS_TAC exec (e--(e+16)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r0 r1 r2 r3 seed (sd:byte list) nonce0 nonce1 nonce2 nonce3
    pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2880),2912)] /\
        ALLPAIRS nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2880),2912)]
         [(seed,32); (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x7790) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; nonce0] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  nonce1 /\
                  read (memory :> bytes64(word_add stackpointer (word 16))) s =
                  nonce2 /\
                  read (memory :> bytes64(word_add stackpointer (word 24))) s =
                  nonce3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce0])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r0 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce1])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r1 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce2])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r2 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (~(r3 = word 0) ==>
                   (let n = num_of_bytelist
                            (list_of_seq
                              (shake256 (APPEND sd [word_zx nonce3])) 128) in
                    !i. i < 256
                        ==> read(memory :> bytes16(word_add r3 (word(2 * i))))
                                 s =
                            iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                    (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                  &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                    (n DIV 2 EXP (4 * i + 3)) MOD 2)))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                memory :> bytes(word_sub stackpointer (word 2880),2880)])`,
  let params =
   (MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_EXEC,2880,128,
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) in
  GETNOISE4_INTRO_TAC 2880 THEN GETNOISE4_CASES_TAC THENL
   [GETNOISE4_CASE_TAC params false; GETNOISE4_CASE_TAC params true]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events do not depend on the    *)
(* seed or the nonces, but they do on whether the fourth pointer is null, so *)
(* the template gives them by cases on that, and the split keeps the pointer *)
(* as a variable rather than substituting 0 for it. At the end the frame     *)
(* variables are expanded in them by GETNOISE_UNBOT_TAC, since they are not  *)
(* arguments of f_events.                                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let GETNOISE4_SAFE_TEMPLATE =
 `\(r0:int64) (r1:int64) (r2:int64) (r3:int64) (seed:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   if r3 = word 0
   then f_ev_null r0 r1 r2 r3 seed pc stackpointer returnaddress
   else f_ev_full r0 r1 r2 r3 seed pc stackpointer returnaddress
   :(uarch_event)list`;;

let GETNOISE4_SAFE_ALLOWED =
  [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let GETNOISE4_SAFE_CALL_TAC exec name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,exec,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GETNOISE4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let GETNOISE_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `delta:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

let GETNOISE4_SAFE_INTRO_TAC n cbdth =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_SHAKE256X4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC cbdth "H_CBD" THEN
  CONCRETIZE_F_EVENTS_TAC GETNOISE4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let GETNOISE4_SAFE_CASES_TAC =
  ASM_CASES_TAC `r3:int64 = word 0` THEN
  FIRST_ASSUM(fun th ->
    let th' = if is_neg(concl th) then EQF_INTRO th else EQT_INTRO th in
    REWRITE_TAC[th'] THEN
    RULE_ASSUM_TAC(fun th'' ->
      if concl th'' = concl th then th'' else REWRITE_RULE[th'] th'')) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if c = `r3:int64 = word 0` || c = `~(r3:int64 = word 0)`
    then ASSUME_TAC(REWRITE_RULE[GSYM VAL_EQ_0] th) else NO_TAC);;

let GETNOISE4_SAFE_CASE_TAC (exec,n,outlen) full =
  let cbd k =
    GETNOISE4_SAFE_CALL_TAC exec "H_CBD"
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
      `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] k in
  GETNOISE4_SETUP_TAC n full THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN GETNOISE4_STACKNORM_TAC THEN
  X86_STEPS_TAC exec (1--2) THEN GETNOISE4_RSP_TAC n THEN
  X86_STEPS_TAC exec (3--17) THEN GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (18--53) THEN GETNOISE_NORM_TAC THEN
  GETNOISE4_SAFE_CALL_TAC exec "H_SHAKE256X4"
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RCX s`; mk_small_numeral outlen; `read R9 s`;
    `word_add bot (word 2080):int64`; `word_add bot (word 2144):int64`;
    `word_add bot (word 2208):int64`; `33`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 54 THEN
  GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (55--58) THEN cbd 59 THEN
  X86_STEPS_TAC exec (60--62) THEN cbd 63 THEN
  X86_STEPS_TAC exec (64--66) THEN cbd 67 THEN
  X86_STEPS_TAC exec (68--69) THEN
  (if full then X86_STEPS_TAC exec (70--72) THEN cbd 73 else ALL_TAC) THEN
  let e = if full then 74 else 70 in
  X86_STEPS_TAC exec (e--(e+16)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  GETNOISE_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e r0 r1 r2 r3 seed pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
          word_sub stackpointer (word 2880),2912] /\
        ALLPAIRS nonoverlapping
         [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
          word_sub stackpointer (word 2880),2912]
         [seed,32; word pc,0x82a0]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x7790) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed pc
                            (word_sub stackpointer (word 2880))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; r0,512; r1,512; r2,512;
                       r3,(if r3 = word 0 then 0 else 512);
                       word_sub stackpointer (word 2880),2912;
                       word(pc + 0x80c0),192]
                      [r0,512; r1,512; r2,512;
                       r3,(if r3 = word 0 then 0 else 512);
                       word_sub stackpointer (word 2880),2880]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                memory :> bytes(word_sub stackpointer (word 2880),2880)])`,
  let params =
   (MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_EXEC,2880,128) in
  GETNOISE4_SAFE_INTRO_TAC 2880
   MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE THEN
  GETNOISE4_SAFE_CASES_TAC THENL
   [GETNOISE4_SAFE_CASE_TAC params false;
    GETNOISE4_SAFE_CASE_TAC params true]);;
