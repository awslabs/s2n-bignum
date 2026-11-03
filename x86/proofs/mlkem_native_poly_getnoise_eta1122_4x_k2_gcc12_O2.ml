(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of two noise polynomials with eta = 3 and two with eta = 2 from  *)
(* a seed and nonces. This is the code for mlkem512_poly_getnoise_eta1122_4x *)
(* from mlkem-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mlkem_native/README.md), which computes 192 bytes of SHAKE256 of the *)
(* seed and each of the four nonces into buffers on the stack with           *)
(* mlkem_shake256x4, applies mlkem_poly_cbd3 to the first two and            *)
(* mlkem_poly_cbd2 to the first 128 bytes of the others, and zeroes the      *)
(* buffers. It is verified in the whole image (see                           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x5ed0, using  *)
(* the theorems for mlkem_shake256x4 at 0x3870, mlkem_poly_cbd3 at 0x6420    *)
(* and mlkem_poly_cbd2 at 0x63b0 in the image.                               *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_shake256x4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_cbd3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_cbd2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    5ed0: lea    r10,[rsp+0x8]
    5ed5: and    rsp,0xffffffffffffffe0
    5ed9: push   QWORD PTR [r10-0x8]
    5edd: push   rbp
    5ede: mov    rbp,rsp
    5ee1: push   r15
    5ee3: push   r14
    5ee5: lea    r15,[rbp-0x270]
    5eec: lea    r14,[rbp-0x1b0]
    5ef3: push   r13
    5ef5: lea    r13,[rbp-0xf0]
    5efc: push   r12
    5efe: lea    r12,[rbp-0x430]
    5f05: push   r10
    5f07: push   rbx
    5f08: lea    rbx,[rbp-0x330]
    5f0f: sub    rsp,0x420
    5f16: mov    eax,DWORD PTR [r10+0x10]
    5f1a: mov    r11d,DWORD PTR [r10]
    5f1d: mov    QWORD PTR [rbp-0x448],rdx
    5f24: movdqu xmm1,XMMWORD PTR [r8]
    5f29: mov    edx,DWORD PTR [r10+0x8]
    5f2d: mov    QWORD PTR [rbp-0x438],rdi
    5f34: lea    rdi,[rbp-0x370]
    5f3b: movdqu xmm0,XMMWORD PTR [r8+0x10]
    5f41: mov    QWORD PTR [rbp-0x440],rsi
    5f48: lea    rsi,[rbp-0x3b0]
    5f4f: mov    r8d,0xc0
    5f55: mov    QWORD PTR [rbp-0x450],rcx
    5f5c: lea    rcx,[rbp-0x3f0]
    5f63: mov    BYTE PTR [rbp-0x350],al
    5f69: mov    BYTE PTR [rbp-0x3d0],r11b
    5f70: movaps XMMWORD PTR [rbp-0x430],xmm1
    5f77: movaps XMMWORD PTR [rbp-0x420],xmm0
    5f7e: movaps XMMWORD PTR [rbp-0x3f0],xmm1
    5f85: movaps XMMWORD PTR [rbp-0x3e0],xmm0
    5f8c: movaps XMMWORD PTR [rbp-0x3b0],xmm1
    5f93: movaps XMMWORD PTR [rbp-0x3a0],xmm0
    5f9a: movaps XMMWORD PTR [rbp-0x370],xmm1
    5fa1: movaps XMMWORD PTR [rbp-0x360],xmm0
    5fa8: mov    BYTE PTR [rbp-0x410],r9b
    5faf: mov    r9,r12
    5fb2: mov    BYTE PTR [rbp-0x390],dl
    5fb8: mov    rdx,r14
    5fbb: push   0x21
    5fbd: push   rdi
    5fbe: mov    rdi,rbx
    5fc1: push   rsi
    5fc2: mov    rsi,r15
    5fc5: push   rcx
    5fc6: mov    rcx,r13
    5fc9: call   3870 <mlkem_shake256x4>
    5fce: mov    rdi,QWORD PTR [rbp-0x438]
    5fd5: add    rsp,0x20
    5fd9: mov    rsi,rbx
    5fdc: call   6420 <mlkem_poly_cbd3>
    5fe1: mov    rdi,QWORD PTR [rbp-0x440]
    5fe8: mov    rsi,r15
    5feb: call   6420 <mlkem_poly_cbd3>
    5ff0: mov    rdi,QWORD PTR [rbp-0x448]
    5ff7: mov    rsi,r14
    5ffa: call   63b0 <mlkem_poly_cbd2>
    5fff: mov    rdi,QWORD PTR [rbp-0x450]
    6006: mov    rsi,r13
    6009: call   63b0 <mlkem_poly_cbd2>
    600e: xor    eax,eax
    6010: mov    rdi,rbx
    6013: mov    ecx,0x60
    6018: rep    stos QWORD PTR es:[rdi],rax
    601b: mov    ecx,0x20
    6020: mov    rdi,r12
    6023: rep    stos QWORD PTR es:[rdi],rax
    6026: lea    rsp,[rbp-0x30]
    602a: pop    rbx
    602b: pop    r10
    602d: pop    r12
    602f: pop    r13
    6031: pop    r14
    6033: pop    r15
    6035: pop    rbp
    6036: lea    rsp,[r10-0x8]
    603a: ret
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x5ed0,0x603b];;

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
(* variable bot for the bottom of the stack of mlkem_shake256x4, 3104 bytes  *)
(* below the aligned stack pointer, which is stackpointer + delta for delta  *)
(* = 32 - val(stackpointer + 3136) MOD 32, where stackpointer is the bottom  *)
(* of the 3136 bytes of the stack below the return address. The facts about  *)
(* the frame are proved by BITBLAST through the form of delta as a word,     *)
(* GETNOISE_DELTA, and the addresses in the frame are bot plus a constant,   *)
(* as GETNOISE_NORM_TAC puts them: the four inputs to SHAKE256 at bot +      *)
(* 2016, 64 bytes apart, and its outputs at bot + 2272, 192 bytes apart.     *)
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
(* seventh to ninth, on the stack. As in mlkem512_poly_getnoise_eta1_4x, the *)
(* first two results are mlkem_poly_cbd3 applied to the first 192 bytes of   *)
(* shake256 of the seed followed by the nonce, and as in                     *)
(* mlkem512_poly_getnoise_eta2 the other two are mlkem_poly_cbd2 applied to  *)
(* the first 128 bytes. The stack is as for mlkem512_poly_getnoise_eta1_4x:  *)
(* the 3136 bytes below the return address, for up to 31 bytes for the       *)
(* alignment, the copy of the return address and the seven saved registers,  *)
(* the 1056 bytes of the buffers and of the saved pointers, and the 1984     *)
(* used by mlkem_shake256x4 with its arguments on the stack below them, and  *)
(* the arguments on the stack are the 24 bytes above the return address.     *)
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

(*** The first 128 of the 192 bytes of SHAKE256, for mlkem_poly_cbd2 ***)

let GETNOISE4_PREFIX = prove
 (`!a (f:num->byte) s:x86state.
        read (memory :> bytes(a,192)) s = num_of_bytelist(list_of_seq f 192)
        ==> read (memory :> bytes(a,128)) s =
            num_of_bytelist(list_of_seq f 128)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `192`; `128`; `read memory s`] READ_BYTES_MOD) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `MIN 192 128 = 128`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `192 = 128 + 64`;
              NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) 128` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let GETNOISE4_PREFIX_TAC c =
  let a = mk_comb(`word_add (bot:int64)`,
                  mk_comb(`word:num->int64`,mk_small_numeral c)) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),_)
        when aa = mk_pair(a,`192`) ->
          ASSUME_TAC(MATCH_MP GETNOISE4_PREFIX th)
    | _ -> NO_TAC);;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!r0 r1 r2 r3 seed (sd:byte list) nonce0 nonce1 nonce2 nonce3
    pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r0,512); (r1,512); (r2,512); (r3,512);
          (word_sub stackpointer (word 3136),3168)] /\
        ALLPAIRS nonoverlapping
         [(r0,512); (r1,512); (r2,512); (r3,512);
          (word_sub stackpointer (word 3136),3168)]
         [(seed,32); (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x5ed0) /\
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
                             (shake256 (APPEND sd [word_zx nonce0])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r0 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce1])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r1 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
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
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce3])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r3 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,512);
                memory :> bytes(word_sub stackpointer (word 3136),3136)])`,
  let exec = MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_GCC12_O2_EXEC in
  let cbd th len k nonce =
    LOCAL_CBD_TAC exec th
     [`read RDI s`; `read RSI s`; GETNOISE4_N len nonce; `pc:num`;
      `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] k in
  GETNOISE4_INTRO_TAC 3136 THEN GETNOISE4_SETUP_TAC 3136 true THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  ENSURES_INIT_TAC "s0" THEN GETNOISE4_STACKNORM_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GETNOISE_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN GETNOISE4_ARGS_TAC 3136 THEN

  (*** The inputs to SHAKE256 for the four nonces ***)

  X86_STEPS_TAC exec (1--2) THEN GETNOISE4_RSP_TAC 3136 THEN
  X86_STEPS_TAC exec (3--17) THEN GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (18--52) THEN GETNOISE_NORM_TAC THEN GETNOISE_SSE_TAC THEN
  MAP_EVERY (fun (k,nonce) -> GETNOISE4_INPUT_TAC `s52:x86state` k nonce)
   [0,`nonce0:int64`; 1,`nonce1:int64`; 2,`nonce2:int64`; 3,`nonce3:int64`]
  THEN

  (*** The calls ***)

  LOCAL_SHAKE256X4_TAC exec
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `192`;
    `read R9 s`; `word_add bot (word 2080):int64`;
    `word_add bot (word 2144):int64`; `word_add bot (word 2208):int64`;
    `33`; GETNOISE4_INP `nonce0:int64`; GETNOISE4_INP `nonce1:int64`;
    GETNOISE4_INP `nonce2:int64`; GETNOISE4_INP `nonce3:int64`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 53 THEN
  GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (54--57) THEN
  cbd MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT 192 58
   `nonce0:int64` THEN
  X86_STEPS_TAC exec (59--61) THEN
  cbd MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT 192 62
   `nonce1:int64` THEN
  GETNOISE4_PREFIX_TAC 2656 THEN GETNOISE4_PREFIX_TAC 2848 THEN
  X86_STEPS_TAC exec (63--65) THEN
  cbd MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT 128 66
   `nonce2:int64` THEN
  X86_STEPS_TAC exec (67--69) THEN
  cbd MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT 128 70
   `nonce3:int64` THEN

  (*** Zeroing the buffers and the return ***)

  X86_STEPS_TAC exec (71--87) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events do not depend on the    *)
(* seed or the nonces. At the end the frame variables are expanded in them   *)
(* by GETNOISE_UNBOT_TAC, since they are not arguments of f_events.          *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

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

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e r0 r1 r2 r3 seed pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [r0,512; r1,512; r2,512; r3,512;
          word_sub stackpointer (word 3136),3168] /\
        ALLPAIRS nonoverlapping
         [r0,512; r1,512; r2,512; r3,512;
          word_sub stackpointer (word 3136),3168]
         [seed,32; word pc,0x82a0]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x5ed0) /\
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
                            (word_sub stackpointer (word 3136))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; r0,512; r1,512; r2,512;
                       r3,512;
                       word_sub stackpointer (word 3136),3168;
                       word(pc + 0x80c0),192]
                      [r0,512; r1,512; r2,512;
                       r3,512;
                       word_sub stackpointer (word 3136),3136]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,512);
                memory :> bytes(word_sub stackpointer (word 3136),3136)])`,
  let exec = MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_GCC12_O2_EXEC in
  let cbd name k =
    GETNOISE4_SAFE_CALL_TAC exec name
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
      `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] k in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_SHAKE256X4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_CBD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_CBD2" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
    `seed:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3136 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GETNOISE4_SETUP_TAC 3136 true THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN GETNOISE4_STACKNORM_TAC THEN
  X86_STEPS_TAC exec (1--2) THEN GETNOISE4_RSP_TAC 3136 THEN
  X86_STEPS_TAC exec (3--17) THEN GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (18--52) THEN GETNOISE_NORM_TAC THEN
  GETNOISE4_SAFE_CALL_TAC exec "H_SHAKE256X4"
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RCX s`; `192`; `read R9 s`;
    `word_add bot (word 2080):int64`; `word_add bot (word 2144):int64`;
    `word_add bot (word 2208):int64`; `33`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 53 THEN
  GETNOISE_NORM_TAC THEN
  X86_STEPS_TAC exec (54--57) THEN cbd "H_CBD3" 58 THEN
  X86_STEPS_TAC exec (59--61) THEN cbd "H_CBD3" 62 THEN
  X86_STEPS_TAC exec (63--65) THEN cbd "H_CBD2" 66 THEN
  X86_STEPS_TAC exec (67--69) THEN cbd "H_CBD2" 70 THEN
  X86_STEPS_TAC exec (71--87) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  GETNOISE_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;
