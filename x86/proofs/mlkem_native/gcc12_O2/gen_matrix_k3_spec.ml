(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generation of the ML-KEM-768 matrix from a seed. This is the code for     *)
(* mlkem768_gen_matrix from mlkem-native's portable C implementation         *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which copies    *)
(* the seed of 32 bytes into four buffers of 64 bytes on the stack, appends  *)
(* the two indices of each entry of the matrix to it, samples the first      *)
(* eight of the nine entries four at a time with mlkem_poly_rej_uniform_x4   *)
(* and the last one with mlkem_poly_rej_uniform, and zeroes the buffers. It  *)
(* is verified in the whole image (see libmlkem.ml), using the theorems for  *)
(* mlkem_poly_rej_uniform_x4 and mlkem_poly_rej_uniform in the image.        *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_rej_uniform_x4_spec.ml";;

(*** The code in the image:

    mlkem768_gen_matrix:
       +0x0: push   rbp
       +0x1: mov    rbp,rsp
       +0x4: push   r12
       +0x6: push   rbx
       +0x7: mov    rbx,rdi
       +0xa: and    rsp,0xffffffffffffffe0
       +0xe: sub    rsp,0x100
      +0x15: movdqu xmm1,XMMWORD PTR [rsi]
      +0x19: movdqu xmm0,XMMWORD PTR [rsi+0x10]
      +0x1e: mov    r12,rsp
      +0x21: lea    rcx,[rsp+0x100]
      +0x29: mov    rax,r12
      +0x2c: movaps XMMWORD PTR [rax],xmm1
      +0x2f: add    rax,0x40
      +0x33: movaps XMMWORD PTR [rax-0x30],xmm0
      +0x37: cmp    rax,rcx
      +0x3a: jne    <mlkem768_gen_matrix+0x2c>
      +0x3c: mov    WORD PTR [rsp+0x20],0x0
      +0x43: test   edx,edx
      +0x45: jne    <mlkem768_gen_matrix+0x130>
      +0x4b: mov    esi,0x1
      +0x50: mov    edi,0x2
      +0x55: mov    r8d,0x100
      +0x5b: mov    WORD PTR [rsp+0x60],si
      +0x60: lea    rdx,[rbx+0x400]
      +0x67: lea    rsi,[rbx+0x200]
      +0x6e: mov    WORD PTR [rsp+0xa0],di
      +0x76: lea    rcx,[rbx+0x600]
      +0x7d: mov    rdi,rbx
      +0x80: mov    WORD PTR [rsp+0xe0],r8w
      +0x89: mov    r8,r12
      +0x8c: call   <mlkem_poly_rej_uniform_x4>
      +0x91: mov    edi,0x2
      +0x96: xor    esi,esi
      +0x98: mov    eax,0x1
      +0x9d: mov    edx,0x2
      +0xa2: movzx  ecx,WORD PTR [rip+0x1c27]
      +0xa9: mov    BYTE PTR [rsp+0x60],dl
      +0xad: mov    r8,r12
      +0xb0: mov    BYTE PTR [rsp+0xa1],dil
      +0xb8: lea    rdi,[rbx+0x800]
      +0xbf: mov    WORD PTR [rsp+0x20],cx
      +0xc4: lea    rcx,[rbx+0xe00]
      +0xcb: mov    BYTE PTR [rsp+0xa0],sil
      +0xd3: lea    rsi,[rbx+0xa00]
      +0xda: mov    BYTE PTR [rsp+0xe1],dl
      +0xe1: lea    rdx,[rbx+0xc00]
      +0xe8: mov    BYTE PTR [rsp+0x61],al
      +0xec: mov    BYTE PTR [rsp+0xe0],al
      +0xf3: call   <mlkem_poly_rej_uniform_x4>
      +0xf8: movzx  eax,WORD PTR [rip+0x1bd3]
      +0xff: lea    rdi,[rbx+0x1000]
     +0x106: mov    rsi,r12
     +0x109: mov    WORD PTR [rsp+0x20],ax
     +0x10e: call   <mlkem_poly_rej_uniform>
     +0x113: xor    eax,eax
     +0x115: mov    rdi,r12
     +0x118: mov    ecx,0x20
     +0x11d: rep    stos QWORD PTR es:[rdi],rax
     +0x120: lea    rsp,[rbp-0x10]
     +0x124: pop    rbx
     +0x125: pop    r12
     +0x127: pop    rbp
     +0x128: ret
     +0x129: nop    DWORD PTR [rax+0x0]
     +0x130: mov    edx,0x200
     +0x135: mov    ecx,0x1
     +0x13a: mov    rdi,rbx
     +0x13d: mov    r8,r12
     +0x140: mov    eax,0x100
     +0x145: mov    WORD PTR [rsp+0xa0],dx
     +0x14d: lea    rsi,[rbx+0x200]
     +0x154: lea    rdx,[rbx+0x400]
     +0x15b: mov    WORD PTR [rsp+0xe0],cx
     +0x163: lea    rcx,[rbx+0x600]
     +0x16a: mov    WORD PTR [rsp+0x60],ax
     +0x16f: call   <mlkem_poly_rej_uniform_x4>
     +0x174: xor    edi,edi
     +0x176: mov    esi,0x2
     +0x17b: mov    eax,0x2
     +0x180: mov    edx,0x1
     +0x185: jmp    <mlkem768_gen_matrix+0xa2>
 ***)

let MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem768_gen_matrix"];;

(* ------------------------------------------------------------------------- *)
(* The seed is loaded as two 128-bit words, and stored with the two indices  *)
(* of an entry in a buffer of 64 bytes, as 34 bytes for SHAKE128.            *)
(* ------------------------------------------------------------------------- *)

let GENMAT_BYTES128_HALVES_STMT =
  `!a:int64 n s:x86state.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`;;

let GENMAT_BYTES128_HALVES =
  assume_spec GENMAT_BYTES128_HALVES_STMT;;

let GENMAT_BYTES_32_OF_HALVES_STMT =
  `!a:int64 n s:x86state.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`;;

let GENMAT_BYTES_32_OF_HALVES =
  assume_spec GENMAT_BYTES_32_OF_HALVES_STMT;;

let GENMAT_BYTES2_STMT =
  `(!a s:x86state.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes16 a) s)) /\
   (!a s:x86state.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes8 a) s) +
        256 * val(read (memory :> bytes8(word_add a (word 1))) s))`;;

let GENMAT_BYTES2 =
  assume_spec GENMAT_BYTES2_STMT;;

let GENMAT_INPUT_STMT =
  `!a:int64 (rho:byte list) x y s:x86state.
        LENGTH rho = 32 /\ x < 256 /\ y < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist rho MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist rho DIV 2 EXP 128) /\
        read (memory :> bytes(word_add a (word 32),2)) s = x + 256 * y
        ==> LENGTH(APPEND rho [word x:byte; word y]) = 34 /\
            read (memory :> bytes(a,34)) s =
            num_of_bytelist(APPEND rho [word x; word y])`;;

let GENMAT_INPUT =
  assume_spec GENMAT_INPUT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The four buffers are aligned to 32 bytes within the stack frame, by AND   *)
(* with -32 after the pushes of RBP, R12 and RBX, so their address depends   *)
(* on the stack pointer. The proof uses a variable bot for the address 3424  *)
(* bytes below them, the bottom of the stack of mlkem_poly_rej_uniform_x4,   *)
(* which is stackpointer + (32 - k) for k = val(stackpointer + 3712) MOD 32, *)
(* where stackpointer is the bottom of the 3736 bytes of the stack below the *)
(* return address, with the facts about its alignment and the overlaps of    *)
(* the frame. The addresses in the frame are then bot plus a constant, in    *)
(* the form of the memory addresses of the simulation, to which              *)
(* GENMAT_NORM_TAC also puts the values in registers, and GENMAT_SP n is the *)
(* address n bytes into the buffers.                                         *)
(* ------------------------------------------------------------------------- *)

let GENMAT_FRAME_ADDRESS_STMT =
  `!a:int64.
        word_sub (word_and (word_add a (word 3712))
                           (word 18446744073709551584))
                 (word 256) =
        word_add a (word(3456 - val(word_add a (word 3712)) MOD 32))`;;

let GENMAT_FRAME_ADDRESS =
  assume_spec GENMAT_FRAME_ADDRESS_STMT;;

let GENMAT_ALIGNED_16_STMT =
  `!x:int64. aligned 16 x <=> word_and x (word 15) = word 0`;;

let GENMAT_ALIGNED_16 =
  assume_spec GENMAT_ALIGNED_16_STMT;;

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

let GENMAT3_NONOV_TAC =
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
       [`a:int64,4608`; `seed:int64,32`; `word pc:int64,libmlkem_size`;
        `word_add stackpointer (word 3712):int64,32`]
    else NO_TAC);;

let GENMAT3_FRAME_TAC =
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
     [memory :> bytes(a,4608); memory :> bytes(bot:int64,3680);
      memory :> bytes(word_add stackpointer (word 3712),24)]` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `bot:int64`
      then REWRITE_TAC[th] else NO_TAC) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC];;

let GENMAT3_SETUP_TAC =
  GENMAT_BOT_TAC THEN GENMAT3_FRAME_TAC THEN GENMAT3_NONOV_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12`;;

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
(* frame, which decide the loop that copies the seed, the values stored from *)
(* the low halves of the YMM registers, the upper halves of which are kept   *)
(* as their initial values, and the constants 0x0101 and 0x0202 for the      *)
(* indices (1,1) and (2,2), which are loaded from the image by RIP-relative  *)
(* MOVZX.                                                                    *)
(* ------------------------------------------------------------------------- *)

let GENMAT_PTR_SUB_STMT =
  `!x:int64 a b. word_sub (word_add x (word a)) (word_add x (word b)) =
                 word_sub (word a) (word b)`;;

let GENMAT_PTR_SUB =
  assume_spec GENMAT_PTR_SUB_STMT;;

let GENMAT_PTR_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th) &&
       can (find_term (fun t -> is_const t && name_of t = "word_sub"))
           (concl th)
    then CONV_RULE(REWRITE_CONV[GENMAT_PTR_SUB] THENC
                   DEPTH_CONV WORD_NUM_RED_CONV THENC NUM_REDUCE_CONV) th
    else th);;

let GENMAT_SUBWORD_JOIN_STMT =
  `!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`;;

let GENMAT_SUBWORD_JOIN =
  assume_spec GENMAT_SUBWORD_JOIN_STMT;;

let GENMAT_SSE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GENMAT_SUBWORD_JOIN]);;

(*** The constants for the indices (1,1) and (2,2) in the image ***)

let mlkem_native_gen_matrix_k3_gcc12_O2_data = define
 `mlkem_native_gen_matrix_k3_gcc12_O2_data:byte list =
  [word 1; word 1; word 2; word 2]`;;

let GENMAT3_DATA_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlkem_native_gen_matrix_k3_gcc12_O2_data
   (layout "mlkem512_gen_matrix_consts");;

let GENMAT3_DATA_LOADED_STMT =
  `!pc s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc
          ==> read (memory :> bytes16 (word (pc + mlkem768_gen_matrix_consts))) s = word 257 /\
              read (memory :> bytes16 (word (pc + mlkem768_gen_matrix_const2))) s = word 514`;;

let GENMAT3_DATA_LOADED =
  assume_spec GENMAT3_DATA_LOADED_STMT;;

(*** RIP-relative addresses come out as word(val(word(pc + n)) + d) ***)

let GENMAT_RIPREL_STMT =
  `!x d. word(val(word x:int64) + d):int64 = word(x + d)`;;

let GENMAT_RIPREL =
  assume_spec GENMAT_RIPREL_STMT;;

let GENMAT_RIPREL_TAC ns =
  MAP_EVERY (fun (n,d) ->
    let x = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral n) in
    ASSUME_TAC(CONV_RULE(RAND_CONV(RAND_CONV
      (GEN_REWRITE_CONV I [GSYM ADD_ASSOC] THENC RAND_CONV NUM_REDUCE_CONV)))
     (SPECL [x; mk_small_numeral d] GENMAT_RIPREL)))
   ns;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is 32 bytes at seed, given as a list of bytes *)
(* rho. Entry (i,j) of the matrix, the polynomial at a + 512 * (3 * i + j),  *)
(* is sampled from shake128 of rho followed by the bytes j and i, as for the *)
(* matrix in FIPS 203, or by i and j if transposed (as a 32-bit integer) is  *)
(* nonzero, which gives the transposed matrix. As for                        *)
(* mlkem_poly_rej_uniform, the theorem has the hypothesis that for some k    *)
(* there are at least 256 samples within the first 504 + 168 * k bytes of    *)
(* shake128 for each entry. The proof is by cases on whether transposed is   *)
(* zero, which also decides a branch. The stack is the 3736 bytes below the  *)
(* return address, for the three saved registers, up to 31 bytes for the     *)
(* alignment, the 256 bytes of the buffers and the 3424 used by              *)
(* mlkem_poly_rej_uniform_x4 (or fewer by mlkem_poly_rej_uniform) below      *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLY_REJ_UNIFORM_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REJ_UNIFORM_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup ***)

let GENMAT3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `seed:int64`; `rho:byte list`; `transposed:int64`; `k:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3736 THEN
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

let GENMAT3_CASE_TAC tr =
  let d = if tr then 1 else 0 in
  let st n = mk_var("s"^string_of_int n,`:x86state`) in
  let xy e = let i = e / 3 and j = e mod 3 in if tr then (i,j) else (j,i) in
  let seed e = let x,y = xy e in GENMAT_SEED x y in
  let inputs g s =
    MAP_EVERY (fun m -> let x,y = xy (4 * g + m) in
                        GENMAT_INPUT_TAC (64 * m) x y s) (0--3) in
  let rest = [`k:num`; `pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let args5 = [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
               `read R8 s`] in
  (if tr then
     SUBGOAL_THEN `~(val(word_zx(transposed:int64):int32) = 0)` ASSUME_TAC
     THENL [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC]
   else ALL_TAC) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GENMAT3_DATA_LOADED) THEN
  GENMAT_RIPREL_TAC [25945,7207; 26031,7123] THEN

  (*** The four copies of the seed ***)

  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (1--6) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 3712))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (7--12) THEN
  GENMAT_NORM_TAC THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
     ((13 + 5 * m)--(15 + 5 * m)) THEN
    GENMAT_NORM_TAC THEN GENMAT_SSE_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC [16 + 5 * m] THEN
    GENMAT_PTR_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC [17 + 5 * m])
   (0--3) THEN

  (*** The first four entries ***)

  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (33--47) THEN
  GENMAT_NORM_TAC THEN
  inputs 0 (st 47) THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 3) (e mod 3)) (0--8) THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (0--3) @ rest) 48 THEN
  GENMAT_NORM_TAC THEN GENMAT_TOBYTES_TAC THEN

  (*** The next four ***)

  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (49--(66 + d)) THEN
  GENMAT_NORM_TAC THEN
  inputs 1 (st(66 + d)) THEN
  LOCAL_POLY_REJ_UNIFORM_X4_TAC (args5 @ map seed (4--7) @ rest) (67 + d)
  THEN GENMAT_NORM_TAC THEN GENMAT_TOBYTES_TAC THEN

  (*** The last one ***)

  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
   ((68 + d)--(72 + d)) THEN
  GENMAT_NORM_TAC THEN
  (let x,y = xy 8 in GENMAT_INPUT_TAC 0 x y (st(72 + d))) THEN
  LOCAL_POLY_REJ_UNIFORM_TAC
   ([`read RDI s`; `read RSI s`; seed 8] @ rest) (73 + d) THEN
  GENMAT_NORM_TAC THEN GENMAT_TOBYTES_TAC THEN

  (*** Zeroing the buffers and the return ***)

  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
   ((74 + d)--(82 + d)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN GENMAT_FINAL_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a seed (rho:byte list) transposed k pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH rho = 32 /\
        (!i j. i < 3 /\ j < 3
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
        nonoverlapping (a,4608) (word_sub stackpointer (word 3736),3744) /\
        ALLPAIRS nonoverlapping
         [(a,4608); (word_sub stackpointer (word 3736),3744)]
         [(seed,32); (word pc,libmlkem_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem768_gen_matrix) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed; transposed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist rho)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i j. i < 3 /\ j < 3
                        ==> wordlist_from_memory
                             (word_add a (word(512 * (3 * i + j))),256) s =
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
               [memory :> bytes(a,4608);
                memory :> bytes(word_sub stackpointer (word 3736),3736)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses, rho and the flag, through the samples of each entry, which are *)
(* public. They are given by cases on the flag, which gives the order of the *)
(* indices and a branch, and the address bot is expanded in them at the end  *)
(* by GENMAT_UNBOT_TAC, since it is not an argument of the template.         *)
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

let GENMAT3_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_X4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_X1" THEN
  CONCRETIZE_F_EVENTS_TAC GENMAT_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GENMAT3_INTRO_TAC THEN GENMAT3_SETUP_TAC;;

let GENMAT3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GENMAT_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let GENMAT_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64` &&
       is_binary "word_add" (lhs(concl th))
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

let GENMAT3_SAFE_CASE_TAC tr =
  let d = if tr then 1 else 0 in
  let st n = mk_var("s"^string_of_int n,`:x86state`) in
  let xy e = let i = e / 3 and j = e mod 3 in if tr then (i,j) else (j,i) in
  let seed e = let x,y = xy e in GENMAT_SEED x y in
  let inputs g s =
    MAP_EVERY (fun m -> let x,y = xy (4 * g + m) in
                        GENMAT_INPUT_TAC (64 * m) x y s) (0--3) in
  let rest = [`k:num`; `pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let args5 = [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
               `read RDX s`; `read RCX s`; `read R8 s`] in
  (if tr then
     SUBGOAL_THEN `~(val(word_zx(transposed:int64):int32) = 0)` ASSUME_TAC
     THENL [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC]
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
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GENMAT3_DATA_LOADED) THEN
  GENMAT_RIPREL_TAC [25945,7207; 26031,7123] THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (1--6) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 3712))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (7--12) THEN
  GENMAT_NORM_TAC THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
     ((13 + 5 * m)--(15 + 5 * m)) THEN
    GENMAT_NORM_TAC THEN GENMAT_SSE_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC [16 + 5 * m] THEN
    GENMAT_PTR_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC [17 + 5 * m])
   (0--3) THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (33--47) THEN
  GENMAT_NORM_TAC THEN
  inputs 0 (st 47) THEN
  MAP_EVERY (fun e -> GENMAT_HYP_TAC (e / 3) (e mod 3)) (0--8) THEN
  GENMAT3_SAFE_CALL_TAC "H_X4" (args5 @ map seed (0--3) @ rest) 48 THEN
  GENMAT_NORM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC (49--(66 + d)) THEN
  GENMAT_NORM_TAC THEN
  inputs 1 (st(66 + d)) THEN
  GENMAT3_SAFE_CALL_TAC "H_X4" (args5 @ map seed (4--7) @ rest) (67 + d)
  THEN GENMAT_NORM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
   ((68 + d)--(72 + d)) THEN
  GENMAT_NORM_TAC THEN
  (let x,y = xy 8 in GENMAT_INPUT_TAC 0 x y (st(72 + d))) THEN
  GENMAT3_SAFE_CALL_TAC "H_X1"
   ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`; seed 8] @ rest)
   (73 + d) THEN
  GENMAT_NORM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_EXEC
   ((74 + d)--(82 + d)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  GENMAT_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
   forall e a seed (rho:byte list) transposed k pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH rho = 32 /\
        (!i j. i < 3 /\ j < 3
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
        nonoverlapping (a,4608) (word_sub stackpointer (word 3736),3744) /\
        ALLPAIRS nonoverlapping
         [(a,4608); (word_sub stackpointer (word 3736),3744)]
         [(seed,32); (word pc,libmlkem_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem768_gen_matrix) /\
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
                            (word_sub stackpointer (word 3736))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; a,4608;
                       word_sub stackpointer (word 3736),3744;
                       word(pc + rodata_mlk_KeccakF_RoundConstants),192; word(pc + mlkem768_gen_matrix_consts),4]
                      [a,4608; word_sub stackpointer (word 3736),3736]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,4608);
                memory :> bytes(word_sub stackpointer (word 3736),3736)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
