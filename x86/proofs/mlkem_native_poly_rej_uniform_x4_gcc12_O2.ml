(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials from four seeds by rejection. This   *)
(* is the code for mlkem_poly_rej_uniform_x4 from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which absorbs the four seeds of 34 bytes, 64 bytes apart, into a fourfold *)
(* SHAKE128 state, squeezes three blocks of 168 bytes of each and samples    *)
(* the coefficients below 3329 from them with mlk_rej_uniform_c, and then    *)
(* squeezes one more block of each and samples from all four until each      *)
(* polynomial has 256 coefficients, before zeroing the state and the         *)
(* buffers. It is verified in the whole image (see                           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x60e0, using  *)
(* the theorems for mlkem_shake128x4_init at 0x3820,                         *)
(* mlkem_shake128x4_absorb_once at 0x3720, mlkem_shake128x4_squeezeblocks at *)
(* 0x3780, mlkem_shake128x4_release at 0x3830 and mlk_rej_uniform_c at       *)
(* 0x6040 in the image, and the lemmas about the samples for                 *)
(* mlkem_poly_rej_uniform.                                                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_poly_rej_uniform_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128x4_init_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128x4_absorb_once_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128x4_squeezeblocks_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_shake128x4_release_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    60e0: push   rbp
    60e1: mov    rbp,rsp
    60e4: push   r15
    60e6: push   r14
    60e8: push   r13
    60ea: mov    r13,rdi
    60ed: push   r12
    60ef: mov    r12,rsi
    60f2: push   rbx
    60f3: mov    rbx,r8
    60f6: and    rsp,0xffffffffffffffe0
    60fa: sub    rsp,0xb60
    6101: lea    r15,[rsp+0x40]
    6106: mov    QWORD PTR [rsp+0x8],rdi
    610b: lea    r14,[rsp+0x360]
    6113: mov    rdi,r15
    6116: mov    QWORD PTR [rsp],rsi
    611a: mov    QWORD PTR [rsp+0x20],rdx
    611f: mov    QWORD PTR [rsp+0x18],rcx
    6124: mov    QWORD PTR [rsp+0x10],r15
    6129: call   3820 <mlkem_shake128x4_init>
    612e: lea    rdx,[rbx+0x40]
    6132: mov    rsi,rbx
    6135: mov    rdi,r15
    6138: lea    rcx,[rbx+0x80]
    613f: lea    r8,[rbx+0xc0]
    6146: mov    rbx,r15
    6149: mov    r9d,0x22
    614f: call   3720 <mlkem_shake128x4_absorb_once>
    6154: lea    r15,[rsp+0x560]
    615c: mov    r9,rbx
    615f: mov    rdi,r14
    6162: lea    rax,[rsp+0x960]
    616a: lea    r11,[rsp+0x760]
    6172: mov    r8d,0x3
    6178: mov    rsi,r15
    617b: mov    rcx,rax
    617e: mov    rdx,r11
    6181: mov    rbx,r11
    6184: mov    QWORD PTR [rsp+0x38],rax
    6189: mov    QWORD PTR [rsp+0x30],r11
    618e: call   3780 <mlkem_shake128x4_squeezeblocks>
    6193: xor    esi,esi
    6195: mov    rdi,r13
    6198: mov    ecx,0x1f8
    619d: mov    rdx,r14
    61a0: call   6040 <mlk_rej_uniform_c.constprop.0>
    61a5: xor    esi,esi
    61a7: mov    rdi,r12
    61aa: mov    ecx,0x1f8
    61af: mov    rdx,r15
    61b2: mov    r13d,eax
    61b5: call   6040 <mlk_rej_uniform_c.constprop.0>
    61ba: mov    rdi,QWORD PTR [rsp+0x20]
    61bf: mov    rdx,rbx
    61c2: xor    esi,esi
    61c4: mov    ecx,0x1f8
    61c9: mov    r12d,eax
    61cc: call   6040 <mlk_rej_uniform_c.constprop.0>
    61d1: mov    rdx,QWORD PTR [rsp+0x38]
    61d6: mov    rdi,QWORD PTR [rsp+0x18]
    61db: xor    esi,esi
    61dd: mov    ecx,0x1f8
    61e2: mov    ebx,eax
    61e4: call   6040 <mlk_rej_uniform_c.constprop.0>
    61e9: cmp    r12d,0xff
    61f0: mov    r10d,eax
    61f3: setbe  al
    61f6: cmp    r13d,0xff
    61fd: jmp    62a0 <mlkem_poly_rej_uniform_x4+0x1c0>
    6202: nop    WORD PTR [rax+rax*1+0x0]
    6208: mov    r9,QWORD PTR [rsp+0x10]
    620d: mov    rcx,QWORD PTR [rsp+0x38]
    6212: mov    rsi,r15
    6215: mov    rdi,r14
    6218: mov    rdx,QWORD PTR [rsp+0x30]
    621d: mov    r8d,0x1
    6223: mov    DWORD PTR [rsp+0x2c],r10d
    6228: call   3780 <mlkem_shake128x4_squeezeblocks>
    622d: mov    rdi,QWORD PTR [rsp+0x8]
    6232: mov    esi,r13d
    6235: mov    rdx,r14
    6238: mov    ecx,0xa8
    623d: call   6040 <mlk_rej_uniform_c.constprop.0>
    6242: mov    rdi,QWORD PTR [rsp]
    6246: mov    esi,r12d
    6249: mov    rdx,r15
    624c: mov    ecx,0xa8
    6251: mov    r13d,eax
    6254: call   6040 <mlk_rej_uniform_c.constprop.0>
    6259: mov    rdx,QWORD PTR [rsp+0x30]
    625e: mov    rdi,QWORD PTR [rsp+0x20]
    6263: mov    esi,ebx
    6265: mov    ecx,0xa8
    626a: mov    r12d,eax
    626d: call   6040 <mlk_rej_uniform_c.constprop.0>
    6272: mov    rdx,QWORD PTR [rsp+0x38]
    6277: mov    esi,DWORD PTR [rsp+0x2c]
    627b: mov    ecx,0xa8
    6280: mov    rdi,QWORD PTR [rsp+0x18]
    6285: mov    ebx,eax
    6287: call   6040 <mlk_rej_uniform_c.constprop.0>
    628c: cmp    r13d,0xff
    6293: mov    r10d,eax
    6296: setbe  al
    6299: cmp    r12d,0xff
    62a0: setbe  dl
    62a3: or     eax,edx
    62a5: cmp    ebx,0xff
    62ab: setbe  dl
    62ae: or     al,dl
    62b0: jne    6208 <mlkem_poly_rej_uniform_x4+0x128>
    62b6: cmp    r10d,0xff
    62bd: jbe    6208 <mlkem_poly_rej_uniform_x4+0x128>
    62c3: mov    rdi,QWORD PTR [rsp+0x10]
    62c8: call   3830 <mlkem_shake128x4_release>
    62cd: xor    eax,eax
    62cf: mov    rdi,r14
    62d2: mov    ecx,0x100
    62d7: rep    stos QWORD PTR es:[rdi],rax
    62da: lea    rsp,[rbp-0x28]
    62de: pop    rbx
    62df: pop    r12
    62e1: pop    r13
    62e3: pop    r14
    62e5: pop    r15
    62e7: pop    rbp
    62e8: ret
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x60e0,0x62e9];;

(* ------------------------------------------------------------------------- *)
(* The samples from one more block, whatever the number of samples so far:   *)
(* if there are already 256, mlk_rej_uniform_c adds none, as there is no     *)
(* room for more, as on AArch64.                                             *)
(* ------------------------------------------------------------------------- *)

let REJX4_SAMPLE_SUC = prove
 (`!(f:num->byte) j.
        SUB_LIST(0,256)
         (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
            (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
        APPEND
         (SUB_LIST(0,256)
           (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
              (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
         (SUB_LIST(0,256 -
                   MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j)))))))
           (REJ_SAMPLE(wordlist_of_num 112
              (num_of_bytelist
                (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_FIELDS_SUC; REJ_SAMPLE_APPEND] THEN
  MAP_EVERY (fun (t,v) -> SPEC_TAC(t,v))
   [`REJ_SAMPLE(wordlist_of_num 112 (num_of_bytelist
      (list_of_seq (\i. (f:num->byte)((504 + 168 * j) + i)) 168)))`,
    `l2:int16 list`;
    `REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
      (num_of_bytelist(list_of_seq (f:num->byte) (504 + 168 * j))))`,
    `l1:int16 list`] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LENGTH(l1:int16 list) <= 256` THENL
   [ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT; SUB_LIST_REFL;
                 ARITH_RULE `x <= 256 ==> MIN 256 x = x`];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT; LT_IMP_LE; SUB_REFL;
                 ARITH_RULE `256 < x ==> MIN 256 x = 256`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; APPEND_NIL]]);;

let REJX4_ARGS_32_TAC c =
  MP_TAC(SPEC c WORD_ZX_32_SMALL) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if (is_binary "<" (concl th) || is_binary "<=" (concl th)) &&
         lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

(* ------------------------------------------------------------------------- *)
(* The fourfold state of 800 bytes and the four buffers of 512 bytes for     *)
(* three blocks each after it are aligned to 32 bytes within the stack       *)
(* frame, by AND with -32 after the pushes, so the frame is at stackpointer  *)
(* + (456 - k) for k = val(stackpointer + 3368) MOD 32, where stackpointer   *)
(* is the bottom of the 3416 bytes of the stack below the return address.    *)
(* The addresses in the frame, REJX4_SP n, are in the form of the memory     *)
(* addresses of the simulation, word_add stackpointer (word((456 - k) + n)), *)
(* and those of the states and buffers in the form of the addresses in the   *)
(* preconditions of the calls, to which REJX4_NORM_TAC also puts the values  *)
(* in registers and the stack pointer and the regions of the stack of the    *)
(* callees.                                                                  *)
(* ------------------------------------------------------------------------- *)

let REJX4_FRAME_ADDRESS = prove
 (`!a:int64.
        word_sub (word_and (word_add a (word 3368))
                           (word 18446744073709551584))
                 (word 2912) =
        word_add a (word(456 - val(word_add a (word 3368)) MOD 32))`,
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
  MP_TAC(SPECL [`val(word_add a (word 3368):int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`val(word_add a (word 3368):int64) MOD 32`,`k:num`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`456`,`x:num`; `k:num`,`y:num`]
    (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k < 32` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

let REJX4_K = `val(word_add (stackpointer:int64) (word 3368)) MOD 32`;;

let REJX4_SP =
  let base = mk_comb(`word_add (stackpointer:int64)`,
                     mk_comb(`word:num->int64`,
                       mk_binop `(-):num->num->num` `456` REJX4_K)) in
  fun n ->
    if n = 0 then base else
    rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV
      (mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
               mk_comb(`word:num->int64`,mk_small_numeral n)))));;

let REJX4_STB = REJX4_SP 64;;

let REJX4_ST m =
  if m = 0 then REJX4_STB else
  rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV
    (mk_comb(mk_comb(`word_add:int64->int64->int64`,REJX4_STB),
             mk_comb(`word:num->int64`,mk_small_numeral(200 * m))))));;

let REJX4_BUF m = REJX4_SP(864 + 512 * m);;

let REJX4_NORM_TAC =
  let k = REJX4_K in
  let kth = REWRITE_RULE[ARITH_EQ]
   (SPECL [`val(word_add (stackpointer:int64) (word 3368))`; `32`]
          MOD_LT_EQ) in
  let mk t = subst [k,`k:num`] t in
  let th1 = prove(mk `word_sub (word (456 - k)) (word 8):int64 =
                      word (448 - k)`,
    MP_TAC kth THEN SPEC_TAC(k,`k:num`) THEN REPEAT STRIP_TAC THEN
    MP_TAC(INST [`456`,`x:num`; `k:num`,`y:num`]
                (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
    MP_TAC(INST [`448`,`x:num`; `k:num`,`y:num`]
                (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    CONV_TAC WORD_RULE)
  and th2 = prove(mk `(448 - k) + 8 = 456 - k`,
    MP_TAC kth THEN SPEC_TAC(k,`k:num`) THEN ARITH_TAC) in
  let wsub d =
    let e = mk_small_numeral(448 - d) and d' = mk_small_numeral d in
    prove(mk(subst [d',`d:num`; e,`e:num`]
               `word_sub (word (448 - k)) (word d):int64 = word (e - k)`),
      MP_TAC kth THEN SPEC_TAC(k,`k:num`) THEN REPEAT STRIP_TAC THEN
      MP_TAC(INST [`448`,`x:num`; `k:num`,`y:num`]
                  (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
      MP_TAC(INST [e,`x:num`; `k:num`,`y:num`]
                  (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
      REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
      CONV_TAC WORD_RULE) in
  let ths = [th1; th2; wsub 416; wsub 336] in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then REWRITE_RULE ths
          (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th)
    else th);;

let REJX4_SETUP_TAC =
  SUBGOAL_THEN
   (subst [REJX4_K,`k:num`]
     `k < 32 /\ 425 <= 456 - k /\ 456 - k <= 456`)
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`val(word_add (stackpointer:int64) (word 3368))`; `32`]
      MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seeds are 34 bytes at seed, seed + 64, seed + 128  *)
(* and seed + 192, given as lists of bytes inp0, ..., inp3. As for           *)
(* mlkem_poly_rej_uniform, the theorem has the hypothesis that for some k    *)
(* there are at least 256 samples among the 12-bit fields of the first 504 + *)
(* 168 * k bytes of shake128 of each seed, and the results are the first 256 *)
(* samples for each. The loop sampling from one more block of each at a time *)
(* stops when there are 256 samples for all four, so the proof uses the      *)
(* minimal such k, k0, as the number of iterations, and the numbers of       *)
(* samples in the invariant are at most 256. The stack is the 3416 bytes     *)
(* below the return address, for the frame of the function, of at most 2991  *)
(* bytes, and the 424 used by mlkem_shake128x4_absorb_once below it.         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INIT_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ABSORB_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REJ_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_RELEASE_X4_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The fields, samples and blocks for each seed, and the least k ***)

let REJX4_INPS =
  [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`]
and REJX4_VECS = [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`]
and REJX4_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let rejx4_fields inp j =
  vsubst [inp,`inp:byte list`; j,`j:num`]
   `wordlist_of_num (336 + 112 * j)
     (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * j))):
    (12 word)list`;;

let rejx4_fields0 inp =
  vsubst [inp,`inp:byte list`]
   `wordlist_of_num 336
     (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list`;;

let rejx4_count inp j =
  mk_comb(`LENGTH:(16 word)list->num`,
          mk_comb(`REJ_SAMPLE`,rejx4_fields inp j));;

let rejx4_block inp i =
  vsubst [inp,`inp:byte list`; i,`i:num`]
   `wordlist_of_num 112
     (num_of_bytelist
       (list_of_seq (\j. shake128 inp ((504 + 168 * i) + j)) 168)):
    (12 word)list`;;

let rejx4_cs0 =
  map (fun inp -> mk_comb(`MIN 256`,
                   rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                         (rejx4_count inp `0`)))))
      REJX4_INPS
and rejx4_cs1 =
  map (fun inp -> mk_comb(`MIN 256`,rejx4_count inp `i + 1`)) REJX4_INPS;;

let REJX4_ABSORBED_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = vsubst [inp,`inp:byte list`] REJ_ABSORBED in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),`34`)) in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SPONGE)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SHAKE128_BLOCKS)))
   (zip REJX4_INPS REJX4_SVS);;

let REJX4_DONE n =
  list_mk_conj
   (map (fun inp -> mk_binop `(<=):num->num->bool` `256` (rejx4_count inp n))
        REJX4_INPS);;

let REJX4_MINIMAL_TAC =
  let p = mk_abs(`n:num`,REJX4_DONE `n:num`) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let REJX4_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

(*** The facts at the intermediate points, with the saved registers ***)

let REJX4_FRAME =
  subst [REJX4_SP 0,`f0:int64`; REJX4_SP 8,`f8:int64`;
         REJX4_SP 16,`f16:int64`; REJX4_SP 24,`f24:int64`;
         REJX4_SP 32,`f32:int64`; REJX4_SP 48,`f48:int64`;
         REJX4_SP 56,`f56:int64`; REJX4_STB,`st:int64`;
         REJX4_BUF 0,`b0:int64`; REJX4_BUF 1,`b1:int64`;
         REJX4_BUF 2,`b2:int64`; REJX4_BUF 3,`b3:int64`]
 `read RSP s = f0 /\
  read RBP s = word_add stackpointer (word 3408) /\
  read (memory :> bytes64 (word_add stackpointer (word 3368))) s =
  rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3376))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3384))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3392))) s =
  r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3400))) s =
  r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3408))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3416))) s =
  returnaddress /\
  read (memory :> bytes64 f0) s = vec1 /\
  read (memory :> bytes64 f8) s = vec0 /\
  read (memory :> bytes64 f16) s = st /\
  read (memory :> bytes64 f24) s = vec3 /\
  read (memory :> bytes64 f32) s = vec2 /\
  read (memory :> bytes64 f48) s = b2 /\
  read (memory :> bytes64 f56) s = b3 /\
  read R14 s = b0 /\ read R15 s = b1 /\
  (read DF s <=> false)`;;

let REJX4_POLY =
 `read (R:(x86state,int64)component) s =
  word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))) /\
  read (memory :> bytes(vec,2 * MIN 256 (LENGTH(REJ_SAMPLE
    (wordlist_of_num (336 + 112 * i)
      (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))))) s =
  num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
    (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (3 + i) (S:1600 word))`;;

let REJX4_POLYS regs =
  flat
   (map (fun (r,(vec,(inp,(st,sv)))) ->
          conjuncts
           (vsubst [r,`R:(x86state,int64)component`; vec,`vec:int64`;
                    inp,`inp:byte list`; st,`st:int64`; sv,`S:1600 word`]
                   REJX4_POLY))
        (zip regs (zip REJX4_VECS (zip REJX4_INPS
           (zip (map REJX4_ST (0--3)) REJX4_SVS)))));;

let REJX4_A1 =
  let t = vsubst [`0`,`i:num`]
           (list_mk_conj(REJX4_POLYS [`R13`; `R12`; `RBX`; `RAX`])) in
  let t' = rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] t)) in
  mk_abs(`s:x86state`,list_mk_conj(conjuncts t' @ conjuncts REJX4_FRAME));;

let REJX4_INV =
  list_mk_abs([`i:num`; `s:x86state`],
    list_mk_conj(REJX4_POLYS [`R13`; `R12`; `RBX`; `R10`] @
                 conjuncts REJX4_FRAME));;

let REJX4_A2 =
  let res inp vec =
    vsubst [inp,`inp:byte list`; vec,`vec:int64`]
     `read (memory :> bytes(vec,512)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * k)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * k))))))` in
  mk_abs(`s:x86state`,
    list_mk_conj(map2 res REJX4_INPS REJX4_VECS @ conjuncts REJX4_FRAME));;

(*** Calls of mlk_rej_uniform_c on the first three blocks ***)

let REJX4_INPUT0_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->x86state->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`336`); s]),
          rejx4_fields0 inp))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `504` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `504 = 168 * 3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`336`; rand(rejx4_fields0 inp)] LENGTH_WORDLIST_OF_NUM));;

let REJX4_CALL0_TAC m n =
  let inp = el m REJX4_INPS in
  REJX4_INPUT0_TAC m (mk_var("s"^string_of_int(n-1),`:x86state`)) THEN
  LOCAL_REJ_X4_TAC [`read RDI s`; `0`; `read RDX s`; `504`; rejx4_fields0 inp;
                    `pc:num`; `read RSP s`;
                    `read (memory :> bytes64(read RSP s)) s`] n THEN
  REJX4_NORM_TAC THEN REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl));;

let REJX4_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 3 && String.sub n 0 2 = "ci"
  | _ -> false;;

let REJX4_ABBREV_TAC =
  MAP_EVERY (fun m ->
    let t = mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`) in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("ci"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> REJX4_IS_ABBREV(concl th)) asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let REJX4_ABBREV m =
  let eq = mk_eq(mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`),
                 mk_var("ci"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th))
            asl;;

(*** Calls of mlk_rej_uniform_c on one more block, and their results ***)

let REJX4_BLOCK_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->x86state->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`112`); s]),
          rejx4_block inp `i:num`))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `168` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `!k n. n <= 168 ==> a = b`) (concl th) &&
         free_in inp (concl th)
      then MP_TAC(SPECL [`3 + i`; `168`] th) else NO_TAC) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `168 * (3 + i) = 504 + 168 * i`;
                ARITH_RULE `(3 + i) + 1 = 3 + i + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rejx4_block inp `i:num`)] LENGTH_WORDLIST_OF_NUM));;

let REJX4_COMBINE_TAC m n =
  let inp = el m REJX4_INPS and vec = el m REJX4_VECS in
  let c = mk_var("ci"^string_of_int m,`:num`)
  and s = mk_var("s"^string_of_int n,`:x86state`) in
  let l1 = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                   mk_comb(`REJ_SAMPLE`,rejx4_fields inp `i:num`))
  and l2 = mk_comb(mk_comb(`SUB_LIST:num#num->(16 word)list->(16 word)list`,
                           mk_pair(`0`,mk_binop `(-):num->num->num` `256` c)),
                   mk_comb(`REJ_SAMPLE`,rejx4_block inp `i:num`)) in
  let lenl1 = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l1),c) in
  REJ_POST_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  SUBGOAL_THEN lenl1 ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [vec; c; l1; l2; s] REJ_BYTES16_APPEND_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  W(fun gl ->
    let th = REWRITE_RULE [REJX4_ABBREV m gl]
             (ISPECL [mk_comb(`shake128`,inp); `i:num`] REJX4_SAMPLE_SUC) in
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
    MP_TAC(AP_TERM `LENGTH:(16 word)list->num` th)) THEN
  REWRITE_TAC[LENGTH_APPEND; ASSUME lenl1] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [LENGTH_SUB_LIST] THEN
  REWRITE_TAC[SUB_0] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]));;

let REJX4_CALL_TAC m n =
  let inp = el m REJX4_INPS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  REJX4_ARGS_32_TAC c THEN
  REJX4_BLOCK_TAC m (mk_var("s"^string_of_int(n-1),`:x86state`)) THEN
  LOCAL_REJ_X4_TAC [`read RDI s`; c; `read RDX s`; `168`;
                    rejx4_block inp `i:num`; `pc:num`; `read RSP s`;
                    `read (memory :> bytes64(read RSP s)) s`] n THEN
  REJX4_NORM_TAC THEN REJX4_COMBINE_TAC m n;;

(* ------------------------------------------------------------------------- *)
(* The loop test compares three of the numbers of samples with 255 and       *)
(* combines the results of SETBE by OR, branching back if any is below 256,  *)
(* and otherwise compares the fourth. The upper bits of the OR come from RDX *)
(* after a call, so the proof introduces a variable for them, and            *)
(* REJX4_JNE_TAC shows that the first test is that of the three numbers by a *)
(* lemma for the form at hand, proved by WORD_BLAST, rewriting the RIP and   *)
(* the events with it, as REJX4_HI_TAC does with REJ_HI_LEMMA. The proof     *)
(* splits on the outcomes of the two tests.                                  *)
(* ------------------------------------------------------------------------- *)

let REJX4_BYTE_MOD = prove
 (`!x:N word. word(val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[word_zx] THEN
  MP_TAC(ISPEC `val(x:N word)` (INST_TYPE [`:8`,`:N`] WORD_MOD_SIZE)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let REJX4_IS_EVENTS th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("events",_)),_)),
         _) -> true
  | _ -> false;;

let REJX4_HI_TAC c =
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` c `2 EXP 32`) (fun bth ->
    let th = MP (SPEC c REJ_HI_LEMMA) bth in
    RULE_ASSUM_TAC(fun th' ->
      if (is_eq(concl th') && is_cond(rand(concl th'))) || REJX4_IS_EVENTS th'
      then REWRITE_RULE[th] th' else th')) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if (is_binary "<" (concl th) || is_binary "<=" (concl th)) &&
         lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    ALL_TAC];;

let REJX4_JNE_TAC cs =
  let ats = map (fun c -> mk_binop `(<):num->num->bool` `255` c) cs in
  let ps = map (fun i -> mk_var("p"^string_of_int i,`:bool`))
               (0--(length ats - 1)) in
  let is_ws t =
    match strip_comb t with Const("word_subword",_),[_;_] -> true | _ -> false
  and is_wj t =
    match strip_comb t with Const("word_join",_),[_;_] -> true | _ -> false in
  let mth = ARITH_RULE `255 < MIN 256 x <=> 256 <= x` in
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),
           Comb(Comb(Comb(Const("COND",_),c),_),_))
        when forall (fun a -> free_in a c) ats ->
        let ys = setify(filter (fun y -> not(is_var y) && not(is_wj y))
                   (map (fun t -> hd(snd(strip_comb t)))
                        (find_terms is_ws c))) in
        let xs = map (fun i -> mk_var("x"^string_of_int i,
                                      type_of(el i ys)))
                     (0--(length ys - 1)) in
        let c' = subst (zip ps ats @ zip xs ys) c in
        let lth = prove(list_mk_forall(frees c',
                                       mk_eq(c',mk_neg(list_mk_conj ps))),
          REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC ps THEN
          REWRITE_TAC[VAL_EQ_0; REJX4_BYTE_MOD] THEN CONV_TAC WORD_BLAST) in
        let ith = INST (zip ats ps @ zip ys xs) (SPEC_ALL lth) in
        ASSUME_TAC(REWRITE_RULE[ith; mth] th) THEN
        RULE_ASSUM_TAC(fun th' ->
          if REJX4_IS_EVENTS th' then REWRITE_RULE[ith; mth] th' else th')
    | _ -> NO_TAC);;

let REJX4_IS_RIP_COND th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),
         Comb(Comb(Comb(Const("COND",_),_),_),_)) -> true
  | _ -> false;;

let REJX4_RIP_CASES_TAC =
  FIRST_ASSUM(fun th ->
    if not(REJX4_IS_RIP_COND th) then NO_TAC else
    let c = lhand(rator(rand(concl th))) in
    let p = if is_neg c then rand c else c in
    ASM_CASES_TAC p THEN
    POP_ASSUM(fun cth ->
      ASSUME_TAC cth THEN
      RULE_ASSUM_TAC(fun th' ->
        if REJX4_IS_RIP_COND th' then REWRITE_RULE[cth] th' else th')));;

let REJX4_RIP_SIMP_TAC =
  FIRST_X_ASSUM(fun th ->
    if not(REJX4_IS_RIP_COND th) then NO_TAC else
    fun (asl,w as gl) ->
      ASSUME_TAC(REWRITE_RULE
        (ARITH_RULE `255 < MIN 256 x <=> 256 <= x` :: map snd asl) th) gl);;

let REJX4_JBE_TAC c =
  REJX4_HI_TAC c THEN REJX4_RIP_SIMP_TAC;;

(*** the fourth does not, from the negation of all four               ***)

let REJX4_FOURTH_TAC =
  FIRST_ASSUM(fun cth ->
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_neg(concl th) && length(conjuncts(rand(concl th))) = 4)) THEN
    REWRITE_TAC[cth] THEN DISCH_TAC);;

(*** The parts of the proof ***)

let REJX4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`; `seed:int64`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `k:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3416 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

(*** The parts of the proof ***)

let REJX4_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJX4_FRAME_ADDRESS]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (13--21) THEN
  REJX4_NORM_TAC THEN
  LOCAL_INIT_X4_TAC [`read RDI s`; `pc:num`; `read RSP s`;
                     `read (memory :> bytes64(read RSP s)) s`] 22 THEN
  REJX4_NORM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (23--30) THEN
  REJX4_NORM_TAC THEN
  LOCAL_ABSORB_X4_TAC
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `34`; `num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
    `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 31 THEN
  REJX4_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (32--44) THEN
  REJX4_NORM_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `3`; `read R9 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 45 THEN
  REJX4_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  MAP_EVERY (fun (m,(a,b)) ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (a--b) THEN
    REJX4_NORM_TAC THEN REJX4_CALL0_TAC m (b + 1))
   [0,(46,50); 1,(52,57); 2,(59,64); 3,(66,71)] THEN
  MAP_EVERY REJX4_ARGS_32_TAC (butlast rejx4_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The parts of the proof ***)

let REJX4_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--11) THEN
  MAP_EVERY REJX4_HI_TAC (butlast rejx4_cs0) THEN
  REJX4_JNE_TAC (butlast rejx4_cs0) THEN
  REJX4_ARGS_32_TAC (last rejx4_cs0) THEN REJX4_RIP_SIMP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (12--13) THEN
  REJX4_JBE_TAC (last rejx4_cs0) THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) rejx4_cs0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `0`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[];;

(*** The first test, when more blocks are needed, to the loop ***)

let REJX4_LOOP_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--11) THEN
  MAP_EVERY REJX4_HI_TAC (butlast rejx4_cs0) THEN
  REJX4_JNE_TAC (butlast rejx4_cs0) THEN
  REJX4_ARGS_32_TAC (last rejx4_cs0) THEN
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (REJX4_DONE `0`)))))
  ASSUME_TAC THENL
   [REJX4_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REJX4_RIP_CASES_TAC THENL
   [REJX4_FOURTH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (12--13) THEN
    REJX4_JBE_TAC (last rejx4_cs0);
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[];;

(*** The loop body, from 3 + i blocks of each to 3 + i + 1 ***)

let REJX4_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REJX4_ABBREV_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Squeezing one more block from each state ***)

  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--8) THEN
  REJX4_NORM_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `1`; `read R9 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `keccak_squeeze (3 + i) (S1:1600 word)`;
    `keccak_squeeze (3 + i) (S2:1600 word)`;
    `keccak_squeeze (3 + i) (S3:1600 word)`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 9 THEN
  REJX4_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN

  (*** Sampling from each block after the samples so far ***)

  MAP_EVERY (fun (m,(a,b)) ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (a--b) THEN
    REJX4_NORM_TAC THEN REJX4_CALL_TAC m (b + 1))
   [0,(10,14); 1,(16,21); 2,(23,28); 3,(30,35)] THEN
  MAP_EVERY REJX4_ARGS_32_TAC (butlast rejx4_cs1) THEN

  (*** The test of whether there are 256 samples for all four now ***)

  ABBREV_TAC `rdx0 = read RDX s36` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (37--46) THEN
  MAP_EVERY REJX4_HI_TAC (butlast rejx4_cs1) THEN
  REJX4_JNE_TAC (butlast rejx4_cs1) THEN
  REJX4_ARGS_32_TAC (last rejx4_cs1) THEN
  ASM_CASES_TAC `i + 1 < k0` THENL
   [SUBGOAL_THEN (mk_neg(REJX4_DONE `i + 1`)) ASSUME_TAC THENL
     [REJX4_MINIMALITY_TAC `i + 1` THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REJX4_RIP_CASES_TAC THENL
     [REJX4_FOURTH_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC
       (47--48) THEN
      REJX4_JBE_TAC (last rejx4_cs1);
      ALL_TAC];
    SUBGOAL_THEN (REJX4_DONE `i + 1`) STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REJX4_RIP_SIMP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (47--48) THEN
    REJX4_JBE_TAC (last rejx4_cs1)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJX4_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun inp ->
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `k0:num`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   REJX4_INPS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJX4_LOOP_TAC =
  ENSURES_WHILE_UP2_TAC `k0:num` `pc + 0x6208` `pc + 0x62c3` REJX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; REJX4_LOOP_INIT_TAC; REJX4_BODY_TAC; REJX4_EXIT_TAC];;

(*** Releasing the state, zeroing the buffers and the return ***)

let REJX4_FINAL_TAC =
  let tac inp =
    let l = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                    mk_comb(`REJ_SAMPLE`,rejx4_fields inp `k:num`)) in
    let lth = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l),`256`) in
    SUBGOAL_THEN lth ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                  ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME lth)] THEN
    MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN REWRITE_TAC[ASSUME lth] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] in
  REPEAT CONJ_TAC THENL map tac REJX4_INPS;;

let REJX4_PART3_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--2) THEN
  REJX4_NORM_TAC THEN
  LOCAL_RELEASE_X4_TAC [`read RDI s`; `pc:num`; `read RSP s`;
                        `read (memory :> bytes64(read RSP s)) s`] 3 THEN
  REJX4_NORM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (4--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REJX4_FINAL_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!vec0 vec1 vec2 vec3 seed (inp0:byte list) (inp1:byte list)
   (inp2:byte list) (inp3:byte list) k pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        LENGTH inp0 = 34 /\ LENGTH inp1 = 34 /\
        LENGTH inp2 = 34 /\ LENGTH inp3 = 34 /\
        ALL (\inp. 256 <= LENGTH(FILTER (\x. val x < 3329)
                            (MAP (word_zx:12 word->16 word)
                              (wordlist_of_num (336 + 112 * k)
                                (num_of_bytelist
                                  (list_of_seq (shake128 inp)
                                               (504 + 168 * k)))))))
            [inp0; inp1; inp2; inp3] /\
        PAIRWISE nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3416),3424)] /\
        ALLPAIRS nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3416),3424)]
         [(seed,34); (word_add seed (word 64),34);
          (word_add seed (word 128),34); (word_add seed (word 192),34);
          (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x60e0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = num_of_bytelist inp0 /\
                  read (memory :> bytes(word_add seed (word 64),34)) s =
                  num_of_bytelist inp1 /\
                  read (memory :> bytes(word_add seed (word 128),34)) s =
                  num_of_bytelist inp2 /\
                  read (memory :> bytes(word_add seed (word 192),34)) s =
                  num_of_bytelist inp3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(vec0,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp0) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec1,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp1) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec2,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp2) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec3,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp3) (504 + 168 * k)))))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(vec0,512); memory :> bytes(vec1,512);
                memory :> bytes(vec2,512); memory :> bytes(vec3,512);
                memory :> bytes(word_sub stackpointer (word 3416),3416)])`,
  REJX4_INTRO_TAC THEN REJX4_SETUP_TAC THEN REJX4_ABSORBED_TAC THEN
  REJX4_MINIMAL_TAC THEN

  (*** The first three blocks of each and the samples from them ***)

  ENSURES_SEQUENCE_TAC `pc + 0x62c3` REJX4_A2 THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x61e9` REJX4_A1 THEN CONJ_TAC THENL
     [REJX4_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL [REJX4_NOLOOP_TAC; REJX4_LOOP_TAC]];
    REJX4_PART3_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, as for mlkem_poly_rej_uniform,     *)
(* with the least k for which all four have 256 samples. Since the           *)
(* instructions executed in the test depend on whether the first three have  *)
(* 256 samples, the template gives the events of the first test and of each  *)
(* iteration of the loop by two functions, for the two cases.                *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

(*** Constant-time and memory safety ***)

let PREJ4_ARGS =
  [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
   `seed:int64`; `inp0:byte list`; `inp1:byte list`;
   `inp2:byte list`; `inp3:byte list`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let PREJ4_DONE3 n = list_mk_conj(butlast(conjuncts(REJX4_DONE n)));;

let PREJ4_SAFE_TEMPLATE =
  let args = PREJ4_ARGS in
  let ty = itlist (fun a t -> mk_fun_ty (type_of a) t) args in
  let app n = list_mk_comb(mk_var(n,ty `:(uarch_event)list`),args)
  and appi n = mk_comb(list_mk_comb(mk_var(n,
                 ty (mk_fun_ty `:num` `:(uarch_event)list`)),args),`i:num`) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`,
                   mk_abs(`n:num`,REJX4_DONE `n:num`)) in
  let three0 = rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                           (PREJ4_DONE3 `0`))) in
  let loop = mk_abs(`i:num`,mk_cond(PREJ4_DONE3 `i + 1`,
                      appi "f_ev_loop2",appi "f_ev_loop1")) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,[k0;loop]) in
  let enter = mk_cond(three0,app "f_ev_enter2",app "f_ev_enter1") in
  let mid = mk_cond(mk_eq(k0,`0`),app "f_ev_skip",
              list_mk_comb(ap,[app "f_ev_exit";
                list_mk_comb(ap,[enum; enter])])) in
  let body = list_mk_comb(ap,[app "f_ev_p3";
               list_mk_comb(ap,[mid; app "f_ev_p1"])]) in
  list_mk_abs(args,body);;

let PREJ4_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_RELEASE" THEN
  CONCRETIZE_F_EVENTS_TAC PREJ4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REJX4_INTRO_TAC THEN REJX4_SETUP_TAC THEN REJX4_ABSORBED_TAC THEN
  REJX4_MINIMAL_TAC;;

let PREJ4_ALLOWED =
  let ty = itlist (fun a t -> mk_fun_ty (type_of a) t) PREJ4_ARGS
                  (mk_fun_ty `:num` `:(uarch_event)list`) in
  PREJ4_ARGS @
  [`i:num`; `ci0:num`; `ci1:num`; `ci2:num`; `ci3:num`;
   `e2:(uarch_event)list`;
   mk_var("f_ev_loop1",ty); mk_var("f_ev_loop2",ty)];;

let PREJ4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref PREJ4_ALLOWED); LABEL_TAC name safety_th]);;

let PREJ4_SAFE_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

(*** with both put in the same form by APPEND_SPINE_CONV               ***)

let rec APPEND_SPINE_CONV tm =
  if is_binary "APPEND" tm then
    if is_binary "APPEND" (lhand tm) then
      (REWR_CONV(GSYM APPEND_ASSOC) THENC APPEND_SPINE_CONV) tm
    else RAND_CONV APPEND_SPINE_CONV tm
  else REFL tm;;

let PREJ4_SAFE_INIT_OPAQUE_TAC =
  PREJ4_SAFE_INIT_TAC THEN
  FIRST_X_ASSUM(fun dth ->
    let l,r = dest_eq(concl dth) in
    if is_var l && name_of l = "e2" && is_binary "APPEND" r then
      let dth' = CONV_RULE(RAND_CONV APPEND_SPINE_CONV) dth in
      let is_trace t =
        is_binary "APPEND" t &&
        can (find_term (fun u -> is_const u && name_of u = "ENUMERATEL")) t in
      ASSUME_TAC(SYM dth') THEN
      PURE_REWRITE_TAC[ENUMERATEL_ADD1] THEN
      CONV_TAC(ONCE_DEPTH_CONV(fun t ->
        if is_trace t then APPEND_SPINE_CONV t else failwith "")) THEN
      PURE_REWRITE_TAC[SYM dth']
    else NO_TAC);;

(*** assumptions they need                                              ***)

let PREJ4_KEEP_TAC : tactic = fun (asl,w) ->
  let hd_const c = try fst(dest_const(fst(strip_comb c))) with _ -> "" in
  let keep (_,th) =
    let c = concl th in
    hd_const c = "memaccess_inbounds" ||
    hd_const c = "nonoverlapping_modulo" ||
    (is_eq c && is_var(lhs c) &&
     let n = name_of(lhs c) in
     String.length n >= 2 && String.sub n 0 2 = "e2") ||
    ((is_binary "<" c || is_binary "<=" c) &&
     not(can (find_term (fun t -> is_const t && name_of t = "read")) c)) in
  (null_meta,[filter keep asl,w],fun i ths -> hd ths);;

let rec PREJ4_SPLIT_TAC g =
  W(fun (asl,w) ->
    if is_binary "APPEND" (rand(rator(rator w))) then
      GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THEN
      PREJ4_SPLIT_TAC
    else ALL_TAC) g;;

let PREJ4_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [FULL_UNIFY_F_EVENTS_TAC ORELSE
    (REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; APPEND_NIL] THEN NO_TAC);
    ALL_TAC] THEN
  PREJ4_KEEP_TAC THEN REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  PREJ4_SPLIT_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let PREJ4_CALL0_TAC m n =
  let inp = el m REJX4_INPS in
  REJX4_INPUT0_TAC m (mk_var("s"^string_of_int(n-1),`:x86state`)) THEN
  PREJ4_SAFE_CALL_TAC "H_REJ"
   [`e:(uarch_event)list`; `read RDI s`; `0`; `read RDX s`; `504`;
    rejx4_fields0 inp; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] n THEN
  REJX4_NORM_TAC THEN REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl));;

let PREJ4_SAFE_PART1_TAC =
  PREJ4_SAFE_INIT_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJX4_FRAME_ADDRESS]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (13--21) THEN
  REJX4_NORM_TAC THEN
  PREJ4_SAFE_CALL_TAC "H_INIT"
   [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 22 THEN
  REJX4_NORM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (23--30) THEN
  REJX4_NORM_TAC THEN
  PREJ4_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RCX s`; `read R8 s`; `34`;
    `num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
    `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 31 THEN
  REJX4_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (32--44) THEN
  REJX4_NORM_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  PREJ4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RCX s`; `3`; `read R9 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 45 THEN
  REJX4_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  MAP_EVERY (fun (m,(a,b)) ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (a--b) THEN
    REJX4_NORM_TAC THEN PREJ4_CALL0_TAC m (b + 1))
   [0,(46,50); 1,(52,57); 2,(59,64); 3,(66,71)] THEN
  MAP_EVERY REJX4_ARGS_32_TAC (butlast rejx4_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PREJ4_SAFE_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  PREJ4_SAFE_INIT_TAC THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--11) THEN
  MAP_EVERY REJX4_HI_TAC (butlast rejx4_cs0) THEN
  REJX4_JNE_TAC (butlast rejx4_cs0) THEN
  REJX4_ARGS_32_TAC (last rejx4_cs0) THEN REJX4_RIP_SIMP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (12--13) THEN
  REJX4_JBE_TAC (last rejx4_cs0) THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) rejx4_cs0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `0`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PREJ4_SAFE_LOOP_INIT_TAC =
  PREJ4_SAFE_INIT_TAC THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--11) THEN
  MAP_EVERY REJX4_HI_TAC (butlast rejx4_cs0) THEN
  REJX4_JNE_TAC (butlast rejx4_cs0) THEN
  REJX4_ARGS_32_TAC (last rejx4_cs0) THEN
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (REJX4_DONE `0`)))))
  ASSUME_TAC THENL
   [REJX4_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REJX4_RIP_CASES_TAC THENL
   [REJX4_FOURTH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (12--13) THEN
    REJX4_JBE_TAC (last rejx4_cs0);
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PREJ4_CALL_TAC m n =
  let inp = el m REJX4_INPS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  REJX4_ARGS_32_TAC c THEN
  REJX4_BLOCK_TAC m (mk_var("s"^string_of_int(n-1),`:x86state`)) THEN
  PREJ4_SAFE_CALL_TAC "H_REJ"
   [`e:(uarch_event)list`; `read RDI s`; c; `read RDX s`; `168`;
    rejx4_block inp `i:num`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] n THEN
  REJX4_NORM_TAC THEN REJX4_COMBINE_TAC m n;;

let PREJ4_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && REJX4_IS_ABBREV(lhand(concl th))
    then MAP_EVERY (SUBST_ALL_TAC o SYM) (CONJUNCTS th) else NO_TAC);;

let PREJ4_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REJX4_ABBREV_TAC THEN PREJ4_SAFE_INIT_OPAQUE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--8) THEN
  REJX4_NORM_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  PREJ4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RCX s`; `1`; `read R9 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `keccak_squeeze (3 + i) (S1:1600 word)`;
    `keccak_squeeze (3 + i) (S2:1600 word)`;
    `keccak_squeeze (3 + i) (S3:1600 word)`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 9 THEN
  REJX4_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  MAP_EVERY (fun (m,(a,b)) ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (a--b) THEN
    REJX4_NORM_TAC THEN PREJ4_CALL_TAC m (b + 1))
   [0,(10,14); 1,(16,21); 2,(23,28); 3,(30,35)] THEN
  MAP_EVERY REJX4_ARGS_32_TAC (butlast rejx4_cs1) THEN
  ABBREV_TAC `rdx0 = read RDX s36` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (37--46) THEN
  MAP_EVERY REJX4_HI_TAC (butlast rejx4_cs1) THEN
  REJX4_JNE_TAC (butlast rejx4_cs1) THEN
  REJX4_ARGS_32_TAC (last rejx4_cs1) THEN
  ASM_CASES_TAC `i + 1 < k0` THENL
   [SUBGOAL_THEN (mk_neg(REJX4_DONE `i + 1`)) ASSUME_TAC THENL
     [REJX4_MINIMALITY_TAC `i + 1` THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REJX4_RIP_CASES_TAC THENL
     [REJX4_FOURTH_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC
       (47--48) THEN
      REJX4_JBE_TAC (last rejx4_cs1);
      ALL_TAC];
    SUBGOAL_THEN (REJX4_DONE `i + 1`) STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REJX4_RIP_SIMP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (47--48) THEN
    REJX4_JBE_TAC (last rejx4_cs1)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PREJ4_UNABBREV_TAC THEN PREJ4_DISCHARGE_TAC;;

let PREJ4_SAFE_EXIT_TAC =
  REWRITE_TAC[] THEN PREJ4_SAFE_INIT_OPAQUE_TAC THEN
  MAP_EVERY (fun inp ->
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `k0:num`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   REJX4_INPS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PREJ4_DISCHARGE_TAC;;

let PREJ4_SAFE_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + 0x6208` `pc + 0x62c3`
    REJX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; PREJ4_SAFE_LOOP_INIT_TAC; PREJ4_SAFE_BODY_TAC;
    PREJ4_SAFE_EXIT_TAC];;

let PREJ4_SAFE_PART3_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  PREJ4_SAFE_INIT_OPAQUE_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (1--2) THEN
  REJX4_NORM_TAC THEN
  PREJ4_SAFE_CALL_TAC "H_RELEASE"
   [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 3 THEN
  REJX4_NORM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_EXEC (4--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PREJ4_DISCHARGE_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e vec0 vec1 vec2 vec3 seed (inp0:byte list) (inp1:byte list)
          (inp2:byte list) (inp3:byte list) k pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        LENGTH inp0 = 34 /\ LENGTH inp1 = 34 /\
        LENGTH inp2 = 34 /\ LENGTH inp3 = 34 /\
        ALL (\inp. 256 <= LENGTH(FILTER (\x. val x < 3329)
                            (MAP (word_zx:12 word->16 word)
                              (wordlist_of_num (336 + 112 * k)
                                (num_of_bytelist
                                  (list_of_seq (shake128 inp)
                                               (504 + 168 * k)))))))
            [inp0; inp1; inp2; inp3] /\
        PAIRWISE nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3416),3424)] /\
        ALLPAIRS nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3416),3424)]
         [(seed,34); (word_add seed (word 64),34);
          (word_add seed (word 128),34); (word_add seed (word 192),34);
          (word pc,0x82a0)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x60e0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = num_of_bytelist inp0 /\
                  read (memory :> bytes(word_add seed (word 64),34)) s =
                  num_of_bytelist inp1 /\
                  read (memory :> bytes(word_add seed (word 128),34)) s =
                  num_of_bytelist inp2 /\
                  read (memory :> bytes(word_add seed (word 192),34)) s =
                  num_of_bytelist inp3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events vec0 vec1 vec2 vec3 seed inp0 inp1 inp2
                            inp3 pc (word_sub stackpointer (word 3416))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,34; word_add seed (word 64),34;
                       word_add seed (word 128),34;
                       word_add seed (word 192),34;
                       vec0,512; vec1,512; vec2,512; vec3,512;
                       word_sub stackpointer (word 3416),3424;
                       word(pc + 0x80c0),192]
                      [vec0,512; vec1,512; vec2,512; vec3,512;
                       word_sub stackpointer (word 3416),3416]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(vec0,512); memory :> bytes(vec1,512);
                memory :> bytes(vec2,512); memory :> bytes(vec3,512);
                memory :> bytes(word_sub stackpointer (word 3416),3416)])`,
  PREJ4_SAFE_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x62c3` REJX4_A2 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x61e9` REJX4_A1 THEN CONJ_TAC THENL
     [PREJ4_SAFE_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL
       [PREJ4_SAFE_NOLOOP_TAC; PREJ4_SAFE_LOOP_TAC]];
    PREJ4_SAFE_PART3_TAC]);;
