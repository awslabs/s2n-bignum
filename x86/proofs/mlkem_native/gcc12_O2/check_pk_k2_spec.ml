(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The modulus check of an ML-KEM-512 encapsulation key. This is the code    *)
(* for mlkem512_check_pk from mlkem-native's portable C implementation       *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which decodes   *)
(* the vector of the key from its first 768 bytes into a buffer on the       *)
(* stack, reduces it, encodes it again into another buffer, compares the     *)
(* result in constant time with the key, and zeroes the buffers. It is       *)
(* verified in the whole image (see libmlkem.ml), using the theorems for     *)
(* mlkem512_polyvec_frombytes, mlkem512_polyvec_reduce and                   *)
(* mlkem512_polyvec_tobytes in the image.                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_frombytes_k2_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_reduce_k2_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_tobytes_k2_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;
needs "x86/proofs/consttime.ml";;

(*** The code in the image:

    mlkem512_check_pk:
       +0x0: push   rbp
       +0x1: mov    rsi,rdi
       +0x4: mov    rbp,rsp
       +0x7: push   r13
       +0x9: mov    r13,rdi
       +0xc: push   r12
       +0xe: push   rbx
       +0xf: and    rsp,0xffffffffffffffe0
      +0x13: sub    rsp,0x700
      +0x1a: lea    rbx,[rsp+0x300]
      +0x22: mov    r12,rsp
      +0x25: mov    rdi,rbx
      +0x28: call   <mlkem512_polyvec_frombytes>
      +0x2d: mov    rdi,rbx
      +0x30: call   <mlkem512_polyvec_reduce>
      +0x35: mov    rsi,rbx
      +0x38: mov    rdi,r12
      +0x3b: call   <mlkem512_polyvec_tobytes>
      +0x40: pxor   xmm2,xmm2
      +0x44: xor    eax,eax
      +0x46: movdqa xmm0,xmm2
      +0x4a: nop    WORD PTR [rax+rax*1+0x0]
      +0x50: movdqu xmm1,XMMWORD PTR [r13+rax*1+0x0]
      +0x57: pxor   xmm1,XMMWORD PTR [r12+rax*1]
      +0x5d: add    rax,0x10
      +0x61: por    xmm0,xmm1
      +0x65: pxor   xmm2,xmm1
      +0x69: cmp    rax,0x300
      +0x6f: jne    <mlkem512_check_pk+0x50>
      +0x71: movdqa xmm1,xmm2
      +0x75: psrldq xmm1,0x8
      +0x7a: pxor   xmm2,xmm1
      +0x7e: movdqa xmm1,xmm2
      +0x82: psrldq xmm1,0x4
      +0x87: pxor   xmm2,xmm1
      +0x8b: movdqa xmm1,xmm2
      +0x8f: psrldq xmm1,0x2
      +0x94: pxor   xmm2,xmm1
      +0x98: movdqa xmm1,xmm2
      +0x9c: psrldq xmm1,0x1
      +0xa1: pxor   xmm2,xmm1
      +0xa5: movdqa xmm1,xmm0
      +0xa9: psrldq xmm1,0x8
      +0xae: movd   edx,xmm2
      +0xb2: por    xmm0,xmm1
      +0xb6: movdqa xmm1,xmm0
      +0xba: psrldq xmm1,0x4
      +0xbf: por    xmm0,xmm1
      +0xc3: movdqa xmm1,xmm0
      +0xc7: psrldq xmm1,0x2
      +0xcc: por    xmm0,xmm1
      +0xd0: movdqa xmm1,xmm0
      +0xd4: psrldq xmm1,0x1
      +0xd9: por    xmm0,xmm1
      +0xdd: movd   eax,xmm0
      +0xe1: movzx  eax,al
      +0xe4: neg    eax
      +0xe6: sar    eax,0x10
      +0xe9: xor    eax,edx
      +0xeb: cmp    al,dl
      +0xed: mov    rdi,r12
      +0xf0: mov    ecx,0x60
      +0xf5: sete   dl
      +0xf8: xor    eax,eax
      +0xfa: rep    stos QWORD PTR es:[rdi],rax
      +0xfd: movzx  edx,dl
     +0x100: lea    edx,[rdx*4-0x4]
     +0x107: mov    ecx,0x80
     +0x10c: mov    rdi,rbx
     +0x10f: rep    stos QWORD PTR es:[rdi],rax
     +0x112: lea    rsp,[rbp-0x18]
     +0x116: mov    eax,edx
     +0x118: pop    rbx
     +0x119: pop    r12
     +0x11b: pop    r13
     +0x11d: pop    rbp
     +0x11e: ret
 ***)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem512_check_pk"];;

(* ------------------------------------------------------------------------- *)
(* The reduced vector, as a list of 16-bit coefficients for the encoding,    *)
(* and the equivalence of its encoding with the key with the 12-bit fields   *)
(* of the key being below 3329.                                              *)
(* ------------------------------------------------------------------------- *)

let CHECK_PK_BYTES16_LIST_STMT =
  `!a n (f:num->int16) s:x86state.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`;;

let CHECK_PK_BYTES16_LIST =
  assume_spec CHECK_PK_BYTES16_LIST_STMT;;

let CHECK_PK_IVAL_WORD_STMT =
  `!f. f < 32768 ==> ival(word f:int16) = &f`;;

let CHECK_PK_IVAL_WORD =
  assume_spec CHECK_PK_IVAL_WORD_STMT;;

let CHECK_PK_REDUCED_STMT =
  `!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`;;

let CHECK_PK_REDUCED =
  assume_spec CHECK_PK_REDUCED_STMT;;

let CHECK_PK_LIST_PROPS_STMT =
  `!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`;;

let CHECK_PK_LIST_PROPS =
  assume_spec CHECK_PK_LIST_PROPS_STMT;;

let CHECK_PK_REENCODE_STMT =
  `!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`;;

let CHECK_PK_REENCODE =
  assume_spec CHECK_PK_REENCODE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The comparison, 16 bytes at a time in the low halves of YMM registers:    *)
(* the bytes of the key and of the encoding XORed together are ORed into one *)
(* accumulator (and XORed into another, which does not affect the result),   *)
(* which is zero if and only if the prefixes so far are equal. The result is *)
(* computed from the bytes of the accumulators ORed (and XORed) together, as *)
(* for mlkem512_check_sk.                                                    *)
(* ------------------------------------------------------------------------- *)

let CHECK_PK_BYTES128_STMT =
  `!a l k n s:x86state.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`;;

let CHECK_PK_BYTES128 =
  assume_spec CHECK_PK_BYTES128_STMT;;

let CHECK_PK_MOD_STEP_STMT =
  `!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`;;

let CHECK_PK_MOD_STEP =
  assume_spec CHECK_PK_MOD_STEP_STMT;;

let CHECK_PK_OR_STEP_STMT =
  `!q:int128 a b.
        word_or q
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456))) =
        word 0 <=>
        q = word 0 /\ a MOD 2 EXP 128 = b MOD 2 EXP 128`;;

let CHECK_PK_OR_STEP =
  assume_spec CHECK_PK_OR_STEP_STMT;;

let CHECK_PK_BYTE_MOD = prove
 (`!x:N word. word(val x MOD 256):M word = word_zx(word_zx x:byte)`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  MP_TAC(SPEC `val(x:N word)` (ARITH_RULE `!n. n MOD 256 < 256`)) THEN
  SIMP_TAC[MOD_LT]);;

let CHECK_PK_SUBWORD_JOIN_STMT =
  `!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`;;

let CHECK_PK_SUBWORD_JOIN =
  assume_spec CHECK_PK_SUBWORD_JOIN_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, by AND with   *)
(* -32 after the pushes of RBP, R13, R12 and RBX, with RBP as a frame        *)
(* pointer. As for mlkem512_check_sk, the proof uses a variable bot for the  *)
(* address 40 bytes below the buffers, the bottom of the stacks of the       *)
(* callees, which is stackpointer + delta for delta = 32 -                   *)
(* val(stackpointer + 1864) MOD 32, where stackpointer is the bottom of the  *)
(* 1896 bytes of the stack below the return address, with the facts about    *)
(* the frame proved by BITBLAST through the form of delta as a word,         *)
(* CHECK_PK_DELTA. The encoding is then at bot + 40 and the vector at        *)
(* bot + 808. The comparison uses SSE instructions, which keep the upper     *)
(* halves of the YMM registers, so those are given names after the calls.    *)
(* ------------------------------------------------------------------------- *)

let CHECK_PK_DELTA_STMT =
  `!x:int64. 32 - val x MOD 32 =
             val(word_sub (word 32) (word_and x (word 31)):int64)`;;

let CHECK_PK_DELTA =
  assume_spec CHECK_PK_DELTA_STMT;;

let CHECK_PK_BOT_TAC =
  ABBREV_TAC
   `delta = 32 - val(word_add (stackpointer:int64) (word 1864)) MOD 32` THEN
  SUBGOAL_THEN `delta <= 32` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bot = word_add (stackpointer:int64) (word delta)` THEN
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 1864))
             (word 18446744073709551584):int64 =
    word_add bot (word 1832)`
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
                          `bot:int64,1832`),r)) ASSUME_TAC THENL
         [REWRITE_TAC[SYM bth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       [`pk:int64,768`; `word pc:int64,libmlkem_size`;
        `word_add stackpointer (word 1864):int64,40`]
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
     [memory :> bytes(bot:int64,1832);
      memory :> bytes(word_add stackpointer (word 1864),32)]` THEN
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
    if can (term_match [] `word_and (word_add stackpointer (word 1864))
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
              512`;;

let CHECK_PK_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                512))`;;

let CHECK_PK_FRAME =
 `read R13 s = pk /\
  read R12 s = word_add bot (word 40) /\
  read RBX s = word_add bot (word 808) /\
  read RBP s = word_add stackpointer (word 1888) /\
  read (memory :> bytes64 (word_add stackpointer (word 1864))) s =
  rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1872))) s =
  r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1880))) s =
  r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1888))) s =
  rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1896))) s =
  returnaddress /\
  ~read DF s`;;

let CHECK_PK_INV data =
  list_mk_abs([`i:num`; `s:x86state`],
   list_mk_conj([`read RAX s = word(16 * i)`; CHECK_PK_FRAME] @
    (if data then
      [vsubst [CHECK_PK_M,`M:num`]
        `read (memory :> bytes(pk,768)) s = n /\
         read (memory :> bytes(word_add bot (word 40),768)) s = M /\
         (word_subword (read YMM0 s) (0,128):int128 = word 0 <=>
          n MOD 2 EXP (128 * i) = M MOD 2 EXP (128 * i))`]
     else [])));;

(*** Decoding, reducing and encoding the vector, up to the loop ***)

let CHECK_PK_LIST_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:x86state`]
   `read (memory :> bytes(word_add bot (word 808),1024)) s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 512)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 2 * 512`] THEN
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
  call (MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT,
        "H_FROMBYTES")
   ([`read RDI s`; `read RSI s`],`n:num`) 14 THEN
  CHECK_PK_NORM_TAC THEN
  X86_STEPS_TAC exec (15--16) THEN
  call (MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT,
        "H_REDUCE")
   ([`read RDI s`],
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`) 17 THEN
  CHECK_PK_NORM_TAC THEN
  (if data then CHECK_PK_LIST_TAC `s17:x86state` else ALL_TAC) THEN
  X86_STEPS_TAC exec (18--20) THEN
  call (MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT,
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
  let bth = MP (ARITH_RULE `i < 48 ==> 16 * i + 16 <= 768`)
               (ASSUME `i < 48`)
  and pth = ARITH_RULE `16 * i = 1 * 16 * i` in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let lth = SPECL [a; `768`; `i:num`; v; s] CHECK_PK_BYTES128 in
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
   `~(val(word_add (word (16 * i)) (word 18446744073709550864):int64) = 0) <=>
    i + 1 < 48`
  SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_ADD_CASES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < 48` THEN ARITH_TAC;
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
   (ISPECL [a; `768`; mk_comb(`read memory:x86state->int64->byte`,s)]
           READ_BYTES_BOUND);;

let CHECK_PK_DONE_TAC =
  SUBGOAL_THEN
   `(word_subword (y0:int256) (0,128):int128 = word 0) <=>
    !i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) &&
         lhand(concl th) = `word_subword (y0:int256) (0,128):int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(CHECK_PK_BOUND `pk:int64` `s0:x86state`) THEN
    MP_TAC(CHECK_PK_BOUND `word_add bot (word 40):int64` `s0:x86state`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 768 = 128 * 48`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(CHECK_PK_M,`mm:num`))) THEN
    MATCH_MP_TAC CHECK_PK_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 512 = 128 * 48`];
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
  WORD_FORALL_OFFSET_TAC 1896 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let CHECK_PK_SAFE_INTRO_TAC exec full =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (if full then
      MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL
    else MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (if full then
      MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL
    else MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (if full then
      MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL
    else MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     APPEND (f_ev_epil pk pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 48 (\i. f_ev_loop pk pc stackpointer returnaddress i))
        (f_ev_prol pk pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   ([`pk:int64`] @ (if full then [`n:num`] else []) @ [`pc:num`]) THEN
  WORD_FORALL_OFFSET_TAC 1896 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let CHECK_PK_TAC (events,data) =
  let exec = MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_EXEC in
  (if events then CHECK_PK_SAFE_INTRO_TAC exec data
   else CHECK_PK_INTRO_TAC) THEN
  CHECK_PK_SETUP_TAC THEN
  (if events then ENSURES_EVENTS_WHILE_UP2_TAC else ENSURES_WHILE_UP2_TAC)
   `48` `pc + mlkem512_check_pk_loop1` `pc + mlkem512_check_pk_loop1_exit` (CHECK_PK_INV data) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CHECK_PK_PART1_TAC exec (events,data);
    CHECK_PK_BODY_TAC exec (events,data);
    CHECK_PK_EXIT_TAC exec (events,data)];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The first 768 bytes of the key at pk are a number n,   *)
(* and the result is 0 if all the 512 12-bit fields of n are below 3329,     *)
(* which is the modulus check of FIPS 203, and -4 otherwise. The stack is    *)
(* the 1896 bytes below the return address, for the four saved registers, up *)
(* to 31 bytes for the alignment, the 1792 bytes of the buffers and the 40   *)
(* used by the callees below them.                                           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    nonoverlapping (pk,768) (word_sub stackpointer (word 1896),1904) /\
    nonoverlapping (word_sub stackpointer (word 1896),1904) (word pc,libmlkem_size)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem512_check_pk) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,768)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s =
              (if !i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(word_sub stackpointer (word 1896),1896)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, and the combined theorem with      *)
(* correctness, for mlkem512_enc_derand, which branches on the result. The   *)
(* events depend only on the address of the key, the stack and the image:    *)
(* the comparison is in constant time and the result is computed without a   *)
(* branch.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
   forall e pk pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    nonoverlapping (pk,768) (word_sub stackpointer (word 1896),1904) /\
    nonoverlapping (word_sub stackpointer (word 1896),1904) (word pc,libmlkem_size)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem512_check_pk) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk] s /\
              (read DF s <=> false) /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk pc (word_sub stackpointer (word 1896))
                               returnaddress /\
                 memaccess_inbounds e2
                  [pk,768; word_sub stackpointer (word 1896),1904]
                  [word_sub stackpointer (word 1896),1896]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(word_sub stackpointer (word 1896),1896)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
   forall e pk n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    nonoverlapping (pk,768) (word_sub stackpointer (word 1896),1904) /\
    nonoverlapping (word_sub stackpointer (word 1896),1904) (word pc,libmlkem_size)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem512_check_pk) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,768)) s = n /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s =
              (if !i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk pc (word_sub stackpointer (word 1896))
                               returnaddress /\
                 memaccess_inbounds e2
                  [pk,768; word_sub stackpointer (word 1896),1904]
                  [word_sub stackpointer (word 1896),1896]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(word_sub stackpointer (word 1896),1896)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
