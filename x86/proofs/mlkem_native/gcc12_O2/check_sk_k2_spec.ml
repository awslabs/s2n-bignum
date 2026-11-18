(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hash check of an ML-KEM-512 decapsulation key. This is the code for   *)
(* mlkem512_check_sk from mlkem-native's portable C implementation compiled  *)
(* by gcc 12 with -O2 (see mlkem_native/README.md), which computes the       *)
(* SHA3-256 hash of the encapsulation key in the decapsulation key into a    *)
(* buffer on the stack, compares it in constant time with the hash stored in *)
(* the decapsulation key, and zeroes the buffer. It is verified in the whole *)
(* image (see libmlkem.ml), using the theorems for mlkem_sha3_256 in the     *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/sha3_256_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem512_check_sk:
       +0x0: push   rbp
       +0x1: lea    rsi,[rdi+0x300]
       +0x8: mov    edx,0x320
       +0xd: mov    rbp,rsp
      +0x10: push   r12
      +0x12: push   rbx
      +0x13: mov    rbx,rdi
      +0x16: and    rsp,0xffffffffffffffe0
      +0x1a: sub    rsp,0x20
      +0x1e: mov    r12,rsp
      +0x21: mov    rdi,r12
      +0x24: call   <mlkem_sha3_256>
      +0x29: movdqu xmm1,XMMWORD PTR [rbx+0x620]
      +0x31: movdqu xmm2,XMMWORD PTR [rbx+0x630]
      +0x39: pxor   xmm1,XMMWORD PTR [rsp]
      +0x3e: pxor   xmm2,XMMWORD PTR [rsp+0x10]
      +0x44: movdqa xmm0,xmm1
      +0x48: pxor   xmm1,xmm2
      +0x4c: por    xmm0,xmm2
      +0x50: movdqa xmm2,xmm1
      +0x54: psrldq xmm2,0x8
      +0x59: pxor   xmm1,xmm2
      +0x5d: movdqa xmm2,xmm1
      +0x61: psrldq xmm2,0x4
      +0x66: pxor   xmm1,xmm2
      +0x6a: movdqa xmm2,xmm1
      +0x6e: psrldq xmm2,0x2
      +0x73: pxor   xmm1,xmm2
      +0x77: movdqa xmm2,xmm1
      +0x7b: psrldq xmm2,0x1
      +0x80: pxor   xmm1,xmm2
      +0x84: movd   edx,xmm1
      +0x88: movdqa xmm1,xmm0
      +0x8c: psrldq xmm1,0x8
      +0x91: por    xmm0,xmm1
      +0x95: movdqa xmm1,xmm0
      +0x99: psrldq xmm1,0x4
      +0x9e: por    xmm0,xmm1
      +0xa2: movdqa xmm1,xmm0
      +0xa6: psrldq xmm1,0x2
      +0xab: por    xmm0,xmm1
      +0xaf: movdqa xmm1,xmm0
      +0xb3: psrldq xmm1,0x1
      +0xb8: por    xmm0,xmm1
      +0xbc: movd   eax,xmm0
      +0xc0: movzx  eax,al
      +0xc3: neg    eax
      +0xc5: sar    eax,0x10
      +0xc8: xor    eax,edx
      +0xca: cmp    al,dl
      +0xcc: pxor   xmm0,xmm0
      +0xd0: sete   al
      +0xd3: movaps XMMWORD PTR [rsp],xmm0
      +0xd7: movzx  eax,al
      +0xda: movaps XMMWORD PTR [rsp+0x10],xmm0
      +0xdf: lea    eax,[rax+rax*4-0x5]
      +0xe3: lea    rsp,[rbp-0x10]
      +0xe7: pop    rbx
      +0xe8: pop    r12
      +0xea: pop    rbp
      +0xeb: ret
 ***)

let MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem512_check_sk"];;

(* ------------------------------------------------------------------------- *)
(* The buffer for the hash is aligned to 32 bytes within the stack frame, by *)
(* AND with -32 after the pushes of RBP, R12 and RBX. As for                 *)
(* mlkem512_poly_getnoise_eta2, the proof uses a variable bot for the        *)
(* address 600 bytes below the aligned stack pointer, the bottom of the      *)
(* stack of mlkem_sha3_256, which is stackpointer + delta for delta = 32 -   *)
(* val(stackpointer + 632) MOD 32, where stackpointer is the bottom of the   *)
(* 656 bytes of the stack below the return address, with the facts about the *)
(* frame proved by BITBLAST through the form of delta as a word,             *)
(* CHECK_SK_DELTA. The buffer is then at bot + 568, which is 8 bytes off a   *)
(* multiple of 16, so the addresses of its two halves, zeroed at the end by  *)
(* MOVAPS, are given as aligned explicitly.                                  *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_ALIGNED_16_STMT =
  `!x:int64. aligned 16 x <=> word_and x (word 15) = word 0`;;

let CHECK_SK_ALIGNED_16 =
  assume_spec CHECK_SK_ALIGNED_16_STMT;;

let CHECK_SK_DELTA_STMT =
  `!x:int64. 32 - val x MOD 32 =
             val(word_sub (word 32) (word_and x (word 31)):int64)`;;

let CHECK_SK_DELTA =
  assume_spec CHECK_SK_DELTA_STMT;;

let CHECK_SK_BOT_TAC =
  ABBREV_TAC
   `delta = 32 - val(word_add (stackpointer:int64) (word 632)) MOD 32` THEN
  SUBGOAL_THEN `delta <= 32` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bot = word_add (stackpointer:int64) (word delta)` THEN
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 632))
             (word 18446744073709551584):int64 =
    word_add bot (word 600) /\
    aligned 16 (word_add bot (word 568):int64) /\
    aligned 16 (word_add bot (word 584):int64)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CHECK_SK_ALIGNED_16] THEN
    MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN
    REWRITE_TAC[CHECK_SK_DELTA] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC];;

let CHECK_SK_NONOV_TAC sksize =
  FIRST_ASSUM(fun bth ->
    if is_eq(concl bth) && rhs(concl bth) = `bot:int64`
    then
      MAP_EVERY (fun r ->
        SUBGOAL_THEN
         (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                          `bot:int64,600`),r)) ASSUME_TAC THENL
         [REWRITE_TAC[SYM bth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       [mk_pair(`sk:int64`,mk_small_numeral sksize); `word pc:int64,libmlkem_size`;
        `word_add stackpointer (word 632):int64,32`]
    else NO_TAC);;

let CHECK_SK_FRAME_TAC =
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
     [memory :> bytes(bot:int64,600);
      memory :> bytes(word_add stackpointer (word 632),24)]` THEN
  CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC];;

let CHECK_SK_SETUP_TAC sksize =
  CHECK_SK_BOT_TAC THEN CHECK_SK_FRAME_TAC THEN CHECK_SK_NONOV_TAC sksize THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12`;;

let CHECK_SK_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let CHECK_SK_RSP_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 632))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The comparison of the two hashes, as two 128-bit words each: the bytes of *)
(* their XOR are ORed together (and XORed together, which does not affect    *)
(* the result) by a sequence of shifts and ORs in the low halves of YMM      *)
(* registers, whose upper halves are given names after the call, and the     *)
(* result of the function is from that. CHECK_SK_COMPARE_TAC reduces it to a *)
(* statement about the XOR of the hashes proved by BITBLAST.                 *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_BYTES128_HALVES_STMT =
  `!a:int64 n s:x86state.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`;;

let CHECK_SK_BYTES128_HALVES =
  assume_spec CHECK_SK_BYTES128_HALVES_STMT;;

let CHECK_SK_EQ_STMT =
  `!h n. h < 2 EXP 256 /\ n < 2 EXP 256
         ==> (h = n <=>
              word(n MOD 2 EXP 128):int128 = word(h MOD 2 EXP 128) /\
              word(n DIV 2 EXP 128):int128 = word(h DIV 2 EXP 128))`;;

let CHECK_SK_EQ =
  assume_spec CHECK_SK_EQ_STMT;;

let READ_MEMORY_BYTES_32_BOUND_STMT =
  `!a n s:x86state.
        read (memory :> bytes(a,32)) s = n ==> n < 2 EXP 256`;;

let READ_MEMORY_BYTES_32_BOUND =
  assume_spec READ_MEMORY_BYTES_32_BOUND_STMT;;

let CHECK_SK_HALVES_TAC a v l h =
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; v,`v:num`]
             `read (memory :> bytes(a,32)) s = v`)) (concl th)
    then ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES_32_BOUND th) THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                  (MATCH_MP CHECK_SK_BYTES128_HALVES th)) THEN
         ABBREV_TAC(mk_eq(mk_var(l,`:int128`),
                    mk_comb(`word:num->int128`,
                     mk_binop `MOD` v `2 EXP 128`))) THEN
         ABBREV_TAC(mk_eq(mk_var(h,`:int128`),
                    mk_comb(`word:num->int128`,
                     mk_binop `DIV` v `2 EXP 128`))) THEN
         STRIP_TAC
    else NO_TAC);;

let CHECK_SK_YMM_TAC st =
  MAP_EVERY (fun (v,r) ->
    ABBREV_TAC(mk_eq(mk_var(v,`:int256`),
      list_mk_comb(`read:(x86state,int256)component->x86state->int256`,
                   [r; st]))))
   [("y0",`YMM0`); ("y1",`YMM1`); ("y2",`YMM2`)];;

let CHECK_SK_BYTE_MOD = prove
 (`!x:N word. word(val x MOD 256):M word = word_zx(word_zx x:byte)`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  MP_TAC(SPEC `val(x:N word)` (ARITH_RULE `!n. n MOD 256 < 256`)) THEN
  SIMP_TAC[MOD_LT]);;

let CHECK_SK_SUBWORD_JOIN_STMT =
  `!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`;;

let CHECK_SK_SUBWORD_JOIN =
  assume_spec CHECK_SK_SUBWORD_JOIN_STMT;;

let CHECK_SK_EXPAND_TAC v =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Const("word",_),_)),r) when r = v ->
        SUBST1_TAC(SYM th)
    | _ -> NO_TAC);;

let CHECK_SK_COMPARE_TAC =
  SUBGOAL_THEN
   `h = num_of_bytelist(sha3_256 ek) <=>
    (nl:int128) = hl /\ (nh:int128) = hh`
  SUBST1_TAC THENL
   [MAP_EVERY CHECK_SK_EXPAND_TAC
     [`nl:int128`; `nh:int128`; `hl:int128`; `hh:int128`] THEN
    MATCH_MP_TAC CHECK_SK_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((nl:int128) = hl /\ (nh:int128) = hh) <=>
    (word_xor hl nl = word 0 /\ word_xor hh nh = word 0)`
  SUBST1_TAC THENL [REWRITE_TAC[WORD_XOR_EQ_0] THEN MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`word_xor hh nh:int128`,`y:int128`) THEN
  SPEC_TAC(`word_xor hl nl:int128`,`x:int128`) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CHECK_SK_BYTE_MOD; GSYM word_zx; VAL_EQ_0;
              CHECK_SK_SUBWORD_JOIN] THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The decapsulation key of 1632 bytes at sk contains the *)
(* encapsulation key of 800 bytes at offset 768, given as a list of bytes    *)
(* ek, and its hash h at offset 1568, as a number. The result is 0 if h is   *)
(* the SHA3-256 hash of ek, as in common/fips202/fips202.ml, and -5          *)
(* otherwise. The stack is the 656 bytes below the return address, for the   *)
(* three saved registers, up to 31 bytes for the alignment, the 32 bytes of  *)
(* the buffer and the 568 used by mlkem_sha3_256 below it.                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_256_TAC exec =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,exec,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let CHECK_SK_INTRO_TAC =
  MAP_EVERY X_GEN_TAC [`sk:int64`; `ek:byte list`; `h:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 656 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!sk (ek:byte list) h pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH ek = 800 /\
        nonoverlapping (sk,1632) (word_sub stackpointer (word 656),664) /\
        nonoverlapping (word_sub stackpointer (word 656),664) (word pc,libmlkem_size)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem512_check_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(word_add sk (word 768),800)) s =
                  num_of_bytelist ek /\
                  read (memory :> bytes(word_add sk (word 1568),32)) s = h)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if h = num_of_bytelist(sha3_256 ek) then word 0
                   else word 0xfffffffb))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 656),656)])`;;

let MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, and the combined theorem with      *)
(* correctness, using the combined one for mlkem_sha3_256, for the           *)
(* decapsulation, which branches on the result. The events do not depend on  *)
(* the keys. CHECK_SK_SAFE_TAC does both proofs, as the correctness proof    *)
(* apart from the comparison for the safety one, and at the end the frame    *)
(* variables are expanded in the events by CHECK_SK_UNBOT_TAC, since they    *)
(* are not arguments of f_events.                                            *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let CHECK_SK_SAFE_ALLOWED =
  [`pc:num`; `sk:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `bot:int64`];;

let CHECK_SK_SAFE_CALL_TAC exec name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,exec,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECK_SK_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let CHECK_SK_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `delta:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

let CHECK_SK_SAFE_TAC full =
  let exec = MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_EXEC
  and sksize = 1632 and eklen = 800 and hoff = 1568 in
  let callee = if full
    then MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_FULL
    else MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE in
  let ilist = if full
    then [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `ek:byte list`;
          mk_small_numeral eklen; `pc:num`; `read RSP s`;
          `read (memory :> bytes64(read RSP s)) s`]
    else [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
          mk_small_numeral eklen; `pc:num`; `read RSP s`;
          `read (memory :> bytes64(read RSP s)) s`] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC callee "H_SHA3" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   ([`e:(uarch_event)list`; `sk:int64`] @
    (if full then [`ek:byte list`; `h:num`] else []) @ [`pc:num`]) THEN
  WORD_FORALL_OFFSET_TAC 656 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CHECK_SK_SETUP_TAC sksize THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  (if full then
     CHECK_SK_HALVES_TAC
      (mk_comb(`word_add (sk:int64)`,
               mk_comb(`word:num->int64`,mk_small_numeral hoff)))
      `h:num` "hl" "hh"
   else ALL_TAC) THEN
  X86_STEPS_TAC exec (1--8) THEN CHECK_SK_RSP_TAC THEN
  X86_STEPS_TAC exec (9--12) THEN CHECK_SK_NORM_TAC THEN
  CHECK_SK_SAFE_CALL_TAC exec "H_SHA3" ilist 13 THEN
  CHECK_SK_NORM_TAC THEN
  (if full then
     CHECK_SK_HALVES_TAC `word_add (bot:int64) (word 568)`
      `num_of_bytelist(sha3_256 ek)` "nl" "nh" THEN
     CHECK_SK_YMM_TAC `s13:x86state`
   else ALL_TAC) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC exec [k] THEN SIMD_SIMPLIFY_TAC[])
   (14--62) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (if full then CONJ_TAC THENL [CHECK_SK_COMPARE_TAC; ALL_TAC]
   else ALL_TAC) THEN
  CHECK_SK_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e sk pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       nonoverlapping (sk,1632) (word_sub stackpointer (word 656),664) /\
       nonoverlapping (word_sub stackpointer (word 656),664) (word pc,libmlkem_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem512_check_sk) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk pc (word_sub stackpointer (word 656))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [word_add sk (word 768),800; word_add sk (word 1568),32;
                      word_sub stackpointer (word 656),664;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [word_sub stackpointer (word 656),656]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 656),656)])`;;

let MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e sk (ek:byte list) h pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ LENGTH ek = 800 /\
       nonoverlapping (sk,1632) (word_sub stackpointer (word 656),664) /\
       nonoverlapping (word_sub stackpointer (word 656),664) (word pc,libmlkem_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem512_check_sk) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 (read DF s <=> false) /\
                 read (memory :> bytes(word_add sk (word 768),800)) s =
                 num_of_bytelist ek /\
                 read (memory :> bytes(word_add sk (word 1568),32)) s = h /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 C_RETURN s =
                 (if h = num_of_bytelist(sha3_256 ek) then word 0
                  else word 0xfffffffb) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk pc (word_sub stackpointer (word 656))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [word_add sk (word 768),800; word_add sk (word 1568),32;
                      word_sub stackpointer (word 656),664;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [word_sub stackpointer (word 656),656]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 656),656)])`;;

let MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
