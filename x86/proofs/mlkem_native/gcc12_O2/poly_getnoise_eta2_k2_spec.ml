(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a noise polynomial with eta = 2 from a seed and a nonce. This *)
(* is the code for mlkem512_poly_getnoise_eta2 from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md), which computes 128 bytes of SHAKE256 of the seed *)
(* and the nonce into a buffer on the stack, applies mlkem_poly_cbd2 to them *)
(* and zeroes the buffers. It is verified in the whole image (see            *)
(* libmlkem.ml), using the theorems for mlkem_shake256 and mlkem_poly_cbd2   *)
(* in the image.                                                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_cbd2_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem512_poly_getnoise_eta2:
       +0x0: push   rbp
       +0x1: mov    ecx,0x21
       +0x6: mov    rbp,rsp
       +0x9: push   r13
       +0xb: push   r12
       +0xd: mov    r12,rdi
      +0x10: push   rbx
      +0x11: and    rsp,0xffffffffffffffe0
      +0x15: sub    rsp,0xc0
      +0x1c: movdqu xmm1,XMMWORD PTR [rsi]
      +0x20: movdqu xmm2,XMMWORD PTR [rsi+0x10]
      +0x25: mov    esi,0x80
      +0x2a: lea    rbx,[rsp+0x40]
      +0x2f: mov    r13,rsp
      +0x32: mov    BYTE PTR [rsp+0x20],dl
      +0x36: mov    rdi,rbx
      +0x39: mov    rdx,r13
      +0x3c: movaps XMMWORD PTR [rsp],xmm1
      +0x40: movaps XMMWORD PTR [rsp+0x10],xmm2
      +0x45: call   <mlkem_shake256>
      +0x4a: mov    rdi,r12
      +0x4d: mov    rsi,rbx
      +0x50: call   <mlkem_poly_cbd2>
      +0x55: xor    eax,eax
      +0x57: mov    rdi,rbx
      +0x5a: mov    ecx,0x10
      +0x5f: rep    stos QWORD PTR es:[rdi],rax
      +0x62: pxor   xmm0,xmm0
      +0x66: mov    BYTE PTR [rsp+0x20],0x0
      +0x6b: movaps XMMWORD PTR [rsp],xmm0
      +0x6f: movaps XMMWORD PTR [rsp+0x10],xmm0
      +0x74: lea    rsp,[rbp-0x18]
      +0x78: pop    rbx
      +0x79: pop    r12
      +0x7b: pop    r13
      +0x7d: pop    rbp
      +0x7e: ret
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem512_poly_getnoise_eta2"];;

(* ------------------------------------------------------------------------- *)
(* The seed is loaded as two 128-bit words, and stored with the nonce in a   *)
(* buffer of 64 bytes, as the 33 bytes of the input to SHAKE256. The stores  *)
(* are from the low halves of YMM registers, whose upper halves are kept as  *)
(* their initial values.                                                     *)
(* ------------------------------------------------------------------------- *)

let GETNOISE_BYTES128_HALVES_STMT =
  `!a:int64 n s:x86state.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`;;

let GETNOISE_BYTES128_HALVES =
  assume_spec GETNOISE_BYTES128_HALVES_STMT;;

let GETNOISE_BYTES_32_OF_HALVES_STMT =
  `!a:int64 n s:x86state.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`;;

let GETNOISE_BYTES_32_OF_HALVES =
  assume_spec GETNOISE_BYTES_32_OF_HALVES_STMT;;

let GETNOISE_INPUT_STMT =
  `!a:int64 (sd:byte list) b s:x86state.
        LENGTH sd = 32 /\
        read (memory :> bytes(a,32)) s = num_of_bytelist sd /\
        read (memory :> bytes8(word_add a (word 32))) s = b
        ==> LENGTH(APPEND sd [b]) = 33 /\
            read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND sd [b])`;;

let GETNOISE_INPUT =
  assume_spec GETNOISE_INPUT_STMT;;

let GETNOISE_SUBWORD_JOIN_STMT =
  `!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`;;

let GETNOISE_SUBWORD_JOIN =
  assume_spec GETNOISE_SUBWORD_JOIN_STMT;;

let GETNOISE_SSE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GETNOISE_SUBWORD_JOIN]);;

(* ------------------------------------------------------------------------- *)
(* The buffer for the input to SHAKE256, followed by the one of 128 bytes    *)
(* for its output, is aligned to 32 bytes within the stack frame, by AND     *)
(* with -32 after the pushes of RBP, R13, R12 and RBX. The proof uses a      *)
(* variable bot for the address 632 bytes below the buffers, the bottom of   *)
(* the stack of mlkem_shake256, which is stackpointer + delta for delta = 32 *)
(* - val(stackpointer + 856) MOD 32, where stackpointer is the bottom of the *)
(* 888 bytes of the stack below the return address. The facts about the      *)
(* frame are proved by BITBLAST through the form of delta as a word,         *)
(* GETNOISE_DELTA, and the addresses in the frame are bot plus a constant,   *)
(* as GETNOISE_NORM_TAC puts them. Since bot is 8 bytes off a multiple of    *)
(* 16, the addresses of the two halves of the seed in the buffer, which are  *)
(* stored by MOVAPS, are given as aligned explicitly.                        *)
(* ------------------------------------------------------------------------- *)

let GETNOISE_ALIGNED_16_STMT =
  `!x:int64. aligned 16 x <=> word_and x (word 15) = word 0`;;

let GETNOISE_ALIGNED_16 =
  assume_spec GETNOISE_ALIGNED_16_STMT;;

let GETNOISE_DELTA_STMT =
  `!x:int64. 32 - val x MOD 32 =
             val(word_sub (word 32) (word_and x (word 31)):int64)`;;

let GETNOISE_DELTA =
  assume_spec GETNOISE_DELTA_STMT;;

let GETNOISE_BOT_TAC =
  ABBREV_TAC
   `delta = 32 - val(word_add (stackpointer:int64) (word 856)) MOD 32` THEN
  SUBGOAL_THEN `delta <= 32` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bot = word_add (stackpointer:int64) (word delta)` THEN
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 856))
             (word 18446744073709551584):int64 =
    word_add bot (word 824) /\
    aligned 16 (word_add bot (word 632):int64) /\
    aligned 16 (word_add bot (word 648):int64)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GETNOISE_ALIGNED_16] THEN
    MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN
    REWRITE_TAC[GETNOISE_DELTA] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC];;

let GETNOISE_NONOV_TAC =
  FIRST_ASSUM(fun bth ->
    if is_eq(concl bth) && rhs(concl bth) = `bot:int64`
    then
      MAP_EVERY (fun r ->
        SUBGOAL_THEN
         (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                          `bot:int64,824`),r)) ASSUME_TAC THENL
         [REWRITE_TAC[SYM bth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       [`r:int64,512`; `seed:int64,32`; `word pc:int64,libmlkem_size`;
        `word_add stackpointer (word 856):int64,40`]
    else NO_TAC);;

let GETNOISE_FRAME_TAC =
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
     [memory :> bytes(r,512); memory :> bytes(bot:int64,824);
      memory :> bytes(word_add stackpointer (word 856),32)]` THEN
  CONJ_TAC THENL [EXPAND_TAC "bot" THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC];;

let GETNOISE_SETUP_TAC =
  GETNOISE_BOT_TAC THEN GETNOISE_FRAME_TAC THEN GETNOISE_NONOV_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13`;;

let GETNOISE_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let GETNOISE_ADDR_CONV =
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC NUM_REDUCE_CONV;;

let GETNOISE_RSP_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 856))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is 32 bytes at seed, given as a list of bytes *)
(* sd, and the nonce is the low byte of the third argument. As for PRF and   *)
(* SamplePolyCBD with eta = 2 in FIPS 203, the result is the centered        *)
(* binomial distribution of mlkem_poly_cbd2 applied to the first 128 bytes   *)
(* of shake256 of the seed followed by the nonce, as in                      *)
(* common/fips202/fips202.ml. The stack is the 888 bytes below the return    *)
(* address, for the four saved registers, up to 31 bytes for the alignment,  *)
(* the 192 bytes of the buffers and the 632 used by mlkem_shake256 below     *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD2_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, the input to SHAKE256 in the buffer ***)

let GETNOISE_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `seed:int64`; `sd:byte list`; `nonce:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 888 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let GETNOISE_INPUT_TAC =
  MP_TAC(SPECL [`word_add bot (word 632):int64`;
                `num_of_bytelist(sd:byte list)`; `s19:x86state`]
               GETNOISE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC GETNOISE_ADDR_CONV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `sd:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`word_add bot (word 632):int64`;
                `sd:byte list`; `word_zx(nonce:int64):byte`; `s19:x86state`]
               GETNOISE_INPUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC GETNOISE_ADDR_CONV THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes8 a) s = x`) (concl th) &&
         free_in `bot:int64` (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    CONV_TAC WORD_BLAST;
    STRIP_TAC];;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r seed (sd:byte list) nonce pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r,512); (seed,32); (word_sub stackpointer (word 888),896)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(r,512); (word_sub stackpointer (word 888),896)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem512_poly_getnoise_eta2) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; seed; nonce] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce])) 128) in
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,512);
                memory :> bytes(word_sub stackpointer (word 888),888)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events do not depend on the    *)
(* seed or the nonce. At the end the frame variables are expanded in them by *)
(* GETNOISE_UNBOT_TAC, since they are not arguments of f_events.             *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let GETNOISE_SAFE_ALLOWED =
  [`pc:num`; `r:int64`; `seed:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let GETNOISE_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GETNOISE_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let GETNOISE_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `delta:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

let GETNOISE_SAFE_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `seed:int64`; `nonce:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 888 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r seed nonce pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [r,512; seed,32; word_sub stackpointer (word 888),896] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [r,512; word_sub stackpointer (word 888),896]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem512_poly_getnoise_eta2) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; seed; nonce] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events seed r pc
                           (word_sub stackpointer (word 888)) returnaddress /\
                    memaccess_inbounds e2
                     [seed,32; r,512; word_sub stackpointer (word 888),896;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [r,512; word_sub stackpointer (word 888),888]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(r,512);
               memory :> bytes(word_sub stackpointer (word 888),888)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
