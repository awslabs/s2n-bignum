(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform from ML-KEM.                           *)
(* This is the code for mlkem_poly_ntt from mlkem-native's portable C        *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* Unlike the hand-written kernel, it reads its own table of zetas from the  *)
(* read-only data rather than taking tables as arguments.                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "common/int_linear.ml";;

(**** print_literal_relocs_from_elf
        "x86/mlkem_native/mlkem_native_poly_ntt_gcc12_O2.o";;
 ****)

let mlkem_native_poly_ntt_gcc12_O2_mc,
    mlkem_native_poly_ntt_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "mlk_zetas" -> "mlk_zetas_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_ntt_gcc12_O2_mc"
    "x86/mlkem_native/mlkem_native_poly_ntt_gcc12_O2.o"
(fun b ADDR -> [b[
  0x41; 0x57;              (* PUSH (% r15) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x41; 0xbf; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% r15d) (Imm32 (word 256)) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x49; 0x89; 0xfd;        (* MOV (% r13) (% rdi) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0xbc; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r12d) (Imm32 (word 1)) *)
  0x55;                    (* PUSH (% rbp) *)
  0x48; 0x8d; 0x6f; 0x02;  (* LEA (% rbp) (%% (rdi,2)) *)
  0x53;                    (* PUSH (% rbx) *)
  0x48; 0x8d; 0x1d]; ADDR ("mlk_zetas_data",(-4)); b[
                           (* LEA (% rbx) (Riprel (word_sx (iword
                                  (&WHOLE_READONLY_data - (&pc + &41))))) *)
  0x0f; 0x1f; 0x80; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x8d; 0x4a; 0xff;        (* LEA (% ecx) (%% (rdx,18446744073709551615)) *)
  0x45; 0x89; 0xe0;        (* MOV (% r8d) (% r12d) *)
  0x44; 0x89; 0xff;        (* MOV (% edi) (% r15d) *)
  0x89; 0x54; 0x24; 0xfc;  (* MOV (Memop Doubleword (%%
                                  (rsp,18446744073709551612))) (% edx) *)
  0x41; 0xd3; 0xe0;        (* SHL (% r8d) (% cl) *)
  0x89; 0xd1;              (* MOV (% ecx) (% edx) *)
  0xd3; 0xef;              (* SHR (% edi) (% cl) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x44; 0x8d; 0x1c; 0x3f;  (* LEA (% r11d) (%%% (rdi,0,rdi)) *)
  0x66; 0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x44; 0x89; 0xc0;        (* MOV (% eax) (% r8d) *)
  0x41; 0x83; 0xc0; 0x01;  (* ADD (% r8d) (Imm8 (word 1)) *)
  0x44; 0x0f; 0xbf; 0x0c; 0x43;
                           (* MOVSX (% r9d) (Memop Word (%%% (rbx,1,rax))) *)
  0x39; 0xf9;              (* CMP (% ecx) (% edi) *)
  0x73; 0x54;              (* JAE (Imm8 (word 84)) *)
  0x89; 0xfe;              (* MOV (% esi) (% edi) *)
  0x89; 0xc8;              (* MOV (% eax) (% ecx) *)
  0x29; 0xce;              (* SUB (% esi) (% ecx) *)
  0x49; 0x8d; 0x54; 0x45; 0x00;
                           (* LEA (% rdx) (%%% (r13,1,rax)) *)
  0x83; 0xee; 0x01;        (* SUB (% esi) (Imm8 (word 1)) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x4c; 0x8d; 0x54; 0x75; 0x00;
                           (* LEA (% r10) (%%% (rbp,1,rsi)) *)
  0x89; 0xfe;              (* MOV (% esi) (% edi) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%%% (rax,0,rax))) *)
  0x44; 0x0f; 0xbf; 0x34; 0x72;
                           (* MOVSX (% r14d) (Memop Word (%%% (rdx,1,rsi))) *)
  0x45; 0x0f; 0xaf; 0xf1;  (* IMUL (% r14d) (% r9d) *)
  0x66; 0x41; 0x69; 0xc6; 0x01; 0xf3;
                           (* IMUL3 (% ax) (% r14w,Imm16 (word 62209)) *)
  0x98;                    (* MOVSX (% eax) (% ax) *)
  0x69; 0xc0; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% eax) (% eax,Imm32 (word 4294963967)) *)
  0x44; 0x01; 0xf0;        (* ADD (% eax) (% r14d) *)
  0x44; 0x0f; 0xb7; 0x32;  (* MOVZX (% r14d) (Memop Word (%% (rdx,0))) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x41; 0x29; 0xc6;        (* SUB (% r14d) (% eax) *)
  0x66; 0x44; 0x89; 0x34; 0x72;
                           (* MOV (Memop Word (%%% (rdx,1,rsi))) (% r14w) *)
  0x66; 0x01; 0x02;        (* ADD (Memop Word (%% (rdx,0))) (% ax) *)
  0x48; 0x83; 0xc2; 0x02;  (* ADD (% rdx) (Imm8 (word 2)) *)
  0x49; 0x39; 0xd2;        (* CMP (% r10) (% rdx) *)
  0x75; 0xcc;              (* JNE (Imm8 (word 204)) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x01; 0xdf;        (* ADD (% edi) (% r11d) *)
  0x81; 0xf9; 0xff; 0x00; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 255)) *)
  0x76; 0x8e;              (* JBE (Imm8 (word 142)) *)
  0x8b; 0x54; 0x24; 0xfc;  (* MOV (% edx) (Memop Doubleword (%%
                                  (rsp,18446744073709551612))) *)
  0x83; 0xc2; 0x01;        (* ADD (% edx) (Imm8 (word 1)) *)
  0x83; 0xfa; 0x08;        (* CMP (% edx) (Imm8 (word 8)) *)
  0x0f; 0x85; 0x5e; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967134)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0xc3                     (* RET *)
]]);;


let MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_ntt_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The NTT is done in 7 layers, layer l+1 consisting of 2^l      *)
(* blocks of 2^(8-l) consecutive coefficients. A block uses one zeta to do   *)
(* butterflies on pairs of coefficients 2^(7-l) apart, independently.        *)
(* ------------------------------------------------------------------------- *)

let ntt_fqmul_c = define
 `ntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let ntt_block_c = define
 `ntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then word_add (m i) (ntt_fqmul_c z (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then word_sub (m(i - len)) (ntt_fqmul_c z (m i))
    else m i`;;

let ntt_blocks_c = define
 `ntt_blocks_c l 0 (r:num->int16) = r /\
  ntt_blocks_c l (SUC b) r =
    ntt_block_c (iword(EL (2 EXP l + b) mlk_zetas))
                (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l))
                (ntt_blocks_c l b r)`;;

let ntt_layers_c = define
 `ntt_layers_c 0 (x:num->int16) = x /\
  ntt_layers_c (SUC l) x = ntt_blocks_c l (2 EXP l) (ntt_layers_c l x)`;;

(* ------------------------------------------------------------------------- *)
(* One block, from loading its zeta through the inner loop.                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK = prove
 (`!a zetas pc stackpointer start len k m w12 w15 wl.
     ALL (nonoverlapping (a,512))
         [(word pc,0xdd); (word zetas,256); (stackpointer,4)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 128
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0x50) /\
               read RCX s = word start /\ read RDI s = word(start + len) /\
               read R8 s = word k /\ read R11 s = word(2 * len) /\
               read RBX s = word zetas /\ read R13 s = a /\
               read RBP s = word_add a (word 2) /\
               read R12 s = w12 /\ read R15 s = w15 /\
               read RSP s = word_add stackpointer (word 4) /\
               read (memory :> bytes32 stackpointer) s = wl /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0xb4) /\
               read RCX s = word start /\ read RDI s = word(start + len) /\
               read R8 s = word(k + 1) /\ read R11 s = word(2 * len) /\
               read RBX s = word zetas /\ read R13 s = a /\
               read RBP s = word_add a (word 2) /\
               read R12 s = w12 /\ read R15 s = w15 /\
               read RSP s = word_add stackpointer (word 4) /\
               read (memory :> bytes32 stackpointer) s = wl /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c (iword(EL k mlk_zetas)) start len m i))
          (MAYCHANGE [RIP; RAX; RDX; RSI; R8; R9; R10; R14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `len:num` `pc + 0x80` `pc + 0xaf`
   `\jj s. bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read RDX s = word_add a (word(2 * (start + jj))) /\
           read R10 s = word_add a (word(2 * (start + len))) /\
           read RSI s = word len /\
           read R9 s = word_zx(word_sx(iword(EL k mlk_zetas):int16):int32) /\
           read RCX s = word start /\ read RDI s = word(start + len) /\
           read R8 s = word(k + 1) /\ read R11 s = word(2 * len) /\
           read RBX s = word zetas /\ read R13 s = a /\
           read RBP s = word_add a (word 2) /\
           read R12 s = w12 /\ read R15 s = w15 /\
           read RSP s = word_add stackpointer (word 4) /\
           read (memory :> bytes32 stackpointer) s = wl /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then ntt_block_c (iword(EL k mlk_zetas)) start len m i
                    else m i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Loading the zeta and setting up the pointers for the inner loop ***)

    ENSURES_INIT_TAC "s0" THEN
    READ_INSTANCE_TAC
     `read (memory :> bytes16 (word_add (word zetas) (word (2 * k)))) s0 =
      iword(EL k mlk_zetas)` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    W64_ZX_SMALL_TAC THEN VAL_INT64_TAC `k:num` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--4) THEN
    W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (5--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN WORD_SMALL_TAC;

    (*** The inner loop body, one butterfly, which only partly overwrites
     *** RAX with the 16-bit multiplication, so its old value is named
     ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `rax0:int64` `read RAX` THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `m:num->int16` (concl th)
      then MP_TAC(SPEC `start + jj:num` th) THEN
           MP_TAC(SPEC `start + len + jj:num` th) THEN
           ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
             `\i. ~(i = start + jj) /\ ~(i = start + len + jj)`
             (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                               ==> (!i. P i /\ R i ==> Q i)`)) th))
      else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + len + jj /\ start + len + jj < start + jj) /\
          ~(start + len <= start + len + jj /\
            start + len + jj < start + len + jj)`] THEN
    REWRITE_TAC[ARITH_RULE
     `2 * (start + len + jj) = 2 * (start + jj) + 2 * len`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_REFL; ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN VAL_INT64_TAC `len:num` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      MLKEM_NATIVE_WORD_SIMP_TAC THEN
      REWRITE_TAC[WORD_ZX_ADD_ZX_16; WORD_ZX_SUB_ZX_16] THEN
      REWRITE_TAC[MONTRED_X86_FOLD] THEN
      REWRITE_TAC[ntt_block_c; ntt_fqmul_c; LE_ADD] THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN REWRITE_TAC[ADD_AC; WORD_ADD_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `2 * (start + len + jj) = 2 * (start + jj) + 2 * len`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      MLKEM_NATIVE_WORD_SIMP_TAC THEN
      REWRITE_TAC[WORD_ZX_ADD_ZX_16; WORD_ZX_SUB_ZX_16] THEN
      REWRITE_TAC[MONTRED_X86_FOLD] THEN
      REWRITE_TAC[ntt_block_c; ntt_fqmul_c] THEN
      SUBGOAL_THEN
       `~(start <= start + len + jj /\ start + len + jj < start + len) /\
        start + len <= start + len + jj /\
        start + len + jj < start + 2 * len`
       (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `jj < len` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(start + len + jj) - len = start + jj`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`~(i = start + jj)`; `~(i = start + len + jj)`] THEN
    ARITH_TAC;

    (*** The inner loop back-edge ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop.                                     *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the block head for layer l, block b, and at the block
 *** end for layer l after block b, with the block counters not yet updated
 ***)

let ntt_blockhead_tm,ntt_blockend_tm =
  let headtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RCX s = word(2 * LEN * B) /\
        read RDI s = word(2 * LEN * B + LEN) /\
        read R8 s = word(2 EXP L + B) /\ read R11 s = word(2 * LEN) /\
        read RBX s = word zetas /\ read R13 s = a /\
        read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4) /\
        read (memory :> bytes32 stackpointer) s = word(L + 1) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L B r i)`
  and endtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RCX s = word(2 * LEN * B) /\
        read RDI s = word(2 * LEN * B + LEN) /\
        read R8 s = word(2 EXP L + B + 1) /\ read R11 s = word(2 * LEN) /\
        read RBX s = word zetas /\ read R13 s = a /\
        read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4) /\
        read (memory :> bytes32 stackpointer) s = word(L + 1) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L (B + 1) r i)` in
  let mk tm l b =
    let len = mk_small_numeral(1 lsl (7 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Apply NTT_BLOCK at the head of block b of layer l ***)

let NTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `zetas:num`; `pc:num`; `stackpointer:int64`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
    red `ntt_blocks_c L B r`; `word 1:int64`; `word 256:int64`;
    red `word(L + 1):int32`] MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 ntt_blocks_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** The layer head, setting up the registers for the first block ***)

let NTT_LAYERHEAD_TAC l =
  ENSURES_SEQUENCE_TAC `pc + 0x50` (ntt_blockhead_tm l `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ntt_blocks_c] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** Going from the end of block i to the head of block i + 1, and the
 *** exit from the block loop at the end of the layer
 ***)

let NTT_BLOCKBACK_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--3) THEN
  W32_DECIDE_FLAGS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (4--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN WORD_SMALL_TAC;;

let NTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--3) THEN
  W32_DECIDE_FLAGS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (4--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (number of layers done before it) ***)

let NTT_LAYER_TAC l =
  NTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC `pc + 0xb4` (ntt_blockend_tm l `0`) THEN
  CONJ_TAC THENL
   [NTT_BLOCK_TAC l `0`;
    if l = 0 then NTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl l - 1))
      `pc + 0xb4` `pc + 0xb4`
      (mk_abs(`i:num`,ntt_blockend_tm l `i:num`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC `pc + 0x50` (ntt_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL [NTT_BLOCKBACK_TAC; NTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      NTT_LAYEREXIT_TAC]];;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYER = prove
 (`!a zetas pc stackpointer l r.
     ALL (nonoverlapping (a,512))
         [(word pc,0xdd); (word zetas,256); (stackpointer,4)] /\
     ALL (nonoverlapping (stackpointer,4))
         [(word pc,0xdd); (word zetas,256)] /\
     l < 7
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0x30) /\
               read RDX s = word(l + 1) /\
               read RBX s = word zetas /\ read R13 s = a /\
               read RBP s = word_add a (word 2) /\
               read R12 s = word 1 /\ read R15 s = word 256 /\
               read RSP s = word_add stackpointer (word 4) /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0xc2) /\
               read RBX s = word zetas /\ read R13 s = a /\
               read RBP s = word_add a (word 2) /\
               read R12 s = word 1 /\ read R15 s = word 256 /\
               read RSP s = word_add stackpointer (word 4) /\
               read (memory :> bytes32 stackpointer) s = word(l + 1) /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_blocks_c l (2 EXP l) r i))
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512);
                      memory :> bytes(stackpointer,4)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
  (map NTT_LAYER_TAC (0--6)));;

(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the NTT, within the same bounds as    *)
(* the hand-written kernel.                                                  *)
(* ------------------------------------------------------------------------- *)

let NTT_BLOCKS_C_CLOSED = prove
 (`!l b r i.
     ntt_blocks_c l b r i =
     if i < 2 * 2 EXP (7 - l) * b
     then let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
          if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
          then word_add (r i) (ntt_fqmul_c z (r(i + 2 EXP (7 - l))))
          else word_sub (r(i - 2 EXP (7 - l))) (ntt_fqmul_c z (r i))
     else r i`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ntt_blocks_c; MULT_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[ntt_block_c] THEN
  SUBGOAL_THEN `1 <= 2 EXP (7 - l)` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `n = 2 EXP (7 - l)` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; LEFT_ADD_DISTRIB] THEN
  ASM_CASES_TAC `2 * n * b <= i /\ i < 2 * n * b + 2 * n` THENL
   [SUBGOAL_THEN `i DIV (2 * n) = b /\ i MOD (2 * n) = i - 2 * n * b`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + 2 * n
      ==> ~(i < 2 * n * b) /\ ~(i + n < 2 * n * b) /\
          i < 2 * n * b + 2 * n`] THEN
    ASM_CASES_TAC `i < 2 * n * b + n` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + n ==> i - 2 * n * b < n`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - 2 * n * b < n)`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - n < 2 * n * b)`] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE
     `~(p <= i /\ i < p + 2 * n)
      ==> ~(p <= i /\ i < p + n) /\ ~(p + n <= i /\ i < p + 2 * n)`] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let NTT_LAYERS_C_STEP = prove
 (`!l x i.
     l < 7 /\ i < 256
     ==> ntt_layers_c (SUC l) x i =
         let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
         if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
         then word_add (ntt_layers_c l x i)
                       (ntt_fqmul_c z (ntt_layers_c l x (i + 2 EXP (7 - l))))
         else word_sub (ntt_layers_c l x (i - 2 EXP (7 - l)))
                       (ntt_fqmul_c z (ntt_layers_c l x i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_layers_c; NTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `i < 2 * 2 EXP (7 - l) * 2 EXP l`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `l < 7 ==> 7 - l + l = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

let NTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 ntt_layers_c :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[ntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun l i ->
    let th = SPECL [mk_small_numeral l; `x:num->int16`; mk_small_numeral i]
                   NTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** All the layer equations, in the order of the layers ***)

let NTT_LAYER_EQUATIONS =
  map (fun (l,i) -> SYM(NTT_LAYER_EQUATION l i))
      (List.concat (map (fun l -> map (fun i -> (l,i)) (0--255)) (0--6)));;

let NTT_FINAL_TAC lfn =
  W(fun (asl,w) ->
    let tm = find_term (can (term_match [] `ntt_layers_c 7 x i`)) w in
    let th = apply lfn tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV FORWARD_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let NTT_LAYERS_C_CORRECT = prove
 (`!x. (!i. i < 256 ==> abs(ival(x i)) <= &8191)
       ==> !i. i < 256
               ==> (ival(ntt_layers_c 7 x i) == forward_ntt (ival o x) i)
                   (mod &3329) /\
                   abs(ival(ntt_layers_c 7 x i)) <= &23594`,
  GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let lfn = MLKEM_NATIVE_LOCAL_CONGBOUND_RULE
                (PROCESS_BOUND_ASSUMPTIONS (map snd asl))
                NTT_LAYER_EQUATIONS in
    REPEAT CONJ_TAC THEN NTT_FINAL_TAC lfn));;


(* ------------------------------------------------------------------------- *)
(* The whole code computes the C version of the NTT.                         *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the layer head and layer end for layer l ***)

let ntt_layerhead_tm,ntt_layerend_tm =
  let headtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RDX s = word(L + 1) /\
        read RBX s = word zetas /\ read R13 s = a /\
        read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_layers_c L x i)`
  and endtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RBX s = word zetas /\ read R13 s = a /\
        read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4) /\
        read (memory :> bytes32 stackpointer) s = word(L + 1) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_layers_c (L + 1) x i)` in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

(*** Apply the lemma for layer l at its head ***)

let NTT_LAYER_APPLY_TAC l =
  let th = SPECL [`a:int64`; `zetas:num`; `pc:num`; `stackpointer:int64`;
                  mk_small_numeral l;
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                     `ntt_layers_c L x`)))]
                 MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYER in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`]
          (SPEC_ALL(CONJUNCT2 ntt_layers_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBSUMED_MAYCHANGE_TAC];;

(*** Going from the end of layer l to the head of the next layer ***)

let NTT_LAYERBACK_TAC l =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYERS = prove
 (`!a zetas (x:num->int16) pc stackpointer.
    riprel32_within_bounds zetas (pc + 41) /\
    ALL (nonoverlapping (a,512))
        [(word pc,0xdd); (word zetas,256); (stackpointer,4)] /\
    ALL (nonoverlapping (stackpointer,4))
        [(word pc,0xdd); (word zetas,256)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read RIP s = word (pc + 0x22) /\
           read RDX s = word 1 /\ read R15 s = word 256 /\
           read R13 s = a /\ read R12 s = word 1 /\
           read RBP s = word_add a (word 2) /\
           read RSP s = word_add stackpointer (word 4) /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + 0xd2) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    ntt_layers_c 7 x i))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [RBX; R14] ,,
       MAYCHANGE [memory :> bytes(a,512); memory :> bytes(stackpointer,4)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`;
    `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC `pc + 0x30` (ntt_layerhead_tm 0) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--2) THEN
    MP_TAC(CONJUNCT1(SPECL [`pc:num`; `41`; `0`; `zetas:num`]
      RIP_REL_ADDR_FOLD)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CONJUNCT1 ntt_layers_c];
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + 0xc2` (ntt_layerend_tm l) THEN
    CONJ_TAC THENL [NTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 6 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + 0x30` (ntt_layerhead_tm (l + 1)) THEN
    CONJ_TAC THENL [NTT_LAYERBACK_TAC l; ALL_TAC]) (0--6) THEN

  (*** The exit after the last layer ***)

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The function saves RBX, RBP and R12-R15, interleaving the saves with
 *** setting up some of them, so the core proof starts after the last save,
 *** with the registers that setup has assigned. The core keeps the layer
 *** number in the red zone just below the stack pointer, and its
 *** "stackpointer" parameter is the address of that 4-byte slot.
 ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_CORRECT = prove
 (`!a zetas (x:num->int16) pc stackpointer.
    riprel32_within_bounds zetas (pc + 41) /\
    ALL (nonoverlapping (a,512))
        [(word pc,0xdd); (word zetas,256); (stackpointer,4)] /\
    ALL (nonoverlapping (stackpointer,4))
        [(word pc,0xdd); (word zetas,256)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read RIP s = word (pc + 0x22) /\
           read RDX s = word 1 /\ read R15 s = word 256 /\
           read R13 s = a /\ read R12 s = word 1 /\
           read RBP s = word_add a (word 2) /\
           read RSP s = word_add stackpointer (word 4) /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + 0xd2) /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [RBX; R14] ,,
       MAYCHANGE [memory :> bytes(a,512); memory :> bytes(stackpointer,4)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:num->int16` o
    MATCH_MP MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYERS) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM)) THEN
  GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC `x:num->int16` NTT_LAYERS_C_CORRECT) THEN
  ASM_SIMP_TAC[]);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a zetas (x:num->int16) pc stackpointer returnaddress.
    riprel32_within_bounds zetas (pc + 41) /\
    ALL (nonoverlapping (a,512)) [(word pc,0xdd); (word zetas,256)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 52),60))
        [(word pc,0xdd); (word zetas,256); (a,512)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 52),52)])`,
  REWRITE_TAC[BYTES_LOADED_MLK_ZETAS_DATA] THEN
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC
    (REWRITE_RULE[BYTES_LOADED_MLK_ZETAS_DATA]
      MLKEM_NATIVE_POLY_NTT_GCC12_O2_CORRECT)
    `[R15; R14; R13; R12; RBP; RBX]` 52 (11,7));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas.                         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** One block, from loading its zeta through the inner loop ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK_SAFE = prove
 (`exists f_ev_blk.
   forall e a zetas pc stackpointer start len k w12 w15 wl.
     ALL (nonoverlapping (a,512))
         [(word pc,0xdd); (word zetas,256); (stackpointer,4)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 128
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0x50) /\
               read RCX s = word start /\ read RDI s = word(start + len) /\
               read R8 s = word k /\ read R11 s = word(2 * len) /\
               read RBX s = word zetas /\ read R13 s = a /\
               read RBP s = word_add a (word 2) /\
               read R12 s = w12 /\ read R15 s = w15 /\
               read RSP s = word_add stackpointer (word 4) /\
               read (memory :> bytes32 stackpointer) s = wl /\
               read events s = e)
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0xb4) /\
               read RCX s = word start /\ read RDI s = word(start + len) /\
               read R8 s = word(k + 1) /\ read R11 s = word(2 * len) /\
               read RBX s = word zetas /\ read R13 s = a /\
               read RBP s = word_add a (word 2) /\
               read R12 s = w12 /\ read R15 s = w15 /\
               read RSP s = word_add stackpointer (word 4) /\
               read (memory :> bytes32 stackpointer) s = wl /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc start len k /\
                 memaccess_inbounds e2
                  [a,512; word zetas,256; stackpointer,4]
                  [a,512; stackpointer,4])
          (MAYCHANGE [RIP; RAX; RDX; RSI; R8; R9; R10; R14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (zetas:num) (pc:num) (start:num) (len:num) (k:num).
      APPEND (f_ev_blkend a zetas pc start len k)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a zetas pc start len k j))
                (f_ev_blkhead a zetas pc start len k))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 0x80` `pc + 0xb4`
   `\j s. read RDX s = word_add a (word(2 * (start + j))) /\
          read R10 s = word_add a (word(2 * (start + len))) /\
          read RSI s = word len /\
          read RCX s = word start /\ read RDI s = word(start + len) /\
          read R8 s = word(k + 1) /\ read R11 s = word(2 * len) /\
          read RBX s = word zetas /\ read R13 s = a /\
          read RBP s = word_add a (word 2) /\
          read R12 s = w12 /\ read R15 s = w15 /\
          read RSP s = word_add stackpointer (word 4) /\
          read (memory :> bytes32 stackpointer) s = wl` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Loading the zeta and setting up the pointers for the inner loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    W64_ZX_SMALL_TAC THEN VAL_INT64_TAC `k:num` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--4) THEN
    W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (5--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN VAL_INT64_TAC `len:num` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (13--13) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (14--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(2 * (start + len) = 2 * (start + j) + 2) <=> j + 1 < len`
     SUBST_ALL_TAC THENL
     [UNDISCH_TAC `j < len` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block, which is the inner loop exit ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let NTT_GCC12_O2_BLOCK_EVENTS =
  new_specification ["x86_ntt_gcc12_O2_block_events"]
                    MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a zetas pc stackpointer.
     ALL (nonoverlapping (a,512))
         [(word pc,0xdd); (word zetas,256); (stackpointer,4)] /\
     ALL (nonoverlapping (stackpointer,4))
         [(word pc,0xdd); (word zetas,256)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0x30) /\
               read RDX s = word(L + 1) /\ read RBX s = word zetas /\
               read R13 s = a /\ read RBP s = word_add a (word 2) /\
               read R12 s = word 1 /\ read R15 s = word 256 /\
               read RSP s = word_add stackpointer (word 4) /\
               read events s = e)
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read RIP s = word(pc + 0xc2) /\
               read RBX s = word zetas /\
               read R13 s = a /\ read RBP s = word_add a (word 2) /\
               read R12 s = word 1 /\ read R15 s = word 256 /\
               read RSP s = word_add stackpointer (word 4) /\
               read (memory :> bytes32 stackpointer) s = word(L + 1) /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc stackpointer /\
                 memaccess_inbounds e2
                  [a,512; word zetas,256; stackpointer,4]
                  [a,512; stackpointer,4])
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512);
                      memory :> bytes(stackpointer,4)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The event template for layer l ***)

let lsafe_template l =
  let tm = subst [mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
                  mk_small_numeral(1 lsl l),`NB:num`]
   `\(a:int64) (zetas:num) (pc:num) (stackpointer:int64).
      APPEND (f_ev_lexit a zetas pc stackpointer)
       (APPEND
         (ENUMERATEL NB
           (\i. APPEND (f_ev_ltest a zetas pc stackpointer i)
                 (x86_ntt_gcc12_O2_block_events a zetas pc
                   (2 * LEN * i) LEN (NB + i))))
         (f_ev_lhead a zetas pc stackpointer))
     :(uarch_event)list` in
  rhs(concl(NUM_REDUCE_CONV tm));;

(*** The block lemma for block b of layer l ***)

let ntt_block_events_inst l b ev =
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`; `stackpointer:int64`;
         red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
         `word 1:int64`; `word 256:int64`; red `word(L + 1):int32`]
        NTT_GCC12_O2_BLOCK_EVENTS;;

(*** Register state at the block head and block end (block b) ***)

let lsafe_blockhead_tm,lsafe_blockend_tm =
  let headtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RCX s = word(2 * LEN * B) /\
        read RDI s = word(2 * LEN * B + LEN) /\
        read R8 s = word(2 EXP L + B) /\ read R11 s = word(2 * LEN) /\
        read RBX s = word zetas /\ read R13 s = a /\
        read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4) /\
        read (memory :> bytes32 stackpointer) s = word(L + 1)`
  and endtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RCX s = word(2 * LEN * B) /\
        read RDI s = word(2 * LEN * B + LEN) /\
        read R8 s = word(2 EXP L + B + 1) /\ read R11 s = word(2 * LEN) /\
        read RBX s = word zetas /\ read R13 s = a /\
        read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4) /\
        read (memory :> bytes32 stackpointer) s = word(L + 1)` in
  let mk tm l b =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] tm))) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Simulation of a short piece of straight-line code with flags, where
 *** a final conditional branch may depend on whether i + 1 < k
 ***)

let LSAFE_SIM_TAC k pre_tac n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN pre_tac THEN
  MAP_EVERY (fun i ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         if c = subst [k,`K:num`] `i + 1 < K` then ALL_TAC (asl,w) else
         (SUBGOAL_THEN (mk_eq(c,subst [k,`K:num`] `i + 1 < K`))
          SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) (asl,w)) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    (WORD_SMALL_TAC ORELSE SIMPLE_ARITH_TAC ORELSE
     (AP_TERM_TAC THEN SIMPLE_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole safety proof for layer l ***)

let NTT_LAYER_SAFE_TAC l =
  let nb = mk_small_numeral(1 lsl l) in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nb `pc + 0x50` `pc + 0xc2`
   (mk_abs(`i:num`,lsafe_blockhead_tm l `i:num`)) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    LSAFE_SIM_TAC nb ALL_TAC 10;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xb4` (lsafe_blockend_tm l `i:num`) THEN
    CONJ_TAC THENL
     [EVENTS_LEMMA_TAC (ntt_block_events_inst l `i:num`);
      LSAFE_SIM_TAC nb ALL_TAC 4];
    LSAFE_SIM_TAC nb ALL_TAC 0];;

let NTT_GCC12_O2_LAYER_EVENTS =
  map (fun l ->
        new_specification ["x86_ntt_gcc12_O2_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,NTT_LAYER_SAFE_TAC l)))
      (0--6);;

(*** The whole code from the core onward, with the layers in sequence ***)

let ntt_top_template =
  let lay l = list_mk_comb(mk_const
     ("x86_ntt_gcc12_O2_layer_events_" ^ string_of_int l,[]),
     [`a:int64`; `zetas:num`; `pc:num`; `stackpointer:int64`])
  and fev n =
    list_mk_comb(mk_var(n,`:int64->num->num->int64->(uarch_event)list`),
                 [`a:int64`;`zetas:num`;`pc:num`;`stackpointer:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    if l > 6 then acc else
    let acc' = app (lay l) acc in
    if l = 6 then acc' else
    chain (l + 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let body = app (fev "f_ev_fin") (chain 0 (fev "f_ev_init")) in
  list_mk_abs([`a:int64`;`zetas:num`;`pc:num`;`stackpointer:int64`],body);;

let ntt_safe_layerhead_tm,ntt_safe_layerend_tm =
  let headtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RDX s = word(L + 1) /\ read RBX s = word zetas /\
        read R13 s = a /\ read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4)`
  and endtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read RBX s = word zetas /\
        read R13 s = a /\ read RBP s = word_add a (word 2) /\
        read R12 s = word 1 /\ read R15 s = word 256 /\
        read RSP s = word_add stackpointer (word 4) /\
        read (memory :> bytes32 stackpointer) s = word(L + 1)` in
  let mk tm l =
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm))) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

let ntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`; `stackpointer:int64`]
        (el l NTT_GCC12_O2_LAYER_EVENTS);;

let NTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC ntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xc2` (ntt_safe_layerend_tm 6) THEN
  CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC `1` ALL_TAC 4] THEN
  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x30` (ntt_safe_layerhead_tm l) THEN
    CONJ_TAC THENL [ALL_TAC; EVENTS_LEMMA_TAC (ntt_layer_events_inst l)] THEN
    if l = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xc2` (ntt_safe_layerend_tm (l - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC `1` ALL_TAC 4]) (rev(0--6)) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--2) THEN
  MP_TAC(CONJUNCT1(SPECL [`pc:num`; `41`; `0`; `zetas:num`]
    RIP_REL_ADDR_FOLD)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The specification is that of mk_safety_spec for the C signature of
 *** mlkem_ntt with the table of zetas as a read-only object and the
 *** theorem above, with the registers assigned before the core added to
 *** the precondition.
 ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_SAFE = time prove
 (`exists f_events.
     forall e a zetas pc stackpointer.
       riprel32_within_bounds zetas (pc + 41) /\
       ALL (nonoverlapping (a,512))
           [word pc,0xdd; word zetas,256; stackpointer,4] /\
       ALL (nonoverlapping (stackpointer,4)) [word pc,0xdd; word zetas,256]
       ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
                read RIP s = word (pc + 0x22) /\
                read RDX s = word 1 /\ read R15 s = word 256 /\
                read R13 s = a /\ read R12 s = word 1 /\
                read RBP s = word_add a (word 2) /\
                read RSP s = word_add stackpointer (word 4) /\
                read events s = e)
           (\s. read RIP s = word (pc + 0xd2) /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a zetas pc stackpointer /\
                  memaccess_inbounds e2
                   [a,512; word zetas,256; stackpointer,4]
                   [a,512; stackpointer,4])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [RBX; R14] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(stackpointer,4)])`,
  NTT_SAFE_TOP_TAC);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e a zetas pc stackpointer returnaddress.
       riprel32_within_bounds zetas (pc + 41) /\
       ALL (nonoverlapping (a,512)) [word pc,0xdd; word zetas,256] /\
       ALL (nonoverlapping (word_sub stackpointer (word 52),60))
           [word pc,0xdd; word zetas,256; a,512]
       ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                bytes_loaded s (word zetas) mlk_zetas_data /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a zetas pc (word_sub stackpointer (word 52))
                         returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word zetas,256; word_sub stackpointer (word 52),60]
                   [a,512; word_sub stackpointer (word 52),52])
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 52),52)])`,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_SAFE
    `[R15; R14; R13; R12; RBP; RBX]` 52 (11,7) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
