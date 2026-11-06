(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four Keccak states, with  *)
(* the padding. This is the code for the static function                     *)
(* mlk_keccak_absorb_once_x4 from mlkem-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 as one translation unit (see                  *)
(* mlkem_native/README.md), specialized by the compiler to the first byte    *)
(* 0x1F of the padding as mlk_keccak_absorb_once_x4.constprop.0. It is what  *)
(* mlk_keccak_absorb_once_x4 is in the separately compiled gcc12_O2 build,   *)
(* with the specification of that function, with two differences. The        *)
(* compiler has used the ranges of the arguments of its callers (a message   *)
(* of 33 or 34 bytes, against a rate of 136 or 168 bytes) to drop the loop   *)
(* over whole blocks, so the message must be nonempty and shorter than a     *)
(* block here (0 < mlen < r), and the calls of mlkem_keccakf1600x4_xor_bytes *)
(* are calls of mlk_keccakf1600x4_xor_bytes_c, three of them: the message,   *)
(* the byte 0x1F and the byte 0x80. The stack is the 32 bytes of the         *)
(* function (it calls no permutation). It is verified in the whole image     *)
(* (see libmlkem.ml), using the theorem for mlk_keccakf1600x4_xor_bytes_c.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccak_absorb_once_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600x4_xor_bytes_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_keccak_absorb_once_x4:
  adrp1:
     +0x0  adrp    x7, <page>
     +0x4  ldr     x7, [x7, #4088]    // got_stack_chk_guard
     +0x8  str     x30, [sp, #-32]!
     +0xc  mov     w12, w1
    +0x10  mov     x1, x2
    +0x14  mov     x2, x3
    +0x18  mov     x3, x4
    +0x1c  mov     x4, x5
    +0x20  ldr     x5, [x7]
    +0x24  str     x5, [sp, #24]
    +0x28  mov     x5, #0x0
    +0x2c  mov     w7, #0x1f
    +0x30  add     x13, sp, #0x17
    +0x34  mov     x11, x6
    +0x38  mov     x10, x0
    +0x3c  strb    w7, [sp, #23]
    +0x40  bl      mlk_keccakf1600x4_xor_bytes_c
    +0x44  mov     w5, w11
    +0x48  mov     x0, x10
    +0x4c  mov     x4, x13
    +0x50  mov     x3, x13
    +0x54  mov     x2, x13
    +0x58  mov     x1, x13
    +0x5c  mov     w6, #0x1
    +0x60  bl      mlk_keccakf1600x4_xor_bytes_c
    +0x64  mov     w7, #0xffffff80
    +0x68  mov     x0, x10
    +0x6c  mov     x2, x13
    +0x70  mov     x1, x13
    +0x74  sub     w5, w12, #0x1
    +0x78  mov     x3, x13
    +0x7c  mov     w6, #0x1
    +0x80  strb    w7, [sp, #23]
    +0x84  bl      mlk_keccakf1600x4_xor_bytes_c
  adrp2:
    +0x88  adrp    x0, <page>
    +0x8c  ldr     x0, [x0, #4088]    // got_stack_chk_guard
    +0x90  ldr     x2, [sp, #24]
    +0x94  ldr     x1, [x0]
    +0x98  subs    x2, x2, x1
    +0x9c  mov     x1, #0x0
    +0xa0  b.ne    stack_chk_fail
    +0xa4  ldr     x30, [sp], #32
  ret:
    +0xa8  ret
    +0xac  bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_keccak_absorb_once_x4"];;

(* ------------------------------------------------------------------------- *)
(* The four states zero at the start, as 200 bytes each.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_ZERO_SPLIT = prove
 (`!a:int64 m n s:armstate.
        read (memory :> bytes(a,m + n)) s = 0 <=>
        read (memory :> bytes(a,m)) s = 0 /\
        read (memory :> bytes(word_add a (word m),n)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let BYTES800_ZERO = prove
 (`!a:int64 s:armstate.
        read (memory :> bytes(a,800)) s = 0
        ==> read (memory :> bytes(a,200)) s = val(word 0:1600 word) /\
            read (memory :> bytes(word_add a (word 200),200)) s =
            val(word 0:1600 word) /\
            read (memory :> bytes(word_add a (word 400),200)) s =
            val(word 0:1600 word) /\
            read (memory :> bytes(word_add a (word 600),200)) s =
            val(word 0:1600 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `800 = 200 + 600`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `600 = 200 + 400`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `400 = 200 + 200`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; VAL_WORD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, which act on all four states, and for the padding  *)
(* byte on the stack, which is used for all four.                            *)
(* ------------------------------------------------------------------------- *)

let ABSX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let ABSX4_STATES_THEN (ttac:term->term->term->term->tactic) =
  KECCAK_STATE_THEN `st:int64` (fun v0 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v1 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v2 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v3 ->
    ttac v0 v1 v2 v3))));;

let LOCAL_XOR_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let ABSX4_XOR_CALL_TAC off len ms n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    LOCAL_XOR_X4_TAC
     ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
       off; len; v0; v1; v2; v3] @ ms @ [`pc:num`; `read X30 s`]) n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

(*** The byte on the stack, which the three states share ***)

let ABSX4_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 23),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(*** The lane after the three XORs, as the specification states it: since
     the message is shorter than a block, there are no blocks and the
     state before the XORs is zero ***)

let ABSX4_LANE_EQ = prove
 (`!M mlen r.
        0 < mlen /\ mlen < r /\ r <= 200 /\ M < 2 EXP (8 * mlen)
        ==> word_xor (word_xor (word_xor (word 0:1600 word)
                                  (word (2 EXP (8 * 0) * M)))
                               (word (2 EXP (8 * mlen) * 31)))
                     (word (2 EXP (8 * (r - 1)) * 128)) =
            word_xor
             (keccak_absorb r
               (M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r 31 mlen))
               (mlen DIV r))
             (word(((M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad r 31 mlen)) DIV
                    2 EXP (8 * r * mlen DIV r)) MOD 2 EXP (8 * r)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mlen DIV r = 0 /\ mlen MOD r = mlen` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`word 0:1600 word`; `M:num`; `mlen:num`; `r:num`; `31`]
               FINAL_EQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[keccak_absorb; MULT_CLAUSES; EXP; DIV_1; WORD_XOR_0] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN
    REWRITE_TAC[WORD_XOR_0; ARITH_RULE `8 * 0 = 0`; EXP; MULT_CLAUSES; DIV_1] THEN
    DISCH_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states must be zero at the start, and each    *)
(* is then as for mlk_keccak_absorb_once on the corresponding message, with  *)
(* the first byte 0x1F of the padding, as for SHAKE. The address of the      *)
(* stack guard is read from the GOT, and the stack is the 32 bytes of the    *)
(* function.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
    returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < mlen /\ mlen < r /\ r <= 200 /\
        nonoverlapping (st,800) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 32),32)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb r
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb r
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb r
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `r:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
    `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
   (can (term_match [] `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
  MAP_EVERY (fun mm ->
    SUBGOAL_THEN (subst [mm,`M:num`] `M < 2 EXP (8 * mlen)`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rand c = mm &&
           can (term_match [`mlen:num`]
                 `read (memory :> bytes (m,mlen)) s = x`) c
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC])
   [`M0:num`; `M1:num`; `M2:num`; `M3:num`] THEN
  SUBGOAL_THEN
   `0 + mlen <= 200 /\ ~(mlen = 0) /\ mlen + 1 <= 200 /\ r - 1 + 1 <= 200`
  STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** The first call: the four messages ***)

  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (1--1) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (2--17) THEN
  ABSX4_XOR_CALL_TAC `0` `mlen:num` [`M0:num`; `M1:num`; `M2:num`; `M3:num`]
    18 THEN

  (*** The second call: the byte 0x1F at byte mlen ***)

  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (19--26) THEN
  ARGS_32_TAC [`mlen:num`] THEN
  ABSX4_BYTE_FACT_TAC "s26" `31` THEN
  ABSX4_XOR_CALL_TAC `mlen:num` `1` [`31`; `31`; `31`; `31`] 27 THEN

  (*** The third call: the byte 0x80 at byte r - 1 ***)

  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (28--36) THEN
  ARGS_32_TAC [`r:num`] THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ABSX4_BYTE_FACT_TAC "s36" `128` THEN
  ABSX4_XOR_CALL_TAC `r - 1` `1` [`128`; `128`; `128`; `128`] 37 THEN

  (*** The stack guard check and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (38--38) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (39--46) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ABSX4_LANE_EQ THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlk_keccakf1600x4_xor_bytes_c. The events are those of the three       *)
(* calls and of the instructions between them. The theorems of correctness   *)
(* and of constant time and memory safety are derived from this one, or      *)
(* proved separately (the correctness theorem above).                        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let ABSX4_FULL_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `r:num`; `mlen:num`; `guard:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let ABSX4_FULL_XOR_TAC off len ms n =
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    REMOVE_THEN "H_XOR" (fun safety_th ->
      ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mlkem_native_libmlkem_gcc12_O2_mono_mc,
         MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC,
         0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
        ([`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
          `read X3 s`; `read X4 s`; off; len; v0; v1; v2; v3] @ ms @
         [`pc:num`; `read X30 s`]) n THENL
       [EXISTS_E2_TAC (ref ABSX4_FULL_VARS); LABEL_TAC "H_XOR" safety_th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < mlen /\ mlen < r /\ r <= 200 /\
        nonoverlapping (st,800) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 32),32)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb r
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb r
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb r
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events m0 m1 m2 m3 st r mlen guard pc
                            (word_sub stackpointer (word 32)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [st,800; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
   (can (term_match [] `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
  MAP_EVERY (fun mm ->
    SUBGOAL_THEN (subst [mm,`M:num`] `M < 2 EXP (8 * mlen)`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rand c = mm &&
           can (term_match [`mlen:num`]
                 `read (memory :> bytes (m,mlen)) s = x`) c
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC])
   [`M0:num`; `M1:num`; `M2:num`; `M3:num`] THEN
  SUBGOAL_THEN
   `0 + mlen <= 200 /\ ~(mlen = 0) /\ mlen + 1 <= 200 /\ r - 1 + 1 <= 200`
  STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (1--1) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (2--17) THEN
  ABSX4_FULL_XOR_TAC `0` `mlen:num` [`M0:num`; `M1:num`; `M2:num`; `M3:num`]
    18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (19--26) THEN
  ARGS_32_TAC [`mlen:num`] THEN
  ABSX4_BYTE_FACT_TAC "s26" `31` THEN
  ABSX4_FULL_XOR_TAC `mlen:num` `1` [`31`; `31`; `31`; `31`] 27 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (28--36) THEN
  ARGS_32_TAC [`r:num`] THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ABSX4_BYTE_FACT_TAC "s36" `128` THEN
  ABSX4_FULL_XOR_TAC `r - 1` `1` [`128`; `128`; `128`; `128`] 37 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (38--38) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (39--46) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [AP_TERM_TAC THEN MATCH_MP_TAC ABSX4_LANE_EQ THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The theorem of constant time and memory safety, which does not need the   *)
(* states to be zero, nor the contents of the messages.                      *)
(* ------------------------------------------------------------------------- *)

let ABSX4_SAFE_XOR_TAC off len n =
  REMOVE_THEN "H_XOR" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `read X4 s`; off; len; `pc:num`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref ABSX4_FULL_VARS); LABEL_TAC "H_XOR" safety_th]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e st r m0 m1 m2 m3 mlen guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < mlen /\ mlen < r /\ r <= 200 /\
        nonoverlapping (st,800) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 32),32)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_keccak_absorb_once_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events m0 m1 m2 m3 st r mlen guard pc
                            (word_sub stackpointer (word 32)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [st,800; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_XOR" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `0 + mlen <= 200 /\ ~(mlen = 0) /\ mlen + 1 <= 200 /\ r - 1 + 1 <= 200`
  STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (1--1) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (2--17) THEN
  ABSX4_SAFE_XOR_TAC `0` `mlen:num` 18 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (19--26) THEN
  ARGS_32_TAC [`mlen:num`] THEN
  ABSX4_SAFE_XOR_TAC `mlen:num` `1` 27 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (28--36) THEN
  ARGS_32_TAC [`r:num`] THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ABSX4_SAFE_XOR_TAC `r - 1` `1` 37 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (38--38) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_EXEC (39--46) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
