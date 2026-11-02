(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a Keccak state, with the padding. This is  *)
(* the code for the static function mlk_keccak_absorb_once from              *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md), which is used by its SHA-3 and SHAKE        *)
(* functions. It zeroes the state, XORs in each whole block of r bytes of    *)
(* the message and permutes the state, and then XORs in the rest of the      *)
(* message and the padding, but does not permute the state again. It is      *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x32b0, using the theorems for                     *)
(* mlkem_keccakf1600_xor_bytes at 0x3d40 and mlkem_keccakf1600_permute at    *)
(* 0x3e70 in the image. The state is zeroed with REP STOSQ, so the           *)
(* specifications assume that the direction flag DF is clear, as the ABI     *)
(* requires on entry.                                                        *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccakf1600_permute_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_keccakf1600_xor_bytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    32b0: push   r14
    32b2: xor    eax,eax
    32b4: push   r13
    32b6: mov    r13,rdi
    32b9: add    rdi,0x8
    32bd: push   r12
    32bf: mov    r12d,esi
    32c2: push   rbp
    32c3: mov    r14,r12
    32c6: mov    rbp,rdx
    32c9: push   rbx
    32ca: mov    rbx,rcx
    32cd: mov    rcx,r13
    32d0: sub    rsp,0x10
    32d4: mov    BYTE PTR [rsp+0xc],r8b
    32d9: mov    QWORD PTR [rdi-0x8],0x0
    32e1: mov    QWORD PTR [rdi+0xb8],0x0
    32ec: and    rdi,0xfffffffffffffff8
    32f0: sub    rcx,rdi
    32f3: add    ecx,0xc8
    32f9: shr    ecx,0x3
    32fc: rep    stos QWORD PTR es:[rdi],rax
    32ff: cmp    rbx,r12
    3302: jb     332b <mlk_keccak_absorb_once+0x7b>
    3304: nop    DWORD PTR [rax+0x0]
    3308: mov    rsi,rbp
    330b: mov    ecx,r14d
    330e: xor    edx,edx
    3310: mov    rdi,r13
    3313: call   3d40 <mlkem_keccakf1600_xor_bytes>
    3318: sub    rbx,r12
    331b: mov    rdi,r13
    331e: add    rbp,r12
    3321: call   3e70 <mlkem_keccakf1600_permute>
    3326: cmp    rbx,r12
    3329: jae    3308 <mlk_keccak_absorb_once+0x58>
    332b: sub    r14d,0x1
    332f: mov    r12d,ebx
    3332: test   rbx,rbx
    3335: jne    3378 <mlk_keccak_absorb_once+0xc8>
    3337: lea    rbx,[rsp+0xc]
    333c: mov    edx,r12d
    333f: mov    rdi,r13
    3342: mov    ecx,0x1
    3347: mov    rsi,rbx
    334a: call   3d40 <mlkem_keccakf1600_xor_bytes>
    334f: mov    edx,r14d
    3352: mov    rsi,rbx
    3355: mov    rdi,r13
    3358: mov    ecx,0x1
    335d: mov    BYTE PTR [rsp+0xc],0x80
    3362: call   3d40 <mlkem_keccakf1600_xor_bytes>
    3367: add    rsp,0x10
    336b: pop    rbx
    336c: pop    rbp
    336d: pop    r12
    336f: pop    r13
    3371: pop    r14
    3373: ret
    3374: nop    DWORD PTR [rax+0x0]
    3378: mov    ecx,ebx
    337a: xor    edx,edx
    337c: mov    rsi,rbp
    337f: mov    rdi,r13
    3382: call   3d40 <mlkem_keccakf1600_xor_bytes>
    3387: mov    eax,r14d
    338a: cmp    rax,rbx
    338d: jne    3337 <mlk_keccak_absorb_once+0x87>
    338f: lea    rsi,[rsp+0xc]
    3394: mov    edx,ebx
    3396: mov    rdi,r13
    3399: mov    ecx,0x1
    339e: or     BYTE PTR [rsp+0xc],0x80
    33a3: call   3d40 <mlkem_keccakf1600_xor_bytes>
    33a8: add    rsp,0x10
    33ac: pop    rbx
    33ad: pop    rbp
    33ae: pop    r12
    33b0: pop    r13
    33b2: pop    r14
    33b4: ret
 ***)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x32b0,0x33b5];;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the arguments, the bytes of the message and the blocks.      *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_BYTE_64 = prove
 (`!p. word_zx(word p:int64):byte = word p`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_ZX_SUB1_SMALL = prove
 (`!r. 0 < r /\ r < 2 EXP 32
       ==> word_zx (word_sub (word_zx (word r:int64):int32) (word 1)):int64 =
           word(r - 1)`,
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `r < 4294967296 ==> r < 18446744073709551616`;
   ARITH_RULE `0 < r ==> 1 <= r`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 4294967296`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 18446744073709551616`]);;

let BIT7_SMALL = prove
 (`!p. p < 128 ==> ~bit 7 (word p:byte)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[BIT_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[DIV_LT; ARITH_ODD]);;

let ABSORB_BLOCK_BOUND = prove
 (`!mlen r i. 0 < r /\ i < mlen DIV r ==> r * i + r <= mlen`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC RAND_CONV [th])
    ASSUME_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + c`) THEN
  REWRITE_TAC[ARITH_RULE `r * i + r = (i + 1) * r`; LE_MULT_RCANCEL] THEN
  ASM_ARITH_TAC);;

let ABSORB_MOD_EQ = prove
 (`!mlen r. mlen - r * mlen DIV r = mlen MOD r`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] (CONJUNCT2 DIVISION_SIMP)) THEN
  ARITH_TAC);;

let ABSORB_LOOP_TEST = prove
 (`!mlen r i. 0 < r /\ r * i + r <= mlen
              ==> (r <= mlen - r * (i + 1) <=> i + 1 < mlen DIV r)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`; LE_RDIV_EQ;
               ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, with the state as bytes between them, and for the  *)
(* arguments and the byte of padding on the stack.                           *)
(* ------------------------------------------------------------------------- *)

let LOCAL_XOR_BYTES_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_PERMUTE_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600);;

(*** The values of the 64-bit words for r and mlen ***)

let ABSORB_VAL_TAC =
  MAP_EVERY (fun t ->
    SUBGOAL_THEN (subst [t,`n:num`] `val(word n:int64) = n`)
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC])
   [`r:num`; `mlen:num`];;

(*** The byte p stored on the stack ***)

let ABSORB_BYTE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL_MOD_256; WORD_ZX_BYTE_64]);;

(*** A call of mlkem_keccakf1600_xor_bytes on the state at st ***)

let ABSORB_XOR_CALL_TAC off len data k =
  KECCAK_STATE_AT_TAC `st:int64` THEN
  KECCAK_STATE_THEN `st:int64` (fun v ->
    LOCAL_XOR_BYTES_TAC
     [`read RDI s`; `read RSI s`; off; len; v; data; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`]
     k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

(*** The byte n on the stack in state sname, as a 1-byte array ***)

let ABSORB_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:x86state`) in
  SUBGOAL_THEN
   (subst [s,`s:x86state`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 276),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `p < 128` THEN ARITH_TAC);
    ALL_TAC];;

(*** The byte p OR 128, which is p + 128 since p < 128 ***)

let ABSORB_OR_BYTE_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes8 a) s = x:byte`) c &&
       free_in `word p:byte` (rand c) && free_in `word 128:byte` (rand c)
    then
      let rhs = rand c in
      let bv = genvar `:byte` in
      let eq = mk_imp(mk_neg(mk_comb(`bit 7:byte->bool`,bv)),
                      mk_eq(subst [bv,`word p:byte`] rhs,
                            mk_comb(mk_comb(`word_add:byte->byte->byte`,bv),
                                    `word 128:byte`))) in
      let bth = INST [`word p:byte`,bv] (BITBLAST_RULE eq) in
      let pth = MP bth (MP (SPEC `p:num` BIT7_SMALL) (ASSUME `p < 128`)) in
      ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] (TRANS th pth))
    else NO_TAC);;

(*** The padding after t bytes of the message in the last block ***)

let ABSORB_TAIL_ARITH_TAC =
  SUBGOAL_THEN `(r * q + t) MOD r = t` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN REWRITE_TAC[MULT_CLAUSES; EXP];;

(*** The flag ZF of the comparison of r - 1 with t, as r - 1 = t ***)

let ABSORB_ZF_TAC =
  ARGS_32_TAC [`r - 1`] THEN
  SUBGOAL_THEN `val(word(r - 1):int64) = r - 1` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if free_in `ZF` (concl th) && is_iff (concl th)
    then ASSUME_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0;
           ASSUME `val(word t:int64) = t`;
           ASSUME `val(word(r - 1):int64) = r - 1`] th)
    else NO_TAC);;

(*** Case split on tm, deciding the flags of the comparison with it ***)

let ABSORB_CASE_FLAG_TAC tm =
  ASM_CASES_TAC tm THEN
  FIRST_ASSUM(fun cth ->
    if concl cth = tm || concl cth = mk_neg tm then
      RULE_ASSUM_TAC(fun th ->
        if is_iff(concl th) && free_in `ZF` (concl th)
        then REWRITE_RULE[cth] th else th)
    else NO_TAC);;

needs "x86/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* Tactics for the events, as for the AArch64 code.                          *)
(* ------------------------------------------------------------------------- *)

(*** The abbreviations q and t in the last block expanded ***)

let ABSORB_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV r = q` || c = `mlen MOD r = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

(*** EXISTS_E2_TAC, also allowing the event functions f_ev_... ***)

let ABSORB_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  ABSORB_UNABBREV_TAC THEN
  ((MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL [
    REFL_TAC;
    SAFE_UNIFY_REFL_TAC allowed_vars_e pfx
  ]) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx));;

let ABSORB_SAFE_VARS =
  [`pc:num`; `m:int64`; `st:int64`; `r:num`; `mlen:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, also when the events for the last  ***)
(*** block are already known from the case of a short message          ***)

let ABSORB_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL
        [FULL_UNIFY_F_EVENTS_TAC ORELSE
         (REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
         ALL_TAC])
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let ABSORB_CS_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof. As in        *)
(* keccak_sponge in common/fips202.ml, the message of mlen bytes is a number *)
(* M, and the padded message is the number                                   *)
(* P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen), with     *)
(* mlen DIV r + 1 blocks of r bytes, where p < 128 is the first byte of the  *)
(* padding (0x1F for SHAKE and 0x06 for SHA-3). The result is the state      *)
(* keccak_absorb r P (mlen DIV r) after absorbing the whole blocks of the    *)
(* message, XORed with the last block of P, so that keccak_f1600 of it is    *)
(* keccak_absorb r P (mlen DIV r + 1), the state in keccak_sponge. In        *)
(* mlkem-native, that last permutation is the first step of squeezing. The   *)
(* stack is the 56 bytes of the function, the return address of a call and   *)
(* the 256 bytes used by the permutation below that. The events, which are   *)
(* the same as in the safety theorem below, depend on the lengths r and      *)
(* mlen, which are public, and are given in parts: for the last block,       *)
(* depending on which of the three cases it is, for a message shorter than   *)
(* a block, and otherwise for the loop over the whole blocks. In the last    *)
(* block the equation for mlen in terms of q and t is kept as                *)
(* r * q + t = mlen, so that it does not rewrite mlen in the events, and     *)
(* only the goal for the state is rewritten with it.                         *)
(* ------------------------------------------------------------------------- *)

let ABSORB_CS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (st:int64) (r:num) (mlen:num) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m st r mlen pc stackpointer returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m st r mlen pc stackpointer returnaddress
        else f_ev_t2 m st r mlen pc stackpointer returnaddress)
       (if mlen < r
        then f_ev_short m st r mlen pc stackpointer returnaddress
        else APPEND (f_ev_epil m st r mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m st r mlen pc stackpointer returnaddress i))
                (f_ev_prol m st r mlen pc stackpointer returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `r:num`; `m:int64`; `mlen:num`; `p:num`; `M:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 320 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen)` THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14`;;

let ABSORB_CS_MID =
 `\s. read R13 s = st /\ read RBX s = word(mlen MOD r) /\
      read RBP s = word_add m (word(r * mlen DIV r)) /\
      read R14 s = word r /\
      read RSP s = word_add stackpointer (word 264) /\
      read (memory :> bytes64 (word_add stackpointer (word 280))) s =
      rbx_init /\
      read (memory :> bytes64 (word_add stackpointer (word 288))) s =
      rbp_init /\
      read (memory :> bytes64 (word_add stackpointer (word 296))) s =
      r12_init /\
      read (memory :> bytes64 (word_add stackpointer (word 304))) s =
      r13_init /\
      read (memory :> bytes64 (word_add stackpointer (word 312))) s =
      r14_init /\
      read (memory :> bytes64 (word_add stackpointer (word 320))) s =
      returnaddress /\
      read (memory :> bytes8 (word_add stackpointer (word 276))) s =
      word p /\
      read (memory :> bytes(m,mlen)) s = M /\
      read (memory :> bytes(st,200)) s =
      val(keccak_absorb r P (mlen DIV r))`;;

let ABSORB_CS_INV =
 `\k s. read R13 s = st /\ read RBX s = word(mlen - r * k) /\
        read RBP s = word_add m (word(r * k)) /\
        read R12 s = word r /\ read R14 s = word r /\
        read RSP s = word_add stackpointer (word 264) /\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 288))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 304))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 312))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 320))) s =
        returnaddress /\
        read (memory :> bytes8 (word_add stackpointer (word 276))) s =
        word p /\
        read (memory :> bytes(m,mlen)) s = M /\
        read (memory :> bytes(st,200)) s = val(keccak_absorb r P k)`;;

let ABSORB_CS_SHORT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--21) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC 22 THEN
  MEMSET_DONE_TAC `st:int64` 200 "s22" THEN
  ARGS_32_TAC [`r:num`] THEN ABSORB_BYTE_TAC THEN ABSORB_VAL_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (23--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[keccak_absorb; VAL_WORD_0];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSORB_CS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r` `pc + 0x3308` `pc + 0x332b`
    ABSORB_CS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

    (*** Initialization of the loop, with the state zeroed ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--21) THEN
    MEMSET_PREP_TAC THEN
    MEMSET_STEP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC 22 THEN
    MEMSET_DONE_TAC `st:int64` 200 "s22" THEN
    ARGS_32_TAC [`r:num`] THEN ABSORB_BYTE_TAC THEN ABSORB_VAL_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (23--25) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[keccak_absorb; VAL_WORD_0];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body: XOR in a block, permute, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * i`; `r:num`;
                  `s0:x86state`] READ_MEMORY_BYTES_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--5) THEN
    ARGS_32_TAC [`r:num`] THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    ABSORB_CS_CALL_TAC "H_XOR"
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `0`; `r:num`;
       `keccak_absorb r P i`; `(M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
       `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
      (ABSORB_SAFE_VARS @ [`i:num`]) 6 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (7--10) THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      ABSORB_CS_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; v; `pc:num`; `read RSP s`;
         `read (memory :> bytes64(read RSP s)) s`]
        (ABSORB_SAFE_VARS @ [`i:num`]) 11) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                  word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
      ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                      DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC [12] THEN
    SUBGOAL_THEN
     `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
      val(word r:int64) = r`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC [13] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN EXPAND_TAC "P" THEN
      CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
      UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSORB_CS_XOR_TAC off len data n =
  KECCAK_STATE_AT_TAC `st:int64` THEN
  KECCAK_STATE_THEN `st:int64` (fun v ->
    ABSORB_CS_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; off; len; v; data;
      `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
     ABSORB_SAFE_VARS n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSORB_CS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

let ABSORB_CS_MLEN_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `r * q + t = mlen`));;

let ABSORB_CS_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes (m,mlen)) s0 = M` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P DIV 2 EXP (8 * r * q)) MOD 2 EXP (8 * r) =
    M DIV 2 EXP (8 * r * q) +
    2 EXP (8 * t) * num_of_bytelist(keccak_pad r p mlen)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "q"; "t"] THEN
    MATCH_MP_TAC KECCAK_BLOCK_LAST THEN ASM_SIMP_TAC[KECCAK_PAD_BOUND];
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--2) THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: p at byte 0 and 128 at byte r - 1 ***)

    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--10) THEN
    ABSORB_BYTE_FACT_TAC "s10" `p:num` THEN
    ABSORB_CS_XOR_TAC `0` `1` `p:num` 11 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (12--17) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s17" `128` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `r - 1` `1` `128` 18 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--25) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ABSORB_CS_MLEN_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
      SUBGOAL_THEN `M DIV 2 EXP (8 * r * q) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        UNDISCH_TAC `M < 2 EXP (8 * (r * q + t))` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0] THEN
      COND_CASES_TAC THENL
       [UNDISCH_TAC `0 = r - 1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MP_TAC(INST_TYPE [`:1600`,`:N`]
         (SPECL [`p:num`; `1`; `7`] WORD_XOR_DISJOINT_ADD)) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
        TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `p < 128` THEN ARITH_TAC;
          REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `~(0 = r - 1)` THEN
          ARITH_TAC]];
      ABSORB_CS_EVENTS_TAC];
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of the message after the blocks ***)

  SUBGOAL_THEN
   `0 + t <= 200 /\ M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `r * q + t = mlen`)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * q`; `t:num`;
                `s2:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--9) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSORB_CS_XOR_TAC `0` `t:num` `M DIV 2 EXP (8 * r * q)` 10 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--12) THEN
  ABSORB_ZF_TAC THEN
  ABSORB_CASE_FLAG_TAC `r - 1 = t` THENL
   [(*** The padding is just the single byte p + 128 at byte r - 1 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> concl th = `r - 1 = t`)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (13--19) THEN
    ABSORB_OR_BYTE_TAC THEN ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s19" `p + 128` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `r - 1` `1` `p + 128` 20 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (21--27) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `r * q + r - 1 = mlen`)) THEN
      SUBGOAL_THEN `(r * q + r - 1) MOD r = r - 1` ASSUME_TAC THENL
       [SUBGOAL_THEN `r * q + r - 1 = q * r + (r - 1)` SUBST1_TAC THENL
         [UNDISCH_TAC `0 < r` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `0 < r ==> r - 1 < r`];
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      ABSORB_CS_EVENTS_TAC];

    (*** Otherwise p at byte t and 128 at byte r - 1 ***)

    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (13--19) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSORB_BYTE_FACT_TAC "s19" `p:num` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_CS_XOR_TAC `t:num` `1` `p:num` 20 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (21--26) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s26" `128` THEN
    ABSORB_CS_XOR_TAC `r - 1` `1` `128` 27 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (28--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ABSORB_CS_MLEN_TAC THEN ABSORB_TAIL_ARITH_TAC THEN
      SUBGOAL_THEN
       `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `t < r` THEN ARITH_TAC;
        ALL_TAC] THEN
      W(fun (_,w) -> MP_TAC(ISPECL
        [`2 EXP (8 * t) * p`; `128`; `8 * t + 8 * (r - t - 1)`]
        (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
      REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
       [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `p < 128` THEN ARITH_TAC;
          REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `~(r - 1 = t)` THEN
          UNDISCH_TAC `t < r` THEN ARITH_TAC];
        REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];
      ABSORB_CS_EVENTS_TAC]];;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e st r m mlen p M pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       0 < r /\ r <= 200 /\ p < 128 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 320),328] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [st,200; word_sub stackpointer (word 320),328]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x32b0) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                 (read DF s <=> false) /\
                 read (memory :> bytes(m,mlen)) s = M /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb r
                    (M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad r p mlen))
                    (mlen DIV r))
                  (word((M + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad r p mlen)) DIV
                        2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st r mlen pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 320),328;
                      word(pc + 0x80c0),192]
                     [st,200; word_sub stackpointer (word 320),320]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 320),320)])`,
  ABSORB_CS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x332b` ABSORB_CS_MID THEN CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ABSORB_CS_SHORT_TAC; ABSORB_CS_LOOP_TAC];
    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSORB_CS_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem alone, from the combined one.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!st r m mlen p M pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        0 < r /\ r <= 200 /\ p < 128 /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 320),328)] /\
        ALL (nonoverlapping (word pc,0x82a0))
         [(st,200); (word_sub stackpointer (word 320),328)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x32b0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m,mlen)) s = M)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad r p mlen))
                     (mlen DIV r))
                   (word((M + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad r p mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 320),320)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `r:num`; `m:int64`; `mlen:num`;
    `p:num`; `M:num`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`])) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, for any byte p, with the events in *)
(* the same parts.                                                           *)
(* ------------------------------------------------------------------------- *)

let ABSORB_SAFE_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let ABSORB_SAFE_XOR_TAC off len n =
  ABSORB_SAFE_CALL_TAC "H_XOR"
    [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; off; len;
     `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
    ABSORB_SAFE_VARS n;;

let ABSORB_SAFE_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSORB_DISCHARGE_TAC;;

(*** The last block, the same for a short message and otherwise ***)

let ABSORB_SAFE_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--2) THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--10) THEN
    ABSORB_SAFE_XOR_TAC `0` `1` 11 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (12--17) THEN
    ARGS_32_TAC [`r - 1`] THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_SAFE_XOR_TAC `r - 1` `1` 18 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--25) THEN
    ABSORB_SAFE_FINAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--9) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSORB_SAFE_XOR_TAC `0` `t:num` 10 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--12) THEN
  ABSORB_ZF_TAC THEN
  ABSORB_CASE_FLAG_TAC `r - 1 = t` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> concl th = `r - 1 = t`)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (13--19) THEN
    ARGS_32_TAC [`r - 1`] THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_SAFE_XOR_TAC `r - 1` `1` 20 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (21--27) THEN
    ABSORB_SAFE_FINAL_TAC;
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (13--19) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSORB_SAFE_XOR_TAC `t:num` `1` 20 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (21--26) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_SAFE_XOR_TAC `r - 1` `1` 27 THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (28--34) THEN
    ABSORB_SAFE_FINAL_TAC];;

let ABSORB_SAFE_MID =
 `\s. read R13 s = st /\ read RBX s = word(mlen MOD r) /\
      read RBP s = word_add m (word(r * mlen DIV r)) /\
      read R14 s = word r /\
      read RSP s = word_add stackpointer (word 264) /\
      read (memory :> bytes64 (word_add stackpointer (word 280))) s =
      rbx_init /\
      read (memory :> bytes64 (word_add stackpointer (word 288))) s =
      rbp_init /\
      read (memory :> bytes64 (word_add stackpointer (word 296))) s =
      r12_init /\
      read (memory :> bytes64 (word_add stackpointer (word 304))) s =
      r13_init /\
      read (memory :> bytes64 (word_add stackpointer (word 312))) s =
      r14_init /\
      read (memory :> bytes64 (word_add stackpointer (word 320))) s =
      returnaddress`;;

let ABSORB_SAFE_INV =
 `\k s. read R13 s = st /\ read RBX s = word(mlen - r * k) /\
        read RBP s = word_add m (word(r * k)) /\
        read R12 s = word r /\ read R14 s = word r /\
        read RSP s = word_add stackpointer (word 264) /\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 288))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 304))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 312))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 320))) s =
        returnaddress`;;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e st r m mlen p pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       0 < r /\ r <= 200 /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 320),328] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [st,200; word_sub stackpointer (word 320),328]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x32b0) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [st; word r; m; word mlen; word p] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st r mlen pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 320),328;
                      word(pc + 0x80c0),192]
                     [st,200; word_sub stackpointer (word 320),320]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 320),320)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (st:int64) (r:num) (mlen:num) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m st r mlen pc stackpointer returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m st r mlen pc stackpointer returnaddress
        else f_ev_t2 m st r mlen pc stackpointer returnaddress)
       (if mlen < r
        then f_ev_short m st r mlen pc stackpointer returnaddress
        else APPEND (f_ev_epil m st r mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m st r mlen pc stackpointer returnaddress i))
                (f_ev_prol m st r mlen pc stackpointer returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `r:num`; `m:int64`; `mlen:num`; `p:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 320 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x332b` ABSORB_SAFE_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [(*** A message shorter than a block, with no loop ***)

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--21) THEN
      MEMSET_PREP_TAC THEN
      MEMSET_STEP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC 22 THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (23--24) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN

    (*** Otherwise the loop over the whole blocks ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r` `pc + 0x3308` `pc + 0x332b`
      ABSORB_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--21) THEN
      MEMSET_PREP_TAC THEN
      MEMSET_STEP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC 22 THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (23--25) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--5) THEN
      ARGS_32_TAC [`r:num`] THEN
      ABSORB_SAFE_CALL_TAC "H_XOR"
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `0`; `r:num`;
         `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
        (ABSORB_SAFE_VARS @ [`i:num`]) 6 THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (7--10) THEN
      ABSORB_SAFE_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
         `read (memory :> bytes64(read RSP s)) s`]
        (ABSORB_SAFE_VARS @ [`i:num`]) 11 THEN
      SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                    word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
        ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                        DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC [12] THEN
      SUBGOAL_THEN
       `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
        val(word r:int64) = r`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC [13] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
        ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The last block ***)

    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSORB_SAFE_TAIL_TAC]);;
