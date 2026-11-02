(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 10 bits per coefficient.                   *)
(* This is the code for mlkem_poly_compress_d10 from mlkem-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2660. It     *)
(* saves four registers on the stack and computes the four 10-bit values for *)
(* each five bytes of the result into the eight bytes below them, in the red *)
(* zone, so it is verified directly as a subroutine, with that part of the   *)
(* stack.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2660: push   r13
    2662: lea    rdx,[rdi+0x4]
    2666: xor    ecx,ecx
    2668: mov    r8d,0x9d7dbc00
    266e: movabs rdi,0x100000000
    2678: push   r12
    267a: push   rbp
    267b: push   rbx
    267c: lea    r10,[rsp-0x8]
    2681: mov    r9,rsp
    2684: nop    DWORD PTR [rax+0x0]
    2688: mov    r11,r10
    268b: mov    ebx,ecx
    268d: mov    eax,ebx
    268f: add    r11,0x2
    2693: add    ebx,0x1
    2696: movsx  rax,WORD PTR [rsi+rax*2]
    269b: imul   rax,r8
    269f: add    rax,rdi
    26a2: shr    rax,0x21
    26a6: and    ax,0x3ff
    26aa: mov    WORD PTR [r11-0x2],ax
    26af: cmp    r9,r11
    26b2: jne    268d <mlkem_poly_compress_d10+0x2d>
    26b4: movzx  ebx,WORD PTR [rsp-0x8]
    26b9: movzx  r12d,WORD PTR [rsp-0x6]
    26bf: add    ecx,0x4
    26c2: add    rdx,0x5
    26c6: movzx  eax,WORD PTR [rsp-0x4]
    26cb: movzx  r11d,WORD PTR [rsp-0x2]
    26d1: mov    r13d,ebx
    26d4: lea    ebp,[r12*4+0x0]
    26dc: shr    r12w,0x6
    26e1: movzx  ebx,bl
    26e4: shr    r13w,0x8
    26e9: or     ebp,r13d
    26ec: mov    r13d,eax
    26ef: shr    ax,0x4
    26f3: shl    r13d,0x4
    26f7: movzx  ebp,bpl
    26fb: or     r12d,r13d
    26fe: mov    r13d,eax
    2701: mov    eax,r11d
    2704: shr    r11w,0x2
    2709: shl    eax,0x6
    270c: movzx  r12d,r12b
    2710: mov    BYTE PTR [rdx-0x5],r11b
    2714: or     eax,r13d
    2717: movzx  eax,al
    271a: shl    eax,0x8
    271d: or     eax,r12d
    2720: shl    eax,0x8
    2723: or     eax,ebp
    2725: shl    eax,0x8
    2728: or     eax,ebx
    272a: mov    DWORD PTR [rdx-0x9],eax
    272d: cmp    ecx,0x100
    2733: jne    2688 <mlkem_poly_compress_d10+0x28>
    2739: pop    rbx
    273a: pop    rbp
    273b: pop    r12
    273d: pop    r13
    273f: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2660,0x2740];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 10 bits, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_ARITH = prove
 (`!v. v < 3329
       ==> (4294967296 + v * 2642263040) DIV 8589934592 =
           (2048 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2048 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(2048 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(2048 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(4294967296 + v * 2642263040) - q * 8589934592` THEN
  ASM_ARITH_TAC);;

let WORD_SX_SMALL_64 = prove
 (`!y:int16. val y < 32768 ==> (word_sx y:int64) = word_zx y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let COMPRESS_D10_FIELD = prove
 (`!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word_add (word_mul (word_sx y:int64) (word 2642263040))
                           (word 4294967296))
                 (33,10):10 word) =
            ((2048 * val y + 3329) DIV 6658) MOD 1024`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL_64; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 18446744073709551616`;
    ARITH_RULE `y < 3329 ==> y * 2642263040 < 18446744073709551616`;
    ARITH_RULE `y < 3329
                ==> y * 2642263040 + 4294967296 < 18446744073709551616`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  ASM_SIMP_TAC[COMPRESS_D10_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The packing of four 10-bit values into five bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_5 = prove
 (`!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n DIV 4294967296) MOD 256 = n DIV 4294967296`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP 40` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 65536`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 16777216`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let VAL_JOIN_10X4 = prove
 (`!(u0:10 word) (u1:10 word) (u2:10 word) (u3:10 word).
     val(word_join u3 (word_join u2 (word_join u1 u0:20 word):30 word):
         40 word) =
     val u0 + 1024 * val u1 + 1048576 * val u2 + 1073741824 * val u3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:10 word`; `u1:10 word`; `u2:10 word`; `u3:10 word`] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1024 * val(u1:10 word) + val(u0:10 word) < 1048576`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1048576 * val(u2:10 word) +
                1024 * val(u1:10 word) + val(u0:10 word) < 1073741824`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1073741824 * val(u3:10 word) +
                1048576 * val(u2:10 word) +
                1024 * val(u1:10 word) + val(u0:10 word) < 1099511627776`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ARITH_TAC]);;

(*** The stored bytes as parts of the 40-bit join of the four fields. The
 *** first four are stored together, and the fifth is stored with the
 *** pointer incremented, so its address is put in the same form.
 ***)

let d10_indices = map (fun k ->
  if k = 0 then `4 * i` else
  mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k)) (0--4);;

let d10_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word_add (word_mul (word_sx ((x:num->int16) j):int64) (word 2642263040))
             (word 4294967296):int64`) (butlast d10_indices);;

let d10_join =
  vsubst (zip d10_xatoms [`w0:int64`; `w1:int64`; `w2:int64`; `w3:int64`])
  `word_join (word_subword (w3:int64) (33,10):10 word)
    (word_join (word_subword (w2:int64) (33,10):10 word)
      (word_join (word_subword (w1:int64) (33,10):10 word)
                 (word_subword (w0:int64) (33,10):10 word):20 word):30 word):
    40 word`;;

let D10_PACK_TAC =
  let rule m th =
    let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV
       [WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THENC
       SIMD_SIMPLIFY_CONV [])) th in
    let v = rand(concl th1) in
    let target = mk_comb(mk_comb(`word_subword:40 word->num#num->byte`,
                                 d10_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) d10_xatoms in
    let eq = subst (zip gvs d10_xatoms) (mk_eq(v,target)) in
    let bth = INST (zip d10_xatoms gvs) (BITBLAST_RULE eq) in
    CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                        NUM_REDUCE_CONV)) (TRANS th1 bth) in
  W(fun (asl,w) ->
    let get pat =
      snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
    let th4 = get
      `read (memory :> bytes32 (word_add r (word (5 * i)))) s = x`
    and th1 = get
      `read (memory :> bytes8 (word_add (word_add r (word (5 * i)))
                                        (word 4))) s = x` in
    MAP_EVERY ASSUME_TAC
     (map2 rule (0--4)
        (CONJUNCTS(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th4) @ [th1])));;

(* ------------------------------------------------------------------------- *)
(* The loops. The inner one, unrolled in the simulation, computes four       *)
(* 10-bit values into the red zone; EAX is the index of the coefficient,     *)
(* which is tidied up before it is used in the address of the load. The      *)
(* pointer to the result is put in the form of the addresses of the stores   *)
(* before it is incremented.                                                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_INDEX_TAC k =
  let jt = el k d10_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read RAX s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 64` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "COMPRESS_D10_INDEX_TAC");;

let COMPRESS_D10_BODY_TAC =
  X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--2) THEN
  MAP_EVERY (fun k ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC
     [3 + 11 * k] THEN
    COMPRESS_D10_INDEX_TAC k THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC
     ((4 + 11 * k)--(13 + 11 * k)) THEN
    PTR_DECIDE_RIP_TAC) (0--3) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RDX s = word_add r (word (5 * i + 4))`)
           (concl th)
    then REWRITE_RULE[WORD_RULE
          `word_add r (word (5 * i + 4)):int64 =
           word_add (word_add r (word (5 * i))) (word 4)`] th
    else th) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (47--78);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 10 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 1024 * x / 3329, rounding up on ties, modulo 1024, i.e.                   *)
(* ((2048 * x + 3329) DIV 6658) MOD 1024, and as for mlkem_encode 10 the     *)
(* 10-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,320))
            [(word pc,0x82a0); (a,512);
             (word_sub stackpointer (word 40),48)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),48))
            [(word pc,0x82a0); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x2660) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,320)) s =
                       nsum {i | i < 256}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320);
                         memory :> bytes(word_sub stackpointer
                                                  (word 40),40)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 40 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN

  (*** The outer loop, over groups of 4 coefficients ***)

  ENSURES_WHILE_UP_TAC `64` `pc + 0x2688` `pc + 0x272d`
   `\i s. read RDX s = word_add r (word(5 * i + 4)) /\
          read RCX s = word(4 * i) /\
          read RSI s = a /\
          read R8 s = word 2642263040 /\
          read RDI s = word 4294967296 /\
          read R10 s = stackpointer /\
          read R9 s = word_add stackpointer (word 8) /\
          read RSP s = word_add stackpointer (word 8) /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbx_init /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,5 * i)) s =
               nsum {j | j < 4 * i}
                (\j. ((2048 * val(x j) + 3329) DIV 6658) MOD 1024 *
                     2 EXP (10 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the four registers ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, for four coefficients and five bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun jt ->
      FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 64` THEN ARITH_TAC; DISCH_TAC])
     (butlast d10_indices) THEN
    COMPRESS_D10_BODY_TAC THEN

    (*** The new bytes as parts of the join of the 10-bit fields ***)

    D10_PACK_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `5 * (i + 1) + 4 = 5 * i + 9`] THEN
      CONV_TAC WORD_RULE;
      WORD_SMALL_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE
     `5 * (i + 1) = ((((5 * i + 1) + 1) + 1) + 1) + 1`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(5 * i + 1) + 1 = 5 * i + 2`;
                ARITH_RULE `(5 * i + 2) + 1 = 5 * i + 3`;
                ARITH_RULE `(5 * i + 3) + 1 = 5 * i + 4`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INST_TYPE [`:40`,`:M`; `:8`,`:N`] VAL_WORD_SUBWORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1] THEN
    MP_TAC(SPEC (mk_comb(`val:40 word->num`,d10_join)) BYTES_OF_NUM_5) THEN
    MP_TAC(ISPEC d10_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th)) THEN
    REWRITE_TAC[VAL_JOIN_10X4] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D10_FIELD) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 64` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) (butlast d10_indices) THEN

    (*** The new values in the number for the output ***)

    REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`; NSUM_LT_ADD] THEN
    REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUM_RING;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_zx (word (4 * i):int64)) (word 256):int32) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                  DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 64 ==> 4 * i < 18446744073709551616`;
                   ARITH_RULE `i < 64 ==> 4 * i < 4294967296`] THEN
      UNDISCH_TAC `i < 64` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       ALL (nonoverlapping (r,320))
           [word pc,0x82a0; a,512; word_sub stackpointer (word 40),48] /\
       ALL (nonoverlapping (word_sub stackpointer (word 40),48))
           [word pc,0x82a0; a,512]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x2660) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r pc
                           (word_sub stackpointer (word 40)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,320; word_sub stackpointer (word 40),48]
                     [r,320; word_sub stackpointer (word 40),40]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,320);
                        memory :> bytes(word_sub stackpointer (word 40),40)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop a r pc stackpointer returnaddress i))
          (f_ev_prol a r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 40 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + 0x2688` `pc + 0x2739`
   `\i s. read RDX s = word_add r (word(5 * i + 4)) /\
          read RCX s = word(4 * i) /\
          read RSI s = a /\
          read R10 s = stackpointer /\
          read R9 s = word_add stackpointer (word 8) /\
          read RSP s = word_add stackpointer (word 8) /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbx_init` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--11) THEN
    REWRITE_TAC[MULT_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--5) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  COMPRESS_D10_BODY_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (79--80) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN
   `word_zx (word_add (word_zx (word (4 * i):int64):int32) (word 4)):int64 =
    word(4 * (i + 1))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [WORD_SMALL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(val(word_zx (word (4 * (i + 1)):int64):int32) = val(word 256:int32)) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 4 * (i + 1) < 18446744073709551616`; ARITH_RULE
     `i < 64 ==> 4 * (i + 1) < 4294967296`] THEN
    UNDISCH_TAC `i < 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) + 4 = 5 * i + 9`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
