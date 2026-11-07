(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks to a byte array.      *)
(* This is the code for mlkem_poly_tobytes from mlkem-native's portable C    *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml); unlike at gcc -O2    *)
(* there is no separate transcription of it.                                 *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with LD2 and ST3, after  *)
(* a check that the input and the output do not overlap, with one branch for *)
(* each of the two orders of the arrays; if they overlap, the code falls     *)
(* back to a scalar loop. Since the specification requires them not to       *)
(* overlap, only the vector code runs, which uses neither the stack nor X18, *)
(* so the specifications are those of gcc12_O2.                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tobytes:
       +0x0: add     x8, x1, #0x200
       +0x4: cmp     x8, x0
       +0x8: b.ls    <mlkem_poly_tobytes+0x54>
       +0xc: add     x8, x0, #0x180
      +0x10: cmp     x8, x1
      +0x14: b.ls    join1                         ---+
      +0x18: mov     x8, xzr                          |
      +0x1c: add     x9, x0, #0x2                     |
      +0x20: add     x10, x1, x8                   <+ |
      +0x24: add     x8, x8, #0x4                   | |
      +0x28: cmp     x8, #0x200                     | |
      +0x2c: ldrh    w11, [x10, #2]                 | |
      +0x30: ldrh    w10, [x10]                     | |
      +0x34: lsl     w12, w11, #4                   | |
      +0x38: lsr     w11, w11, #4                   | |
      +0x3c: orr     w12, w12, w10, lsr #8          | |
      +0x40: sturb   w10, [x9, #-2]                 | |
      +0x44: sturb   w12, [x9, #-1]                 | |
      +0x48: strb    w11, [x9], #3                  | |
      +0x4c: b.ne    loop1                         -+ |
      +0x50: ret                                      |
      +0x54: mov     x8, x1
      +0x58: add     x9, x1, #0x40
      +0x5c: ld2     {v0.8h-v1.8h}, [x8], #32
      +0x60: ushr    v4.8h, v0.8h, #8
      +0x64: shl     v5.8h, v1.8h, #4
      +0x68: orr     v4.16b, v5.16b, v4.16b
      +0x6c: ld2     {v2.8h-v3.8h}, [x8]
      +0x70: mov     x8, x0
      +0x74: ushr    v5.8h, v2.8h, #8
      +0x78: shl     v6.8h, v3.8h, #4
      +0x7c: uzp1    v16.16b, v0.16b, v2.16b
      +0x80: orr     v5.16b, v6.16b, v5.16b
      +0x84: uzp1    v17.16b, v4.16b, v5.16b
      +0x88: shrn    v18.8b, v1.8h, #4
      +0x8c: shrn2   v18.16b, v3.8h, #4
      +0x90: st3     {v16.16b-v18.16b}, [x8], #48
      +0x94: ld2     {v0.8h-v1.8h}, [x9]
      +0x98: add     x9, x1, #0x60
      +0x9c: ld2     {v2.8h-v3.8h}, [x9]
      +0xa0: add     x9, x1, #0x80
      +0xa4: ushr    v17.8h, v0.8h, #8
      +0xa8: shl     v18.8h, v1.8h, #4
      +0xac: ushr    v7.8h, v2.8h, #8
      +0xb0: shl     v16.8h, v3.8h, #4
      +0xb4: uzp1    v4.16b, v0.16b, v2.16b
      +0xb8: orr     v7.16b, v16.16b, v7.16b
      +0xbc: orr     v16.16b, v18.16b, v17.16b
      +0xc0: uzp1    v5.16b, v16.16b, v7.16b
      +0xc4: shrn    v6.8b, v1.8h, #4
      +0xc8: shrn2   v6.16b, v3.8h, #4
      +0xcc: st3     {v4.16b-v6.16b}, [x8]
      +0xd0: add     x8, x1, #0xa0
      +0xd4: ld2     {v0.8h-v1.8h}, [x9]
      +0xd8: add     x9, x1, #0xc0
      +0xdc: ld2     {v2.8h-v3.8h}, [x8]
      +0xe0: add     x8, x0, #0x60
      +0xe4: ushr    v17.8h, v0.8h, #8
      +0xe8: shl     v18.8h, v1.8h, #4
      +0xec: ushr    v7.8h, v2.8h, #8
      +0xf0: shl     v16.8h, v3.8h, #4
      +0xf4: uzp1    v4.16b, v0.16b, v2.16b
      +0xf8: orr     v7.16b, v16.16b, v7.16b
      +0xfc: orr     v16.16b, v18.16b, v17.16b
      +0x100: uzp1    v5.16b, v16.16b, v7.16b
      +0x104: shrn    v6.8b, v1.8h, #4
      +0x108: shrn2   v6.16b, v3.8h, #4
      +0x10c: st3     {v4.16b-v6.16b}, [x8]
      +0x110: add     x8, x1, #0xe0
      +0x114: ld2     {v0.8h-v1.8h}, [x9]
      +0x118: add     x9, x1, #0x100
      +0x11c: ld2     {v2.8h-v3.8h}, [x8]
      +0x120: add     x8, x0, #0x90
      +0x124: ushr    v17.8h, v0.8h, #8
      +0x128: shl     v18.8h, v1.8h, #4
      +0x12c: ushr    v7.8h, v2.8h, #8
      +0x130: shl     v16.8h, v3.8h, #4
      +0x134: uzp1    v4.16b, v0.16b, v2.16b
      +0x138: orr     v7.16b, v16.16b, v7.16b
      +0x13c: orr     v16.16b, v18.16b, v17.16b
      +0x140: uzp1    v5.16b, v16.16b, v7.16b
      +0x144: shrn    v6.8b, v1.8h, #4
      +0x148: shrn2   v6.16b, v3.8h, #4
      +0x14c: st3     {v4.16b-v6.16b}, [x8]
      +0x150: add     x8, x1, #0x120
      +0x154: ld2     {v0.8h-v1.8h}, [x9]
      +0x158: add     x9, x1, #0x140
      +0x15c: ld2     {v2.8h-v3.8h}, [x8]
      +0x160: add     x8, x0, #0xc0
      +0x164: ushr    v17.8h, v0.8h, #8
      +0x168: shl     v18.8h, v1.8h, #4
      +0x16c: ushr    v7.8h, v2.8h, #8
      +0x170: shl     v16.8h, v3.8h, #4
      +0x174: uzp1    v4.16b, v0.16b, v2.16b
      +0x178: orr     v7.16b, v16.16b, v7.16b
      +0x17c: orr     v16.16b, v18.16b, v17.16b
      +0x180: uzp1    v5.16b, v16.16b, v7.16b
      +0x184: shrn    v6.8b, v1.8h, #4
      +0x188: shrn2   v6.16b, v3.8h, #4
      +0x18c: st3     {v4.16b-v6.16b}, [x8]
      +0x190: add     x8, x1, #0x160
      +0x194: ld2     {v0.8h-v1.8h}, [x9]
      +0x198: add     x9, x1, #0x180
      +0x19c: ld2     {v2.8h-v3.8h}, [x8]
      +0x1a0: add     x8, x0, #0xf0
      +0x1a4: ushr    v17.8h, v0.8h, #8
      +0x1a8: shl     v18.8h, v1.8h, #4
      +0x1ac: ushr    v7.8h, v2.8h, #8
      +0x1b0: shl     v16.8h, v3.8h, #4
      +0x1b4: uzp1    v4.16b, v0.16b, v2.16b
      +0x1b8: orr     v7.16b, v16.16b, v7.16b
      +0x1bc: orr     v16.16b, v18.16b, v17.16b
      +0x1c0: uzp1    v5.16b, v16.16b, v7.16b
      +0x1c4: shrn    v6.8b, v1.8h, #4
      +0x1c8: shrn2   v6.16b, v3.8h, #4
      +0x1cc: st3     {v4.16b-v6.16b}, [x8]
      +0x1d0: add     x8, x1, #0x1a0
      +0x1d4: ld2     {v0.8h-v1.8h}, [x9]
      +0x1d8: add     x9, x1, #0x1c0
      +0x1dc: ld2     {v2.8h-v3.8h}, [x8]
      +0x1e0: add     x8, x0, #0x120
      +0x1e4: ushr    v17.8h, v0.8h, #8
      +0x1e8: shl     v18.8h, v1.8h, #4
      +0x1ec: ushr    v7.8h, v2.8h, #8
      +0x1f0: shl     v16.8h, v3.8h, #4
      +0x1f4: uzp1    v4.16b, v0.16b, v2.16b
      +0x1f8: orr     v7.16b, v16.16b, v7.16b
      +0x1fc: orr     v16.16b, v18.16b, v17.16b
      +0x200: uzp1    v5.16b, v16.16b, v7.16b
      +0x204: shrn    v6.8b, v1.8h, #4
      +0x208: shrn2   v6.16b, v3.8h, #4
      +0x20c: st3     {v4.16b-v6.16b}, [x8]
      +0x210: add     x8, x1, #0x1e0
      +0x214: ld2     {v0.8h-v1.8h}, [x9]
      +0x218: ld2     {v2.8h-v3.8h}, [x8]
      +0x21c: add     x8, x0, #0x150
      +0x220: ushr    v17.8h, v0.8h, #8
      +0x224: shl     v18.8h, v1.8h, #4
      +0x228: ushr    v7.8h, v2.8h, #8
      +0x22c: shl     v16.8h, v3.8h, #4
      +0x230: uzp1    v4.16b, v0.16b, v2.16b
      +0x234: orr     v7.16b, v16.16b, v7.16b
      +0x238: orr     v16.16b, v18.16b, v17.16b
      +0x23c: uzp1    v5.16b, v16.16b, v7.16b
      +0x240: shrn    v6.8b, v1.8h, #4
      +0x244: shrn2   v6.16b, v3.8h, #4
      +0x248: st3     {v4.16b-v6.16b}, [x8]
      +0x24c: ret
 ***)

let MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_tobytes"];;

(* ------------------------------------------------------------------------- *)
(* The packing of the coefficients in groups of two into three bytes, as in  *)
(* the gcc12_O2 proof, but for all the groups at once: if the bytes of each  *)
(* group are as the C code computes them, the 384 bytes are the 12-bit       *)
(* coefficients put together little-endian.                                  *)
(* ------------------------------------------------------------------------- *)

let TOBYTES_PACK_STMT =
  `!r s (l:int16 list).
     LENGTH l = 256 /\ ALL (\x. val x < 4096) l /\
     (!k. k < 128
          ==> read (memory :> bytes8 (word_add r (word(3 * k)))) s =
              word_zx (EL (2 * k) l) /\
              read (memory :> bytes8 (word_add r (word(3 * k + 1)))) s =
              word_or (word_shl (word_zx (EL (2 * k + 1) l)) 4)
                      (word_zx (word_ushr (EL (2 * k) l) 8)) /\
              read (memory :> bytes8 (word_add r (word(3 * k + 2)))) s =
              word_zx (word_ushr (EL (2 * k + 1) l) 4))
     ==> read (memory :> bytes(r,384)) s =
         num_of_wordlist (MAP word_zx l:(12 word)list)`;;

let TOBYTES_PACK = assume_spec TOBYTES_PACK_STMT;;

(* ------------------------------------------------------------------------- *)
(* The simulation: the input as the 16-bit coefficients EL j l, merged into  *)
(* the 256-bit loads of LD2, and after each step the registers loaded by     *)
(* LD2 and the 128-bit parts of the memory written by ST3 as joins.          *)
(* ------------------------------------------------------------------------- *)

let TOBYTES_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(32 * k))) in
  READ_MEMORY_MERGE_CONV 4
   (vsubst [addr,`x:int64`] `read (memory :> bytes256 x) s0`)) (0--15);;

let TOBYTES_INPUT_TAC =
  SUBGOAL_THEN
   `!j. j < 256
        ==> read (memory :> bytes16 (word_add a (word(2 * j)))) s0 =
            EL j (l:int16 list)`
   MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `j:num`; `s0:armstate`]
                 READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC TOBYTES_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

let TOBYTES_UNFOLD_CONV =
  REWRITE_CONV[word_deinterleave8_x; word_deinterleave4_x;
               word_deinterleave2_x; word_deinterleave8_y;
               word_deinterleave4_y; word_deinterleave2_y;
               word_split_lo; word_split_hi] THENC
  TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV DIMINDEX_CONV THENC
  TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV THENC
  SIMD_SIMPLIFY_CONV [];;

let TOBYTES_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const(("word_interleave"|"word_deinterleave8_x"|
                     "word_deinterleave8_y"),_) -> true
            | _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV TOBYTES_UNFOLD_CONV) th
    else th) THEN
  SIMD_SIMPLIFY_TAC[];;

(*** The bytes of the 24 stores of 16 bytes ***)

let TOBYTES_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o
      CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th)));;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the output r (384 bytes) and the input a (512 bytes), the scalar loop is  *)
(* taken unless a + 512 <= r or r + 384 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps respectively.      *)
(* ------------------------------------------------------------------------- *)

let TOBYTES_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "TOBYTES_RESOLVE_TAC");;

let TOBYTES_CHECK_TAC (body:int->tactic) =
  MP_TAC(SPECL [`r:int64`; `a:int64`; `384`; `512`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_EXEC (1--3) THEN
  ASM_CASES_TAC `val(word_add a (word 512):int64) <= val(r:int64)` THENL
   [TOBYTES_RESOLVE_TAC THEN body 3;
    TOBYTES_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_EXEC (4--6) THEN
    TOBYTES_RESOLVE_TAC THEN body 6];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As at -O2, the C code relies on the coefficients being *)
(* < 2^12, as stated in its contract, so this is an assumption here.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,384)) [(word pc,libmlkem_size); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_tobytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tobytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* gcc12_O2. Since the events must come from a single simulation (for each   *)
(* of the two cases of the overlap check), the input is named as w j for any *)
(* contents of memory, with w j = EL j l when l has 256 elements, which is   *)
(* used only at the end.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tobytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
