(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a polynomial from the centered binomial distribution with     *)
(* eta = 2. This is the code for mlkem_poly_cbd2 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* libmlkem.ml). It saves RBX on the stack, so it is verified directly as a  *)
(* subroutine, with that part of the stack.                                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd2:
       +0x0: push   rbx
       +0x1: mov    r8,rdi
       +0x4: mov    r10,rsi
       +0x7: xor    r9d,r9d
       +0xa: nop    WORD PTR [rax+rax*1+0x0]
      +0x10: mov    edi,DWORD PTR [r10+r9*4]
      +0x14: lea    esi,[r9*8+0x0]
      +0x1c: xor    edx,edx
      +0x1e: mov    eax,edi
      +0x20: shr    edi,1
      +0x22: and    eax,0x55555555
      +0x27: and    edi,0x55555555
      +0x2d: add    edi,eax
      +0x2f: nop
      +0x30: mov    ecx,edx
      +0x32: mov    eax,edi
      +0x34: mov    ebx,edi
      +0x36: mov    r11d,esi
      +0x39: shr    eax,cl
      +0x3b: lea    ecx,[rdx+0x2]
      +0x3e: add    edx,0x4
      +0x41: add    esi,0x1
      +0x44: shr    ebx,cl
      +0x46: and    eax,0x3
      +0x49: mov    ecx,ebx
      +0x4b: and    ecx,0x3
      +0x4e: sub    eax,ecx
      +0x50: mov    WORD PTR [r8+r11*2],ax
      +0x55: cmp    edx,0x20
      +0x58: jne    <mlkem_poly_cbd2+0x30>
      +0x5a: add    r9,0x1
      +0x5e: cmp    r9,0x20
      +0x62: jne    <mlkem_poly_cbd2+0x10>
      +0x64: pop    rbx
      +0x65: ret
 ***)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_cbd2"];;

(* ------------------------------------------------------------------------- *)
(* Each iteration loads a 32-bit word t of the input and adds its pairs of   *)
(* bits. Coefficient j of 8 is computed from the sum shifted right by 4 * j  *)
(* and 4 * j + 2, which depends only on the 4-bit field j of t. Below, the   *)
(* computation on a 4-bit field is checked for all its values and related    *)
(* to the bits of the number for the input bytes.                            *)
(* ------------------------------------------------------------------------- *)

let NIBBLE_BIT_STMT =
  `!n m k. k < 4
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 16) DIV 2 EXP k) MOD 2`;;

let NIBBLE_BIT =
  assume_spec NIBBLE_BIT_STMT;;

let CBD2_NIBBLE_STMT =
  `!m. m < 16
       ==> word_sub
            (word_zx (word_add (word_and (word m:4 word) (word 1))
                               (word_and (word_ushr (word m) 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr (word m:4 word) 2)
                                         (word 1))
                               (word_ushr (word m) 3))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2) -
                 &((m DIV 4) MOD 2 + (m DIV 8) MOD 2))`;;

let CBD2_NIBBLE =
  assume_spec CBD2_NIBBLE_STMT;;

let CBD2_LANE_STMT =
  `!n i j t:int32.
      j < 8 /\ word((n DIV 2 EXP (32 * i)) MOD 4294967296) = t
      ==> let x:4 word = word_subword t (4 * j,4) in
          word_sub
            (word_zx (word_add (word_and x (word 1))
                               (word_and (word_ushr x 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr x 2) (word 1))
                               (word_ushr x 3))):int16 =
          iword(&((n DIV 2 EXP (4 * (8 * i + j))) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 1)) MOD 2) -
                &((n DIV 2 EXP (4 * (8 * i + j) + 2)) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 3)) MOD 2))`;;

let CBD2_LANE =
  assume_spec CBD2_LANE_STMT;;

(*** Coefficient k of the iteration, from its 16-bit store, with t as given
 *** by tth
 ***)

let CBD2_LANE_RULE k tth th =
  let jt = mk_small_numeral k in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `t:int32`] CBD2_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `8`)))
             tth)) in
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_VAL_MOD_65536])) th in
  let eq = mk_eq(rand(concl th1),lhs(concl lth)) in
  TRANS th1 (TRANS (BITBLAST_RULE eq) lth);;

(* ------------------------------------------------------------------------- *)
(* The inner loop over the 8 coefficients of an iteration, unrolled in the   *)
(* simulation. R11 is the index of the coefficient, which is tidied up       *)
(* before it is used as a register offset, and CBD2_STORE_TAC puts the fact  *)
(* about the store of the coefficient in its final form.                     *)
(* ------------------------------------------------------------------------- *)

let CBD2_INDEX_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read R11 s = x`) c then
      let th' = REWRITE_RULE[WORD_SX_64_32; ADD_CLAUSES] th in
      MP_TAC th' THEN
      SUBGOAL_THEN (mk_eq(rand(concl th'),wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "CBD2_INDEX_TAC");;

let CBD2_STORE_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
                     mk_comb(`word:num->int64`,
                             mk_binop `( * ):num->num->num` `2` jt)) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes16 addr) s = x` in
  W(fun (asl,w) ->
    let tth0 = snd(find (fun (_,th) ->
      let c = concl th in is_eq c && rand c = `t:int32` &&
      (try fst(dest_const(rator(lhs c))) = "word" with Failure _ -> false))
      asl) in
    let tth = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                (REWRITE_CONV[MULT_ASSOC] THENC NUM_REDUCE_CONV))) tth0 in
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] pat) (concl th)
      then ASSUME_TAC(CBD2_LANE_RULE k tth th)
      else failwith "CBD2_STORE_TAC"));;

let CBD2_INNER_TAC store k =
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC
   ((10 + 16 * k)--(13 + 16 * k)) THEN
  CBD2_INDEX_TAC k THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC
   ((14 + 16 * k)--(25 + 16 * k)) THEN
  (if store then CBD2_STORE_TAC k else ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 2 in common/fips203/fips203.ml,       *)
(* coefficient i of the result is the number of 1 bits among bits 4 * i and  *)
(* 4 * i + 1 of the 128 bytes as a number n, minus the number among bits     *)
(* 4 * i + 2 and 4 * i + 3, here as a 16-bit integer rather than modulo      *)
(* 3329.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,512))
            [(word pc,libmlkem_size); (a,128); (word_sub stackpointer (word 8),16)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),16))
            [(word pc,libmlkem_size); (a,128)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_cbd2) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,128; word_sub stackpointer (word 8),16] /\
           ALL (nonoverlapping (word_sub stackpointer (word 8),16))
               [word pc,libmlkem_size; a,128]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_cbd2) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 8))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,128; r,512; word_sub stackpointer (word 8),16]
                          [r,512; word_sub stackpointer (word 8),8]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512);
                           memory :> bytes(word_sub stackpointer (word 8),
                                           8)])`;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
