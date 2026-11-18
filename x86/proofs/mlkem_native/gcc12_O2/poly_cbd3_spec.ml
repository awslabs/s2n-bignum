(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 3. This is the code for         *)
(* mlkem_poly_cbd3 from mlkem-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mlkem_native/README.md). It is verified in the whole *)
(* image (see libmlkem.ml). As for mlkem_poly_cbd2, it saves RBX on the      *)
(* stack, so it is verified directly as a subroutine, with that part of the  *)
(* stack.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd3:
       +0x0: push   rbx
       +0x1: mov    r8,rdi
       +0x4: xor    r9d,r9d
       +0x7: mov    rdi,rsi
       +0xa: nop    WORD PTR [rax+rax*1+0x0]
      +0x10: movzx  eax,BYTE PTR [rdi+0x1]
      +0x14: movzx  edx,BYTE PTR [rdi+0x2]
      +0x18: mov    r10d,r9d
      +0x1b: movzx  ecx,BYTE PTR [rdi]
      +0x1e: shl    edx,0x10
      +0x21: shl    eax,0x8
      +0x24: or     eax,edx
      +0x26: or     eax,ecx
      +0x28: mov    esi,eax
      +0x2a: mov    edx,eax
      +0x2c: shr    eax,0x2
      +0x2f: shr    esi,1
      +0x31: and    eax,0x249249
      +0x36: and    edx,0x249249
      +0x3c: and    esi,0x249249
      +0x42: add    esi,eax
      +0x44: add    esi,edx
      +0x46: xor    edx,edx
      +0x48: mov    ecx,edx
      +0x4a: mov    eax,esi
      +0x4c: mov    ebx,esi
      +0x4e: mov    r11d,r10d
      +0x51: shr    eax,cl
      +0x53: lea    ecx,[rdx+0x3]
      +0x56: add    edx,0x6
      +0x59: add    r10d,0x1
      +0x5d: shr    ebx,cl
      +0x5f: and    eax,0x7
      +0x62: mov    ecx,ebx
      +0x64: and    ecx,0x7
      +0x67: sub    eax,ecx
      +0x69: mov    WORD PTR [r8+r11*2],ax
      +0x6e: cmp    edx,0x18
      +0x71: jne    <mlkem_poly_cbd3+0x48>
      +0x73: add    r9d,0x4
      +0x77: add    rdi,0x3
      +0x7b: cmp    r9d,0x100
      +0x82: jne    <mlkem_poly_cbd3+0x10>
      +0x84: pop    rbx
      +0x85: ret
 ***)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_cbd3"];;

(*** The three bytes for four coefficients, as parts of a 24-bit word ***)

let CBD3_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,192)) s = n /\ i < 64 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * i)):24 word) (8 * j,8)`;;

let CBD3_BYTES =
  assume_spec CBD3_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* Each iteration takes three bytes as a 24-bit word t and adds its groups   *)
(* of three bits. Coefficient j of 4 is computed from the sum shifted right  *)
(* by 6 * j and 6 * j + 3, which depends only on the 6-bit field j of t.     *)
(* Below, the computation on a 6-bit field is checked for all its values and *)
(* related to the bits of the number for the input bytes, as for             *)
(* mlkem_poly_cbd2.                                                          *)
(* ------------------------------------------------------------------------- *)

let SIXBIT_BIT_STMT =
  `!n m k. k < 6
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 64) DIV 2 EXP k) MOD 2`;;

let SIXBIT_BIT =
  assume_spec SIXBIT_BIT_STMT;;

let CBD3_FIELD_STMT =
  `!m. m < 64
       ==> word_sub
            (word_zx (word_add (word_add (word_and (word m:6 word) (word 1))
                                         (word_and (word_ushr (word m) 1)
                                                   (word 1)))
                               (word_and (word_ushr (word m) 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr (word m:6 word)
                                                              3) (word 1))
                                         (word_and (word_ushr (word m) 4)
                                                   (word 1)))
                               (word_ushr (word m) 5))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2 + (m DIV 4) MOD 2) -
                 &((m DIV 8) MOD 2 + (m DIV 16) MOD 2 + (m DIV 32) MOD 2))`;;

let CBD3_FIELD =
  assume_spec CBD3_FIELD_STMT;;

let CBD3_LANE_STMT =
  `!n i j w:24 word.
      j < 4 /\ word(n DIV 2 EXP (24 * i)) = w
      ==> let x:6 word = word_subword w (6 * j,6) in
          word_sub
            (word_zx (word_add (word_add (word_and x (word 1))
                                         (word_and (word_ushr x 1) (word 1)))
                               (word_and (word_ushr x 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr x 3) (word 1))
                                         (word_and (word_ushr x 4) (word 1)))
                               (word_ushr x 5))):int16 =
          iword(&((n DIV 2 EXP (6 * (4 * i + j))) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 1)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 2)) MOD 2) -
                &((n DIV 2 EXP (6 * (4 * i + j) + 3)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 4)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 5)) MOD 2))`;;

let CBD3_LANE =
  assume_spec CBD3_LANE_STMT;;

(*** Coefficient k of the iteration, from its 16-bit store, with w as given
 *** by tth
 ***)

let CBD3_LANE_RULE k tth th =
  let jt = mk_small_numeral k in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `w:24 word`] CBD3_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `4`)))
             tth)) in
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_VAL_MOD_65536])) th in
  let eq = mk_eq(rand(concl th1),lhs(concl lth)) in
  TRANS th1 (TRANS (BITBLAST_RULE eq) lth);;

(* ------------------------------------------------------------------------- *)
(* The inner loop over the 4 coefficients of an iteration, unrolled in the   *)
(* simulation, as for mlkem_poly_cbd2.                                       *)
(* ------------------------------------------------------------------------- *)

let CBD3_INDEX_TAC k =
  let jt = if k = 0 then `4 * i` else
           mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read R11 s = x`) c then
      MP_TAC th THEN
      SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 64` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "CBD3_INDEX_TAC");;

let CBD3_STORE_TAC k =
  let jt = if k = 0 then `4 * i` else
           mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k) in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
                     mk_comb(`word:num->int64`,
                             mk_binop `( * ):num->num->num` `2` jt)) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes16 addr) s = x` in
  W(fun (asl,w) ->
    let tth = snd(find (fun (_,th) ->
      let c = concl th in is_eq c && rand c = `w:24 word` &&
      (try fst(dest_const(rator(lhs c))) = "word" with Failure _ -> false))
      asl) in
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] pat) (concl th)
      then ASSUME_TAC(CBD3_LANE_RULE k tth th)
      else failwith "CBD3_STORE_TAC"));;

let CBD3_INNER_TAC store k =
  (if k = 0 then ALL_TAC else
   X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC
    ((19 + 16 * k)--(22 + 16 * k))) THEN
  CBD3_INDEX_TAC k THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC
   ((23 + 16 * k)--(34 + 16 * k)) THEN
  (if store then CBD3_STORE_TAC k else ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 3 in common/fips203/fips203.ml,       *)
(* coefficient i of the result is the number of 1 bits among bits 6 * i to   *)
(* 6 * i + 2 of the 192 bytes as a number n, minus the number among bits     *)
(* 6 * i + 3 to 6 * i + 5, here as a 16-bit integer rather than modulo 3329. *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,512))
            [(word pc,libmlkem_size); (a,192); (word_sub stackpointer (word 8),16)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),16))
            [(word pc,libmlkem_size); (a,192)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_cbd3) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,192; word_sub stackpointer (word 8),16] /\
           ALL (nonoverlapping (word_sub stackpointer (word 8),16))
               [word pc,libmlkem_size; a,192]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_cbd3) /\
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
                          [a,192; r,512; word_sub stackpointer (word 8),16]
                          [r,512; word_sub stackpointer (word 8),8]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512);
                           memory :> bytes(word_sub stackpointer (word 8),
                                           8)])`;;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
