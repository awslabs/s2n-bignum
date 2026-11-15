(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message. This is the code for     *)
(* mlkem_poly_tomsg from mlkem-native's portable C implementation compiled   *)
(* by gcc 12 with -O2 (see mlkem_native/README.md). It is verified in the    *)
(* whole image (see libmlkem.ml).                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomsg:
       +0x0: xor    r8d,r8d
       +0x3: nop    DWORD PTR [rax+rax*1+0x0]
       +0x8: mov    BYTE PTR [rdi],0x0
       +0xb: xor    edx,edx
       +0xd: xor    ecx,ecx
       +0xf: nop
      +0x10: lea    eax,[rcx+r8*1]
      +0x14: movsx  eax,WORD PTR [rsi+rax*2]
      +0x18: imul   eax,eax,0x13afb8
      +0x1e: add    eax,0x40000000
      +0x23: shr    eax,0x1f
      +0x26: shl    eax,cl
      +0x28: add    ecx,0x1
      +0x2b: or     edx,eax
      +0x2d: mov    BYTE PTR [rdi],dl
      +0x2f: cmp    ecx,0x8
      +0x32: jne    <mlkem_poly_tomsg+0x10>
      +0x34: add    r8d,0x8
      +0x38: add    rdi,0x1
      +0x3c: cmp    r8d,0x100
      +0x43: jne    <mlkem_poly_tomsg+0x8>
      +0x45: ret
 ***)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_tomsg"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D1_ARITH_STMT =
  `!v. v < 3329
       ==> (1073741824 + v * 1290168) DIV 2147483648 =
           (4 * v + 3329) DIV 6658`;;

let COMPRESS_D1_ARITH =
  assume_spec COMPRESS_D1_ARITH_STMT;;

let TOMSG_BIT_STMT =
  `!y:int16.
        val y < 3329
        ==> word_ushr
             (word_zx (word_zx (word_add
               (word_zx (word_zx (word_mul
                  (word_zx (word_zx (word_sx y:int32):int64):int32)
                  (word 1290168)):int64):int32)
               (word 1073741824)):int64):int32) 31 =
            word(((4 * val y + 3329) DIV 6658) MOD 2)`;;

let TOMSG_BIT =
  assume_spec TOMSG_BIT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Splitting off the bits for one byte from the number for the message.      *)
(* ------------------------------------------------------------------------- *)

let NSUM_BYTE_STMT =
  `!f m. nsum {k | k < 8} (\k. f(m + k) * 2 EXP (m + k)) =
         2 EXP m * nsum {k | k < 8} (\k. f(m + k) * 2 EXP k)`;;

let NSUM_BYTE =
  assume_spec NSUM_BYTE_STMT;;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop), which   *)
(* the 32-bit LEA computes in RAX, before it is used in the load with a      *)
(* scaled index.                                                             *)
(* ------------------------------------------------------------------------- *)

let tomsg_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let TOMSG_INDEX_TAC k =
  let jt = el k tomsg_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read RAX s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [REWRITE_TAC[WORD_SX_64_32] THEN WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "TOMSG_INDEX_TAC");;

let TOMSG_INNER_TAC =
  X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (1--4) THEN
  MAP_EVERY (fun k ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC
     ((5 + 11 * k)--(5 + 11 * k)) THEN
    TOMSG_INDEX_TAC k THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC
     ((6 + 11 * k)--(15 + 11 * k))) (0--7);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 1 in common/fips203/fips203.ml,  *)
(* the bit for a coefficient x in [0,3329) is the integer closest to         *)
(* 2 * x / 3329, rounding up on ties, modulo 2, i.e.                         *)
(* ((4 * x + 3329) DIV 6658) MOD 2, and as for mlkem_encode 1 the bits are   *)
(* put together little-endian. Like the C code, this relies on the           *)
(* coefficients being in [0,3329).                                           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_CORRECT_STMT =
  `!r a x pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,32)) [(word pc,libmlkem_size); (a,512)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_tomsg) /\
           C_ARGUMENTS [r; a] s /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i)
      (\s. read RIP s = word (pc + mlkem_poly_tomsg_ret) /\
           ((!i. i < 256 ==> val(x i) < 3329)
            ==> read(memory :> bytes(r,32)) s =
                nsum {i | i < 256}
                     (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 * 2 EXP i)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,32)])`;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,32))
        [(word pc,libmlkem_size); (a,512); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_tomsg) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           ((!i. i < 256 ==> val(x i) < 3329)
            ==> read(memory :> bytes(r,32)) s =
                nsum {i | i < 256}
                     (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 * 2 EXP i)))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,32)])`;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,32)) [word pc,libmlkem_size; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_tomsg) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_tomsg_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,512; r,32] [r,32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,32)])`;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,32))
               [word pc,libmlkem_size; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_tomsg) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,32; stackpointer,8] [r,32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,32)])`;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
