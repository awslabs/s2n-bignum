(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial. This is the code for     *)
(* mlkem_poly_frommsg from mlkem-native's portable C implementation compiled *)
(* by gcc 12 with -O2 (see mlkem_native/README.md). It is verified in the    *)
(* whole image (see libmlkem.ml).                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_frommsg:
       +0x0: mov    r8,rdi
       +0x3: mov    r9d,0x1
       +0x9: xor    edi,edi
       +0xb: nop    DWORD PTR [rax+rax*1+0x0]
      +0x10: xor    ecx,ecx
      +0x12: nop    WORD PTR [rax+rax*1+0x0]
      +0x18: mov    eax,r9d
      +0x1b: shl    eax,cl
      +0x1d: and    al,BYTE PTR [rsi]
      +0x1f: movzx  eax,al
      +0x22: neg    eax
      +0x24: sar    eax,0x10
      +0x27: lea    edx,[rcx+rdi*1]
      +0x2a: add    ecx,0x1
      +0x2d: and    ax,0x681
      +0x31: mov    WORD PTR [r8+rdx*2],ax
      +0x36: cmp    ecx,0x8
      +0x39: jne    <mlkem_poly_frommsg+0x18>
      +0x3b: add    edi,0x8
      +0x3e: add    rsi,0x1
      +0x42: cmp    edi,0x100
      +0x48: jne    <mlkem_poly_frommsg+0x10>
      +0x4a: ret
 ***)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_frommsg"];;

(* ------------------------------------------------------------------------- *)
(* The bits of a byte of an array given as a number.                         *)
(* ------------------------------------------------------------------------- *)

let BYTE_BIT_STMT =
  `!n m k. k < 8
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 256) DIV 2 EXP k) MOD 2`;;

let BYTE_BIT =
  assume_spec BYTE_BIT_STMT;;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop), which   *)
(* the 32-bit LEA computes in RDX, before it is used in the store with a     *)
(* scaled index.                                                             *)
(* ------------------------------------------------------------------------- *)

let FROMMSG_INDEX_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read RDX s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [REWRITE_TAC[WORD_SX_64_32] THEN WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "FROMMSG_INDEX_TAC");;

let FROMMSG_BODY_TAC =
  MAP_EVERY (fun k ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC
     ((3 + 12 * k)--(9 + 12 * k)) THEN
    FROMMSG_INDEX_TAC k THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC
     ((10 + 12 * k)--(14 + 12 * k))) (0--7);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 1 in                           *)
(* common/fips203/fips203.ml, the result for a bit y is the integer closest  *)
(* to 3329 * y / 2, rounding up on ties, i.e. (3329 * y + 1) DIV 2.          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_CORRECT_STMT =
  `!r a n pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,32)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_frommsg) /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,32)) s = n)
      (\s. read RIP s = word (pc + mlkem_poly_frommsg_ret) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512))
        [(word pc,libmlkem_size); (a,32); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_frommsg) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,32)) s = n)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,32]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_frommsg) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_frommsg_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,32; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,32; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_frommsg) /\
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
                          [a,32; r,512; stackpointer,8] [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
