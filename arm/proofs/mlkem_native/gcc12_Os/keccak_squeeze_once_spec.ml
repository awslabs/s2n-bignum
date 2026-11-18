(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a Keccak state. This is the code for the static      *)
(* function mlk_keccak_squeeze_once from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -Os (see mlkem_native/README.md),  *)
(* which is used by its SHA-3 and SHAKE256 functions. While outlen bytes of  *)
(* output remain, it permutes the state and then extracts the first r bytes  *)
(* of it, or all the bytes that remain if there are fewer. It is verified in *)
(* the whole image (see libmlkem.ml), using the theorems for                 *)
(* mlkem_keccakf1600_permute and mlkem_keccakf1600_extract_bytes in the      *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The code in the image:

    mlk_keccak_squeeze_once:
       +0x0: stp     x19, x20, [sp, #-48]!
       +0x4: mov     x20, x0
       +0x8: mov     x19, x1
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x21, x2
      +0x14: mov     w22, w3
      +0x18: stp     x23, x30, [sp, #32]
      +0x1c: cbnz    x19, <mlk_keccak_squeeze_once+0x30>
      +0x20: ldp     x21, x22, [sp, #16]
      +0x24: ldp     x23, x30, [sp, #32]
      +0x28: ldp     x19, x20, [sp], #48
      +0x2c: ret
      +0x30: mov     x0, x21
      +0x34: bl      <mlkem_keccakf1600_permute>
      +0x38: cmp     x22, x19
      +0x3c: mov     x1, x20
      +0x40: csel    x23, x22, x19, ls
      +0x44: mov     x0, x21
      +0x48: mov     w3, w23
      +0x4c: mov     w2, #0x0
      +0x50: add     x20, x20, x23
      +0x54: sub     x19, x19, x23
      +0x58: bl      <mlkem_keccakf1600_extract_bytes>
      +0x5c: b       <mlk_keccak_squeeze_once+0x1c>
 ***)

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlk_keccak_squeeze_once"];;

(* ------------------------------------------------------------------------- *)
(* The bytes of one block of the output, the numbers for the pointer and the *)
(* number of bytes left, and the loop test.                                  *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_ONCE_BLOCK_STMT =
  `!(S:1600 word) r k n.
        0 < r /\ n <= r /\ r <= 200
        ==> num_of_bytelist
             (list_of_seq
               (\j. word_subword (keccak_squeeze ((r * k + j) DIV r + 1) S)
                                 (8 * ((r * k + j) MOD r),8):byte) n) =
            val(keccak_squeeze (k + 1) S) MOD 2 EXP (8 * n)`;;

let SQUEEZE_ONCE_BLOCK = assume_spec SQUEEZE_ONCE_BLOCK_STMT;;

(*** The number of bytes extracted in each iteration, MIN r (outlen - r * i),
     as the result of the compare and select ***)

let SQUEEZE_ONCE_CSEL_STMT =
  `!r x. r < 2 EXP 64 /\ x < 2 EXP 64
         ==> (if ~(val(word x:int64) <= r /\
                   ~(val(word_sub (word r:int64) (word x)) = 0))
              then word r else word x):int64 = word(MIN r x)`;;

let SQUEEZE_ONCE_CSEL = assume_spec SQUEEZE_ONCE_CSEL_STMT;;

(*** The iterations: k = (outlen + r - 1) DIV r, and for i < k the bytes done
     before and after iteration i ***)

let SQUEEZE_ONCE_ITER_STMT =
  `!outlen r i.
        0 < r /\ i < (outlen + r - 1) DIV r
        ==> r * i < outlen /\
            MIN outlen (r * i) = r * i /\
            MIN outlen (r * (i + 1)) = r * i + MIN r (outlen - r * i) /\
            outlen - r * i - MIN r (outlen - r * i) =
            outlen - MIN outlen (r * (i + 1))`;;

let SQUEEZE_ONCE_ITER = assume_spec SQUEEZE_ONCE_ITER_STMT;;

let SQUEEZE_ONCE_END_STMT =
  `!outlen r.
        0 < r
        ==> MIN outlen (r * ((outlen + r - 1) DIV r)) = outlen`;;

let SQUEEZE_ONCE_END = assume_spec SQUEEZE_ONCE_END_STMT;;

let SQUEEZE_ONCE_TEST_STMT =
  `!outlen r i.
        0 < r /\ i < (outlen + r - 1) DIV r
        ==> (outlen - MIN outlen (r * (i + 1)) = 0 <=>
             ~(i + 1 < (outlen + r - 1) DIV r))`;;

let SQUEEZE_ONCE_TEST = assume_spec SQUEEZE_ONCE_TEST_STMT;;

(*** The bound on outlen from the nonoverlapping, and the 64-bit words for
     outlen and r ***)

let SQONCE_BOUND_TAC =
  SUBGOAL_THEN `200 + outlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word outlen:int64) = outlen /\ val(word r:int64) = r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let SQONCE_PRESERVED_TAC =
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23`;;

(*** The test of outlen = 0 at the start, when it is known to be false ***)

let SQONCE_NONZERO_TAC =
  let t1 = `val(word outlen:int64) = outlen` and t2 = `~(outlen = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

let SQONCE_CS_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out:int64`; `outlen:num`; `st:int64`; `r:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`;
        `f_ev_loop:int64->num->int64->num->num->int64->int64->num->
                   (uarch_event)list`]);
      LABEL_TAC name safety_th]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The state is a 1600-bit word S, as in                  *)
(* common/fips202/fips202.ml. Byte i of the output is byte i MOD r of        *)
(* keccak_squeeze (i DIV r + 1) S, the state after i DIV r + 1               *)
(* permutations, and the final state is the one after (outlen + r - 1) DIV r *)
(* permutations. When S is the result of mlk_keccak_absorb_once, the output  *)
(* is the bytes of the sponge in common/fips202/fips202.ml (see              *)
(* KECCAK_SPONGE_SQUEEZE in common/fips202/properties/keccak_fips202.ml).    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out outlen st r (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        PAIRWISE nonoverlapping
         [(out,outlen); (st,200); (word_sub stackpointer (word 272),272)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out,outlen); (st,200); (word_sub stackpointer (word 272),272)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlk_keccak_squeeze_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; st; word r] s /\
                  read (memory :> wbytes st) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq
                     (\i. word_subword (keccak_squeeze (i DIV r + 1) S)
                                       (8 * (i MOD r),8):byte)
                     outlen) /\
                  read (memory :> wbytes st) s =
                  keccak_squeeze ((outlen + r - 1) DIV r) S)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen); memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out outlen st r pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       PAIRWISE nonoverlapping
        [out,outlen; st,200; word_sub stackpointer (word 272),272] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out,outlen; st,200; word_sub stackpointer (word 272),272]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlk_keccak_squeeze_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; word outlen; st; word r] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out outlen st r pc
                           (word_sub stackpointer (word 272)) returnaddress /\
                    memaccess_inbounds e2
                     [out,outlen; st,200; word_sub stackpointer (word 272),272;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,outlen; st,200;
                      word_sub stackpointer (word 272),272]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,outlen); memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlkem_keccakf1600_permute and mlkem_keccakf1600_extract_bytes.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out outlen st r (S:1600 word) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       PAIRWISE nonoverlapping
        [out,outlen; st,200; word_sub stackpointer (word 272),272] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out,outlen; st,200; word_sub stackpointer (word 272),272]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlk_keccak_squeeze_once) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; word outlen; st; word r] s /\
                 read (memory :> wbytes st) s = S /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,outlen)) s =
                 num_of_bytelist
                  (list_of_seq
                    (\i. word_subword (keccak_squeeze (i DIV r + 1) S)
                                      (8 * (i MOD r),8):byte)
                    outlen) /\
                 read (memory :> wbytes st) s =
                 keccak_squeeze ((outlen + r - 1) DIV r) S /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out outlen st r pc
                           (word_sub stackpointer (word 272)) returnaddress /\
                    memaccess_inbounds e2
                     [out,outlen; st,200; word_sub stackpointer (word 272),272;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,outlen; st,200;
                      word_sub stackpointer (word 272),272]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,outlen); memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
