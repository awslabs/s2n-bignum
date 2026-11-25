(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::WorkingMemory::RequiredSize(size_t input_size), the     *)
(* size of the scratch memory of the compressor for an input of n bytes:     *)
(* snappy_working_memory_size n (common/snappy/snappy_working_memory.ml),    *)
(* i.e. 2 * CalculateTableSize(m) + m + MaxCompressedLength(m) for          *)
(* m = min(n, kBlockSize). gcc 12 -O2 inlines CalculateTableSize (the        *)
(* Log2Floor by clz) and calls MaxCompressedLength, so this is proved        *)
(* relative to its contract. The function saves X19, X20, X29 and X30 in a  *)
(* frame of 32 bytes below SP.                                               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/max_compressed_length_spec.ml";;
needs "common/snappy/snappy_working_memory.ml";;
needs "arm/proofs/utils/compare_branch.ml";;

(*** The code in the image (see the listing in layout.ml):

    WorkingMemory_RequiredSize:
     +0x0  stp     x29, x30, [sp, #-32]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  cmp     x0, #0x10, lsl #12        n > 65536
    +0x10  b.hi    +0x60
    +0x14  mov     x19, x0
    +0x18  cmp     x0, #0x8, lsl #12         n > 32768
    +0x1c  b.hi    +0x84
    +0x20  sub     w0, w0, #0x1
    +0x24  mov     w20, #0x2
    +0x28  clz     w0, w0
    +0x2c  cmp     w19, #0xff
    +0x30  eor     w0, w0, #0x1f             Log2Floor(n - 1)
    +0x34  mov     x1, #0x200
    +0x38  lsl     w20, w20, w0
    +0x3c  lsl     x20, x20, #1
    +0x40  csel    x20, x20, x1, hi          n > 255 ? 2 * table : 2 * 256
  join1:
    +0x44  mov     x0, x19
    +0x48  add     x19, x19, x20
    +0x4c  bl      MaxCompressedLength
    +0x50  add     x0, x19, x0
    +0x54  ldp     x19, x20, [sp, #16]
    +0x58  ldp     x29, x30, [sp], #32
    +0x5c  ret
    +0x60  mov     x20, #0x10000             (n > 65536: m = 65536)
    +0x64  mov     x19, x20
    +0x68  mov     x0, x19
    +0x6c  add     x19, x19, x20
    +0x70  bl      MaxCompressedLength
    +0x74  add     x0, x19, x0
    +0x78  ldp     x19, x20, [sp, #16]
    +0x7c  ldp     x29, x30, [sp], #32
    +0x80  ret
    +0x84  mov     x20, #0x10000             (32768 < n <= 65536)
    +0x88  b       join1
 ***)

(* ------------------------------------------------------------------------- *)
(* The bytes of the hash table as the code computes them for 255 < n <=      *)
(* 32768 (also in WorkingMemory(size_t, char* ) and GetHashTable): 2 << (31 *)
(* - clz(n - 1)), in 32 bits, then doubled in 64 bits.                       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_TABLE_SIZE_CLZ = prove
 (`!n. 255 < n /\ n <= 32768
       ==> word_jshl (word 2:int32)
             (word_xor (word (word_clz (word_sub (word n:int32) (word 1))))
                       (word 31)) =
           word(snappy_table_size n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word n) (word 1):int32 = word(n - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `255 < n ==> 1 <= n`]; ALL_TAC] THEN
  SUBGOAL_THEN `?k. 7 <= k /\ k <= 14 /\ 2 EXP k < n /\ n <= 2 EXP (k + 1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun k -> ASM_CASES_TAC (mk_binary "<=" (`n:num`,
                    mk_small_numeral (1 lsl (k + 1)))) THENL
                  [EXISTS_TAC (mk_small_numeral k) THEN
                   CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC])
     [7;8;9;10;11;12;13] THEN
    EXISTS_TAC `14` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `k:num`] SNAPPY_TABLE_SIZE_LOG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `word_clz (word(n - 1):int32) = 31 - k` SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_CLZ_UNIQUE_VAL THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `32 - (31 - k) - 1 = k` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(n - 1):int32) = n - 1` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `n - 1 - 2 EXP k` THEN
    UNDISCH_TAC `n <= 2 EXP (k + 1)` THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `7 <= k` THEN UNDISCH_TAC `k <= 14` THEN
  SPEC_TAC(`k:num`,`k:num`) THEN
  REWRITE_TAC[IMP_IMP; ARITH_RULE
   `k <= 14 /\ 7 <= k <=>
    k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/
    k = 14`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SNAPPY_TABLE_BYTES_CLZ = prove
 (`!n. 255 < n /\ n <= 32768
       ==> (word_shl
             (word_zx
               (word_jshl (word 2:int32)
                  (word_xor (word (word_clz (word_sub (word n:int32) (word 1))))
                            (word 31))):int64) 1 =
            word(2 * snappy_table_size n))`,
  SIMP_TAC[SNAPPY_TABLE_SIZE_CLZ] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` SNAPPY_TABLE_SIZE_BOUNDS) THEN
  SPEC_TAC(`snappy_table_size n`,`h:num`) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_zx; word_shl; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `h <= 32768 ==> h < 4294967296`;
               ARITH_RULE `h <= 32768 ==> h < 18446744073709551616`] THEN
  ARITH_TAC);;

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "WorkingMemory_RequiredSize"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The saved registers are ghosts restored at the return.       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!n pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        nonoverlapping (word pc,libsnappy_size) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_RequiredSize) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [n] s)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = word(snappy_working_memory_size (val n)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety: the accesses are the frame on the stack.   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!e n pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        nonoverlapping (word pc,libsnappy_size) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_RequiredSize) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [n] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = word(snappy_working_memory_size (val n)) /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(word_sub sp (word 32),32))
                        (memrange(word_sub sp (word 32),32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
    SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
