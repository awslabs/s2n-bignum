(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hash check of an ML-KEM-1024 decapsulation key. This is the code for  *)
(* mlkem1024_check_sk from mlkem-native's portable C implementation compiled *)
(* by clang 17 with -O3 (see mlkem_native/README.md), which computes the     *)
(* SHA3-256 hash of the encapsulation key in the decapsulation key into a    *)
(* buffer on the stack, compares it in constant time with the hash stored in *)
(* the decapsulation key, and zeroes the buffer. The specifications are      *)
(* those of gcc12_O2, except for the stack: the function saves its           *)
(* registers, aligns the buffer to 32 bytes below them, and the frame also   *)
(* includes the 528 bytes of mlkem_sha3_256 below the buffer. It is verified *)
(* in the whole image (see libmlkem.ml), using the theorems for              *)
(* mlkem_sha3_256 in the image.                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/sha3_256_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_check_sk:
       +0x0: stp     x29, x30, [sp, #-32]!
       +0x4: stp     x20, x19, [sp, #16]
       +0x8: mov     x29, sp
       +0xc: sub     x9, sp, #0x40
      +0x10: and     sp, x9, #0xffffffffffffffe0
      +0x14: adrp    x8, <page>
      +0x18: mov     x19, x0
      +0x1c: add     x1, x0, #0x600
      +0x20: mov     x0, sp
      +0x24: mov     w2, #0x620
      +0x28: mov     x20, sp
      +0x2c: ldr     x8, [x8, #4088]
      +0x30: ldr     x8, [x8]
      +0x34: str     x8, [sp, #56]
      +0x38: bl      <mlkem_sha3_256>
      +0x3c: ldp     q1, q2, [sp]
      +0x40: mov     w8, wzr
      +0x44: ldr     q0, [x19, #3120]
      +0x48: ldr     q3, [x19, #3104]
      +0x4c: eor     v0.16b, v2.16b, v0.16b
      +0x50: eor     v1.16b, v1.16b, v3.16b
      +0x54: orr     v2.16b, v1.16b, v0.16b
      +0x58: ext     v3.16b, v2.16b, v2.16b, #8
      +0x5c: eor     v0.16b, v1.16b, v0.16b
      +0x60: ext     v1.16b, v0.16b, v0.16b, #8
      +0x64: orr     v2.8b, v2.8b, v3.8b
      +0x68: fmov    x9, d2
      +0x6c: eor     v0.8b, v0.8b, v1.8b
      +0x70: fmov    x11, d0
      +0x74: orr     x9, x9, x9, lsr #32
      +0x78: lsr     x10, x9, #16
      +0x7c: orr     w9, w9, w10
      +0x80: eor     x10, x11, x11, lsr #32
      +0x84: movi    v0.2d, #0x0
      +0x88: orr     w9, w9, w9, lsr #8
      +0x8c: eor     x10, x10, x10, lsr #16
      +0x90: sub     w9, w8, w9, uxtb
      +0x94: lsr     x11, x10, #8
      +0x98: eor     w10, w10, w11
      +0x9c: eor     w9, w10, w9, lsr #16
      +0xa0: adrp    x11, <page>
      +0xa4: stp     q0, q0, [sp]
      +0xa8: and     w9, w9, #0xff
      +0xac: ldr     x11, [x11, #4088]
      +0xb0: cmp     w9, w10, uxtb
      +0xb4: ldr     x12, [sp, #56]
      +0xb8: mov     w9, #0xfffffffb
      +0xbc: csel    w0, w8, w9, eq
      +0xc0: ldr     x11, [x11]
      +0xc4: cmp     x11, x12
      +0xc8: b.ne    <mlkem1024_check_sk+0xdc>
      +0xcc: mov     sp, x29
      +0xd0: ldp     x20, x19, [sp, #16]
      +0xd4: ldp     x29, x30, [sp], #32
      +0xd8: ret
      +0xdc: bl      <stack_chk_fail>
 ***)

let MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem1024_check_sk"];;

(* ------------------------------------------------------------------------- *)
(* The buffer for the hash is aligned to 32 bytes within the stack frame, so *)
(* its address depends on whether the stack pointer is a multiple of 32 or   *)
(* just of 16, and it is loaded as two 128-bit words, as is the stored hash. *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let CHECK_SK_ALIGNED_16_32 = assume_spec CHECK_SK_ALIGNED_16_32_STMT;;

let CHECK_SK_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 544)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 544 else 528))`;;

let CHECK_SK_BUFFER_ADDRESS = assume_spec CHECK_SK_BUFFER_ADDRESS_STMT;;

let CHECK_SK_BUFFER = `word_add (stackpointer:int64)
                        (word(if aligned 32 stackpointer then 544 else 528))`;;

let CHECK_SK_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 544))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 544 else 528))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CHECK_SK_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let READ_MEMORY_BYTES128_HALVES_STMT =
  `!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`;;

let READ_MEMORY_BYTES128_HALVES =
  assume_spec READ_MEMORY_BYTES128_HALVES_STMT;;

(* ------------------------------------------------------------------------- *)
(* The comparison of the two hashes, as two 128-bit words each, which ORs    *)
(* together the bytes of their XOR (also XORing them, which does not affect  *)
(* the result), and the result of the function from it.                      *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_EQ_STMT =
  `!h n. h < 2 EXP 256 /\ n < 2 EXP 256
         ==> (h = n <=>
              word(n MOD 2 EXP 128):int128 = word(h MOD 2 EXP 128) /\
              word(n DIV 2 EXP 128):int128 = word(h DIV 2 EXP 128))`;;

let CHECK_SK_EQ = assume_spec CHECK_SK_EQ_STMT;;

let READ_MEMORY_BYTES_32_BOUND_STMT =
  `!a n s:armstate.
        read (memory :> bytes(a,32)) s = n ==> n < 2 EXP 256`;;

let READ_MEMORY_BYTES_32_BOUND = assume_spec READ_MEMORY_BYTES_32_BOUND_STMT;;

let CHECK_SK_RESULT_STMT =
  `!c c'. (c <=> c')
          ==> word_zx (if c then word 0 else word 4294967291:int32):int64 =
              (if c' then word 0 else word 4294967291)`;;

let CHECK_SK_RESULT = assume_spec CHECK_SK_RESULT_STMT;;

(*** The comparison, with the four 128-bit words as hl, hh, nl and nh ***)

let CHECK_SK_EXPAND_TAC v =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Const("word",_),_)),r) when r = v ->
        SUBST1_TAC(SYM th)
    | _ -> NO_TAC);;

let CHECK_SK_COMPARE_TAC =
  MATCH_MP_TAC CHECK_SK_RESULT THEN
  SUBGOAL_THEN
   `h = num_of_bytelist(sha3_256 ek) <=>
    (nl:int128) = hl /\ (nh:int128) = hh`
  SUBST1_TAC THENL
   [MAP_EVERY CHECK_SK_EXPAND_TAC
     [`nl:int128`; `nh:int128`; `hl:int128`; `hh:int128`] THEN
    MATCH_MP_TAC CHECK_SK_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((nl:int128) = hl /\ (nh:int128) = hh) <=>
    (word_xor hl nl = word 0 /\ word_xor hh nh = word 0)`
  SUBST1_TAC THENL [REWRITE_TAC[WORD_XOR_EQ_0] THEN MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`word_xor hh nh:int128`,`y:int128`) THEN
  SPEC_TAC(`word_xor hl nl:int128`,`x:int128`) THEN REPEAT GEN_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The decapsulation key of 3168 bytes at sk contains the *)
(* encapsulation key of 1568 bytes at offset 1536, given as a list of bytes  *)
(* ek, and its hash h at offset 3104, as a number. The result is 0 if h is   *)
(* the SHA3-256 hash of ek, as in common/fips202/fips202.ml, and -5          *)
(* otherwise. The stack guard is handled as for mlkem_sha3_256, and the      *)
(* stack is the 112 bytes of the function, with the buffer aligned within    *)
(* them, and the 528 used by mlkem_sha3_256 below them.                      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHA3_256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let CHECK_SK_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 640):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `528 <= (if aligned 32 (stackpointer:int64) then 544 else 528) /\
    (if aligned 32 (stackpointer:int64) then 544 else 528) <= 544`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `aligned 16 (word_add (stackpointer:int64)
                         (word(if aligned 32 stackpointer then 544 else 528)))`
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_sub (word (if aligned 32 (stackpointer:int64) then 544 else 528))
             (word 528):int64 =
    word((if aligned 32 stackpointer then 544 else 528) - 528)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_SUB2 THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(if aligned 32 (stackpointer:int64) then 544 else 528) - 528 <= 16`
  ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The GOT entry in the form in the precondition of mlkem_sha3_256 ***)

let CHECK_SK_GOT_TAC =
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
        `read (memory :> bytes64 (word_add (word pc) (word n))) s = g`)
        (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

(*** The region below the buffer for the callee, in the form word(x - 528) ***)

let CHECK_SK_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE[ASSUME
     `word_sub (word (if aligned 32 (stackpointer:int64) then 544 else 528))
               (word 528):int64 =
      word((if aligned 32 stackpointer then 544 else 528) - 528)`] th
    else th);;

(*** A 32-byte value as two 128-bit words, named by l and h ***)

let CHECK_SK_HALVES_TAC a v l h =
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; v,`v:num`]
             `read (memory :> bytes(a,32)) s = v`)) (concl th)
    then ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES_32_BOUND th) THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV(REWRITE_CONV
                  [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                  DEPTH_CONV NUM_ADD_CONV))
                  (MATCH_MP READ_MEMORY_BYTES128_HALVES th)) THEN
         ABBREV_TAC(mk_eq(mk_var(l,`:int128`),
                    mk_comb(`word:num->int128`,
                     mk_binop `MOD` v `2 EXP 128`))) THEN
         ABBREV_TAC(mk_eq(mk_var(h,`:int128`),
                    mk_comb(`word:num->int128`,
                     mk_binop `DIV` v `2 EXP 128`))) THEN
         STRIP_TAC
    else NO_TAC);;

let MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!sk (ek:byte list) h guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1568 /\
        nonoverlapping (sk,3168) (word_sub stackpointer (word 640),640) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 640),640)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem1024_check_sk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(word_add sk (word 1536),1568)) s =
                  num_of_bytelist ek /\
                  read (memory :> bytes(word_add sk (word 3104),32)) s = h)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if h = num_of_bytelist(sha3_256 ek) then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 640),640)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlkem_sha3_256, it is       *)
(* stated directly, since the events depend on the address of the stack      *)
(* guard, read from the GOT. They do not depend on the keys.                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e sk guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (sk,3168) (word_sub stackpointer (word 640),640) /\
       ALLPAIRS nonoverlapping
        [word_sub stackpointer (word 640),640]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem1024_check_sk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk guard pc
                           (word_sub stackpointer (word 640)) returnaddress /\
                    memaccess_inbounds e2
                     [word_add sk (word 1536),1568;
                      word_add sk (word 3104),32;
                      word_sub stackpointer (word 640),640;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [word_sub stackpointer (word 640),640]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 640),640)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using the    *)
(* combined theorem for mlkem_sha3_256, for the decapsulation, which         *)
(* branches on the result.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e sk (ek:byte list) h guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH ek = 1568 /\
       nonoverlapping (sk,3168) (word_sub stackpointer (word 640),640) /\
       ALLPAIRS nonoverlapping
        [word_sub stackpointer (word 640),640]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem1024_check_sk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(word_add sk (word 1536),1568)) s =
                 num_of_bytelist ek /\
                 read (memory :> bytes(word_add sk (word 3104),32)) s = h /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 C_RETURN s =
                 (if h = num_of_bytelist(sha3_256 ek) then word 0
                  else word 0xfffffffb) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk guard pc
                           (word_sub stackpointer (word 640)) returnaddress /\
                    memaccess_inbounds e2
                     [word_add sk (word 1536),1568;
                      word_add sk (word 3104),32;
                      word_sub stackpointer (word 640),640;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [word_sub stackpointer (word 640),640]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 640),640)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_SK_K4_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
