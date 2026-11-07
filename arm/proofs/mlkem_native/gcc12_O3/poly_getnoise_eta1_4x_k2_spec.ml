(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four noise polynomials with eta = 3 from a seed and nonces.   *)
(* This is the code for mlkem512_poly_getnoise_eta1_4x from mlkem-native's   *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), which computes 192 bytes of SHAKE256 of the seed *)
(* and each of the four nonces into buffers on the stack with                *)
(* mlkem_shake256x4, applies mlkem_poly_cbd3 to them, skipping the fourth    *)
(* polynomial if its pointer is null, and zeroes the buffers, the first ones *)
(* with memset. It is verified in the whole image (see                       *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_shake256x4 and mlkem_poly_cbd3 in the image and assuming the        *)
(* contracts for memset and memcpy in utils/mlkem_native_libc.ml.            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/shake256x4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_cbd3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem512_poly_getnoise_eta1_4x:
        +0x0: sub     sp, sp, #0x480
        +0x4: stp     x19, x20, [sp, #16]
        +0x8: add     x20, sp, #0x7f
        +0xc: and     x20, x20, #0xffffffffffffffe0
       +0x10: stp     x21, x22, [sp, #32]
       +0x14: add     x10, x20, #0x340
       +0x18: add     x9, x20, #0x380
       +0x1c: stp     x23, x24, [sp, #48]
       +0x20: add     x19, x20, #0x300
       +0x24: mov     x22, x2
       +0x28: stp     x25, x26, [sp, #64]
       +0x2c: add     x8, x20, #0x3c0
       +0x30: add     x25, x20, #0x180
       +0x34: stp     x27, x30, [sp, #80]
       +0x38: add     x27, x20, #0x240
       +0x3c: mov     x21, x3
       +0x40: ldp     q0, q1, [x4]
       +0x44: mov     x3, x27
       +0x48: adrp    x4, <page>
       +0x4c: ldr     x4, [x4, #4088]  // got_stack_chk_guard
       +0x50: mov     x24, x0
       +0x54: mov     x23, x1
       +0x58: mov     x0, x20
       +0x5c: ldr     x2, [x4]
       +0x60: str     x2, [sp, #1144]
       +0x64: mov     x2, #0x0
       +0x68: stp     q0, q1, [x9]
       +0x6c: mov     x2, x25
       +0x70: stp     q0, q1, [x10]
       +0x74: mov     x4, #0xc0
       +0x78: add     x26, x20, x4
       +0x7c: strb    w5, [x19, #32]
       +0x80: mov     x5, x19
       +0x84: strb    w6, [x19, #96]
       +0x88: mov     x6, x10
       +0x8c: strb    w7, [x19, #160]
       +0x90: mov     x7, x9
       +0x94: mov     x9, #0x21
       +0x98: stp     x8, x9, [sp]
       +0x9c: ldrb    w9, [sp, #1152]
       +0xa0: stp     q0, q1, [x8]
       +0xa4: mov     x1, x26
       +0xa8: strb    w9, [x19, #224]
       +0xac: stp     q0, q1, [x19]
       +0xb0: bl      <mlkem_shake256x4>
       +0xb4: mov     x1, x20
       +0xb8: mov     x0, x24
       +0xbc: bl      <mlkem_poly_cbd3>
       +0xc0: mov     x1, x26
       +0xc4: mov     x0, x23
       +0xc8: bl      <mlkem_poly_cbd3>
       +0xcc: mov     x1, x25
       +0xd0: mov     x0, x22
       +0xd4: bl      <mlkem_poly_cbd3>
       +0xd8: cbz     x21, <mlkem512_poly_getnoise_eta1_4x+0xe8>
       +0xdc: mov     x1, x27
       +0xe0: mov     x0, x21
       +0xe4: bl      <mlkem_poly_cbd3>
       +0xe8: mov     x0, x20
       +0xec: mov     x2, #0x300
       +0xf0: mov     w1, #0x0
       +0xf4: bl      <memset@plt>
       +0xf8: movi    v0.4s, #0x0
       +0xfc: stp     q0, q0, [x19]
      +0x100: stp     q0, q0, [x19, #32]
      +0x104: stp     q0, q0, [x19, #64]
      +0x108: stp     q0, q0, [x19, #96]
      +0x10c: stp     q0, q0, [x19, #128]
      +0x110: stp     q0, q0, [x19, #160]
      +0x114: stp     q0, q0, [x19, #192]
      +0x118: stp     q0, q0, [x19, #224]
      +0x11c: adrp    x0, <page>
      +0x120: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x124: ldr     x2, [sp, #1144]
      +0x128: ldr     x1, [x0]
      +0x12c: subs    x2, x2, x1
      +0x130: mov     x1, #0x0
      +0x134: b.ne    <mlkem512_poly_getnoise_eta1_4x+0x154>
      +0x138: ldp     x19, x20, [sp, #16]
      +0x13c: ldp     x21, x22, [sp, #32]
      +0x140: ldp     x23, x24, [sp, #48]
      +0x144: ldp     x25, x26, [sp, #64]
      +0x148: ldp     x27, x30, [sp, #80]
      +0x14c: add     sp, sp, #0x480
      +0x150: ret
      +0x154: bl      <__stack_chk_fail@plt>

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem512_poly_getnoise_eta1_4x"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16: the four outputs of SHAKE256, of 192 bytes each, and then its four *)
(* inputs, the seed and a nonce, at intervals of 64 bytes. The seed is       *)
(* copied to the inputs as two 128-bit words.                                *)
(* ------------------------------------------------------------------------- *)

let GETNOISE4_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let GETNOISE4_ALIGNED_16_32 = assume_spec GETNOISE4_ALIGNED_16_32_STMT;;

let GETNOISE4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 1855)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 1824 else 1840))`;;

let GETNOISE4_BUFFER_ADDRESS = assume_spec GETNOISE4_BUFFER_ADDRESS_STMT;;

let GETNOISE4_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 1855))
             (word 18446744073709551584):int64 =
    word_add stackpointer
     (word(if aligned 32 stackpointer then 1824 else 1840))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC GETNOISE4_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(*** Offset k of the buffer, as normalized by the simulation ***)

let GETNOISE4_AT k =
  let off = `if aligned 32 (stackpointer:int64) then 1824 else 1840` in
  let t = if k = 0 then off
          else mk_binop `(+):num->num->num` off (mk_small_numeral k) in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,t));;

let GETNOISE4_READ_MEMORY_BYTES128_HALVES_STMT =
  `!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`;;

let GETNOISE4_READ_MEMORY_BYTES128_HALVES =
  assume_spec GETNOISE4_READ_MEMORY_BYTES128_HALVES_STMT;;

(*** The 33 bytes of one input to SHAKE256 from the seed and a nonce ***)

let GETNOISE4_BYTES_32_OF_HALVES_STMT =
  `!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`;;

let GETNOISE4_BYTES_32_OF_HALVES =
  assume_spec GETNOISE4_BYTES_32_OF_HALVES_STMT;;

let GETNOISE4_INPUT_STMT =
  `!a:int64 (sd:byte list) b s:armstate.
        LENGTH sd = 32 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist sd MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist sd DIV 2 EXP 128) /\
        read (memory :> bytes8(word_add a (word 32))) s = b
        ==> LENGTH(APPEND sd [b]) = 33 /\
            read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND sd [b])`;;

let GETNOISE4_INPUT = assume_spec GETNOISE4_INPUT_STMT;;

(*** Offsets in the buffers as single numbers ***)

let GETNOISE4_ADDRESS_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let GETNOISE4_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE GETNOISE4_ADDRESS_CONV th else th);;

(*** The input k in the buffer, at state s44, with the nonce byte b ***)

let GETNOISE4_INPUT_TAC =
  let th = CONV_RULE NUM_REDUCE_CONV GETNOISE4_INPUT in
  fun k b ->
    let a = GETNOISE4_AT (768 + 64 * k) in
    MP_TAC(SPECL [a; `sd:byte list`; b; `s44:armstate`] th) THEN
    ANTS_TAC THENL
     [CONV_TAC GETNOISE4_ADDRESS_CONV THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_BLAST;
      STRIP_TAC];;

(*** The GOT entries in the form in the precondition of the callee ***)

let GETNOISE4_GOT_TAC =
  MAP_EVERY (fun t ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] t) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [`read (memory :> bytes64
           (word_add (word pc) (word got_stack_chk_guard))) s =
     g:int64`;
    `read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
     g:int64`;
    `read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
     g:int64`];;

(*** The test of whether the fourth pointer is null ***)

let GETNOISE4_BRANCH_TAC tm =
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && is_cond(rand(concl th))
    then REWRITE_RULE[VAL_EQ_0; ASSUME tm] th else th);;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let GETNOISE4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2880):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `1824 <= (if aligned 32 (stackpointer:int64) then 1824 else 1840) /\
    (if aligned 32 (stackpointer:int64) then 1824 else 1840) <= 1840`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--27);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy as for    *)
(* mlkem_shake256x4. The seed is 32 bytes at seed, given as a list of bytes  *)
(* sd, and the nonces are the low bytes of the sixth to eighth arguments and *)
(* of the ninth, on the stack. For each polynomial, as for                   *)
(* mlkem512_poly_getnoise_eta2 but with eta = 3, the result is               *)
(* mlkem_poly_cbd3 applied to the first 192 bytes of shake256 of the seed    *)
(* followed by the nonce, except that if the fourth pointer is null there is *)
(* no fourth result. The stack is the 1152 bytes of the function and the     *)
(* 1728 used by mlkem_shake256x4 below them.                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_SHAKE256X4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_CBD3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let GETNOISE4_N nonce =
  vsubst [nonce,`nonce:int64`]
   `num_of_bytelist(list_of_seq
     (shake256(APPEND (sd:byte list) [word_zx(nonce:int64)])) 192)`;;

(*** Up to the test of the fourth pointer: the inputs, SHAKE256, cbd3 ***)

let GETNOISE4_START_TAC =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GETNOISE4_READ_MEMORY_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC (1--4) THEN
  GETNOISE4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (5--19) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (20--44) THEN
  GETNOISE4_NORMALIZE_TAC THEN
  GETNOISE4_INPUT_TAC 0 `word_zx(nonce0:int64):byte` THEN
  GETNOISE4_INPUT_TAC 1 `word_zx(nonce1:int64):byte` THEN
  GETNOISE4_INPUT_TAC 2 `word_zx(nonce2:int64):byte` THEN
  GETNOISE4_INPUT_TAC 3 `word_zx(nonce3:int64):byte` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (45--45) THEN
  GETNOISE4_GOT_TAC THEN
  LOCAL_SHAKE256X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `192`;
    `read X5 s`; `read X6 s`; `read X7 s`;
    `word_add (stackpointer:int64)
      (word((if aligned 32 stackpointer then 1824 else 1840) + 960))`;
    `33`; `APPEND (sd:byte list) [word_zx(nonce0:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce1:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce2:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce3:int64)]`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 46 THEN
  MAP_EVERY (fun (k,nonce) ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
     ((k-3)--(k-1)) THEN
    LOCAL_CBD3_TAC [`read X0 s`; `read X1 s`; GETNOISE4_N nonce;
                    `pc:num`; `read SP s`; `read X30 s`] k)
   [50,`nonce0:int64`; 54,`nonce1:int64`; 58,`nonce2:int64`] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC (59--59);;

(*** From step k: zeroing the buffers, the stack guard, the return ***)

let GETNOISE4_END_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (k--(k+3)) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC (k+3) THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (k+8) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   ((k+9)--(k+18)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   ((k+19)--(k+31)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r0 r1 r2 r3 seed (sd:byte list) nonce0 nonce1 nonce2 nonce3
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2880),2880)] /\
        ALLPAIRS nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2880),2880)]
         [(seed,32); (stackpointer,1); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem512_poly_getnoise_eta1_4x) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                   [r0; r1; r2; r3; seed; nonce0; nonce1; nonce2] s /\
                  read (memory :> bytes8 stackpointer) s =
                  word_zx(nonce3:int64) /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist sd)
             (\s. read PC s = returnaddress /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce0])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r0 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce1])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r1 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce2])) 192) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r2 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                 &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                   (n DIV 2 EXP (6 * i + 5)) MOD 2))) /\
                  (~(r3 = word 0) ==>
                   (let n = num_of_bytelist
                            (list_of_seq
                              (shake256 (APPEND sd [word_zx nonce3])) 192) in
                    !i. i < 256
                        ==> read(memory :> bytes16(word_add r3 (word(2 * i))))
                                 s =
                            iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                  &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                    (n DIV 2 EXP (6 * i + 5)) MOD 2)))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                memory :> bytes(word_sub stackpointer (word 2880),2880)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contracts for memset and memcpy. The events do not depend on the seed or  *)
(* the nonces, but on whether the fourth pointer is null.                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let GETNOISE4_ALLOWED =
  [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let GETNOISE4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GETNOISE4_ALLOWED); LABEL_TAC name safety_th]);;

(*** Up to the test of the fourth pointer ***)

let GETNOISE4_SAFE_START_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC (1--4) THEN
  GETNOISE4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (5--19) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (20--44) THEN
  GETNOISE4_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (45--45) THEN
  GETNOISE4_GOT_TAC THEN
  GETNOISE4_SAFE_CALL_TAC "H_SHAKE256X4"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `192`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word_add (stackpointer:int64)
      (word((if aligned 32 stackpointer then 1824 else 1840) + 960))`;
    `33`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 46 THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
     ((k-3)--(k-1)) THEN
    GETNOISE4_SAFE_CALL_TAC "H_CBD3"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
      `read SP s`; `read X30 s`] k)
   [50; 54; 58] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC (59--59);;

(*** From step k ***)

let GETNOISE4_SAFE_END_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   (k--(k+3)) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC (k+3) THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET"
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref GETNOISE4_ALLOWED) (k+8) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   ((k+9)--(k+18)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_EXEC
   ((k+19)--(k+31)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2880),2880] /\
           ALLPAIRS nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2880),2880]
            [seed,32; stackpointer,1; word pc,libmlkem_size;
             word(pc + got_stack_chk_guard),8;
             guard,8; word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O3_mc /\
                     read PC s = word (pc + mlkem512_poly_getnoise_eta1_4x) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [r0; r1; r2; r3; seed] s /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events r0 r1 r2 r3 seed guard mf mc pc
                               (word_sub stackpointer (word 2880))
                               returnaddress /\
                        memaccess_inbounds e2
                         [seed,32; stackpointer,1; r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2880),2880;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + mlkem_poly_cbd3_consts),16;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          ea,el]
                         [r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2880),2880]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(r0,512); memory :> bytes(r1,512);
                   memory :> bytes(r2,512);
                   memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                   memory :> bytes(word_sub stackpointer (word 2880),2880)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
