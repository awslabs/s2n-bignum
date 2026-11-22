(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four noise polynomials with eta = 2 from a seed and nonces.   *)
(* This is the code for mlkem768_poly_getnoise_eta1_4x from mlkem-native's   *)
(* portable C implementation compiled by clang 17 with -O2 (see              *)
(* mlkem_native/README.md), which computes 128 bytes of SHAKE256 of the seed *)
(* and each of the four nonces into buffers on the stack with                *)
(* mlkem_shake256x4, applies mlkem_poly_cbd2 to them, skipping the fourth    *)
(* polynomial if its pointer is null, and zeroes the buffers with inline     *)
(* stores. It is verified in the whole image (see libmlkem.ml), using the    *)
(* theorems for mlkem_shake256x4 and mlkem_poly_cbd2 in the image and        *)
(* assuming the contracts for memset and memcpy in                           *)
(* utils/mlkem_native_libc.ml, which mlkem_shake256x4 needs.                 *)
(*                                                                           *)
(* The buffers are aligned to 32 bytes within the stack frame, which the     *)
(* code makes by rounding the stack pointer down, so the proof is by cases   *)
(* on whether the incoming stack pointer is a multiple of 32.                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/shake256x4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_cbd2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem768_poly_getnoise_eta1_4x:
       +0x0: stp     x29, x30, [sp, #-80]!
       +0x4: stp     x28, x25, [sp, #16]
       +0x8: stp     x24, x23, [sp, #32]
       +0xc: stp     x22, x21, [sp, #48]
      +0x10: stp     x20, x19, [sp, #64]
      +0x14: mov     x29, sp
      +0x18: sub     x9, sp, #0x330
      +0x1c: and     sp, x9, #0xffffffffffffffe0
      +0x20: adrp    x8, <page>
      +0x24: ldrb    w10, [x29, #80]
      +0x28: add     x11, sp, #0x20
      +0x2c: add     x12, sp, #0x120
      +0x30: add     x9, x11, #0x80
      +0x34: add     x24, x12, #0x80
      +0x38: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x3c: add     x25, x12, #0x100
      +0x40: add     x20, x12, #0x180
      +0x44: mov     x19, x3
      +0x48: mov     x21, x2
      +0x4c: mov     x22, x1
      +0x50: ldr     x8, [x8]
      +0x54: mov     x23, x0
      +0x58: add     x0, sp, #0x120
      +0x5c: mov     x1, x24
      +0x60: mov     x2, x25
      +0x64: mov     x3, x20
      +0x68: str     x8, [sp, #808]
      +0x6c: add     x8, x11, #0x40
      +0x70: ldp     q0, q1, [x4]
      +0x74: strb    w5, [sp, #64]
      +0x78: add     x11, x11, #0xc0
      +0x7c: strb    w6, [sp, #128]
      +0x80: add     x5, sp, #0x20
      +0x84: strb    w7, [sp, #192]
      +0x88: mov     w4, #0x80
      +0x8c: strb    w10, [sp, #256]
      +0x90: mov     w10, #0x21
      +0x94: mov     x6, x8
      +0x98: mov     x7, x9
      +0x9c: stp     q0, q1, [sp, #32]
      +0xa0: str     q0, [sp, #96]
      +0xa4: str     q1, [sp, #112]
      +0xa8: stp     q0, q1, [sp, #160]
      +0xac: stp     q0, q1, [sp, #224]
      +0xb0: stp     x11, x10, [sp]
      +0xb4: bl      <mlkem_shake256x4>
      +0xb8: add     x1, sp, #0x120
      +0xbc: mov     x0, x23
      +0xc0: bl      <mlkem_poly_cbd2>
      +0xc4: mov     x0, x22
      +0xc8: mov     x1, x24
      +0xcc: bl      <mlkem_poly_cbd2>
      +0xd0: mov     x0, x21
      +0xd4: mov     x1, x25
      +0xd8: bl      <mlkem_poly_cbd2>
      +0xdc: cbz     x19, <mlkem768_poly_getnoise_eta1_4x+0xec>
      +0xe0: mov     x0, x19
      +0xe4: mov     x1, x20
      +0xe8: bl      <mlkem_poly_cbd2>
      +0xec: movi    v0.2d, #0x0
      +0xf0: add     x8, sp, #0x120
      +0xf4: stp     q0, q0, [sp, #288]
      +0xf8: stp     q0, q0, [sp, #320]
      +0xfc: stp     q0, q0, [sp, #352]
     +0x100: stp     q0, q0, [sp, #384]
     +0x104: stp     q0, q0, [sp, #416]
     +0x108: stp     q0, q0, [sp, #448]
     +0x10c: stp     q0, q0, [sp, #480]
     +0x110: stp     q0, q0, [sp, #512]
     +0x114: stp     q0, q0, [sp, #544]
     +0x118: stp     q0, q0, [sp, #576]
     +0x11c: stp     q0, q0, [sp, #608]
     +0x120: stp     q0, q0, [sp, #640]
     +0x124: stp     q0, q0, [sp, #672]
     +0x128: stp     q0, q0, [sp, #704]
     +0x12c: stp     q0, q0, [sp, #736]
     +0x130: stp     q0, q0, [sp, #768]
     +0x134: stp     q0, q0, [sp, #64]
     +0x138: stp     q0, q0, [sp, #96]
     +0x13c: add     x8, sp, #0x20
     +0x140: stp     q0, q0, [sp, #32]
     +0x144: stp     q0, q0, [sp, #128]
     +0x148: stp     q0, q0, [sp, #160]
     +0x14c: stp     q0, q0, [sp, #192]
     +0x150: stp     q0, q0, [sp, #224]
     +0x154: stp     q0, q0, [sp, #256]
     +0x158: adrp    x8, <page>
     +0x15c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x160: ldr     x9, [sp, #808]
     +0x164: ldr     x8, [x8]
     +0x168: cmp     x8, x9
     +0x16c: b.ne    <mlkem768_poly_getnoise_eta1_4x+0x18c>
     +0x170: mov     sp, x29
     +0x174: ldp     x20, x19, [sp, #64]
     +0x178: ldp     x22, x21, [sp, #48]
     +0x17c: ldp     x24, x23, [sp, #32]
     +0x180: ldp     x28, x25, [sp, #16]
     +0x184: ldp     x29, x30, [sp], #80
     +0x188: ret
     +0x18c: bl      __stack_chk_fail
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem768_poly_getnoise_eta1_4x"];;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. Above the two stack arguments of mlkem_shake256x4 (the pointer to  *)
(* the fourth input and the input length) are its four inputs, the seed and  *)
(* a nonce, at intervals of 64 bytes, and then the four outputs of SHAKE256, *)
(* of 128 bytes each. The seed is copied to the inputs as two 128-bit        *)
(* words.                                                                    *)
(* ------------------------------------------------------------------------- *)

let GETNOISE4_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let GETNOISE4_ALIGNED_16_32 = assume_spec GETNOISE4_ALIGNED_16_32_STMT;;

let GETNOISE4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 1888)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 1888 else 1872))`;;

let GETNOISE4_BUFFER_ADDRESS = assume_spec GETNOISE4_BUFFER_ADDRESS_STMT;;

let GETNOISE4_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 1888))
             (word 18446744073709551584):int64 =
    word_add stackpointer
     (word(if aligned 32 stackpointer then 1888 else 1872))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC GETNOISE4_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(*** Offset k of the buffer, as normalized by the simulation ***)

let GETNOISE4_AT k =
  let off = `if aligned 32 (stackpointer:int64) then 1888 else 1872` in
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
    let a = GETNOISE4_AT (32 + 64 * k) in
    MP_TAC(SPECL [a; `sd:byte list`; b; `s45:armstate`] th) THEN
    ANTS_TAC THENL
     [CONV_TAC GETNOISE4_ADDRESS_CONV THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_BLAST;
      STRIP_TAC];;

(*** The GOT entries in the form in the precondition of the callee ***)

let GETNOISE4_GOT_TAC =
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
        `read (memory :> bytes64 (word_add (word pc) (word n))) s = g`)
        (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

(*** The test of whether the fourth pointer is null ***)

let GETNOISE4_BRANCH_TAC tm =
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && is_cond(rand(concl th))
    then REWRITE_RULE[VAL_EQ_0; ASSUME tm] th else th);;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let GETNOISE4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2784):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `1872 <= (if aligned 32 (stackpointer:int64) then 1888 else 1872) /\
    (if aligned 32 (stackpointer:int64) then 1888 else 1872) <= 1888`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `aligned 16 (word_add (stackpointer:int64)
                 (word(if aligned 32 stackpointer then 1888 else 1872)))`
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_sub (word (if aligned 32 (stackpointer:int64) then 1888 else 1872))
             (word 1872):int64 =
    word((if aligned 32 stackpointer then 1888 else 1872) - 1872)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_SUB2 THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
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
     (mk_const(r,[]))) (19--25) THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The region below the buffers for the callee, in the form word(x - 1872) ***)

let GETNOISE4_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE[ASSUME
     `word_sub (word (if aligned 32 (stackpointer:int64) then 1888 else 1872))
               (word 1872):int64 =
      word((if aligned 32 stackpointer then 1888 else 1872) - 1872)`] th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy as for    *)
(* mlkem_shake256x4. The seed is 32 bytes at seed, given as a list of bytes  *)
(* sd, and the nonces are the low bytes of the sixth to eighth arguments and *)
(* of the ninth, on the stack. For each polynomial, as for                   *)
(* mlkem512_poly_getnoise_eta2 but with eta = 2, the result is               *)
(* mlkem_poly_cbd2 applied to the first 128 bytes of shake256 of the seed    *)
(* followed by the nonce, except that if the fourth pointer is null there is *)
(* no fourth result. The stack is the 80 bytes of saved registers, 816       *)
(* bytes of the buffers and the canary, up to 16 bytes of padding for the    *)
(* alignment, and the 1872 used by mlkem_shake256x4 below them.              *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHAKE256X4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD2_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_CBD2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let GETNOISE4_N nonce =
  vsubst [nonce,`nonce:int64`]
   `num_of_bytelist(list_of_seq
     (shake256(APPEND (sd:byte list) [word_zx(nonce:int64)])) 128)`;;

(*** Up to the test of the fourth pointer: the inputs, SHAKE256, cbd2 ***)

let GETNOISE4_START_TAC =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GETNOISE4_READ_MEMORY_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC (1--8) THEN
  GETNOISE4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (9--9) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (10--45) THEN
  GETNOISE4_NORMALIZE_TAC THEN
  GETNOISE4_INPUT_TAC 0 `word_zx(nonce0:int64):byte` THEN
  GETNOISE4_INPUT_TAC 1 `word_zx(nonce1:int64):byte` THEN
  GETNOISE4_INPUT_TAC 2 `word_zx(nonce2:int64):byte` THEN
  GETNOISE4_INPUT_TAC 3 `word_zx(nonce3:int64):byte` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (46--46) THEN
  GETNOISE4_GOT_TAC THEN
  LOCAL_SHAKE256X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `128`;
    `read X5 s`; `read X6 s`; `read X7 s`;
    `word_add (stackpointer:int64)
      (word((if aligned 32 stackpointer then 1888 else 1872) + 224))`;
    `33`; `APPEND (sd:byte list) [word_zx(nonce0:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce1:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce2:int64)]`;
    `APPEND (sd:byte list) [word_zx(nonce3:int64)]`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 47 THEN
  GETNOISE4_FIX_TAC THEN
  MAP_EVERY (fun (k,nonce) ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
     ((k-3)--(k-1)) THEN
    GETNOISE4_NORMALIZE_TAC THEN
    LOCAL_CBD2_TAC [`read X0 s`; `read X1 s`; GETNOISE4_N nonce;
                    `pc:num`; `read X30 s`] k)
   [51,`nonce0:int64`; 55,`nonce1:int64`; 59,`nonce2:int64`] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC (60--60);;

(*** From step k: zeroing the buffers, the stack guard, the return ***)

let GETNOISE4_END_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (k--(k+27)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   ((k+28)--(k+39)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r0 r1 r2 r3 seed (sd:byte list) nonce0 nonce1 nonce2 nonce3
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2784),2784)] /\
        ALLPAIRS nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2784),2784)]
         [(seed,32); (stackpointer,1); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem768_poly_getnoise_eta1_4x) /\
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
                             (shake256 (APPEND sd [word_zx nonce0])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r0 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                   &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce1])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r1 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                   &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce2])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r2 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                   &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (~(r3 = word 0) ==>
                   (let n = num_of_bytelist
                            (list_of_seq
                              (shake256 (APPEND sd [word_zx nonce3])) 128) in
                    !i. i < 256
                        ==> read(memory :> bytes16(word_add r3 (word(2 * i))))
                                 s =
                            iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                    (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                    &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                    (n DIV 2 EXP (4 * i + 3)) MOD 2)))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                memory :> bytes(word_sub stackpointer (word 2784),2784)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
      (mlkem_native_libmlkem_clang17_O2_mc,
       MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GETNOISE4_ALLOWED); LABEL_TAC name safety_th]);;

(*** Up to the test of the fourth pointer ***)

let GETNOISE4_SAFE_START_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC (1--8) THEN
  GETNOISE4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (9--9) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (10--45) THEN
  GETNOISE4_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (46--46) THEN
  GETNOISE4_GOT_TAC THEN
  GETNOISE4_SAFE_CALL_TAC "H_SHAKE256X4"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `128`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word_add (stackpointer:int64)
      (word((if aligned 32 stackpointer then 1888 else 1872) + 224))`;
    `33`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 47 THEN
  GETNOISE4_FIX_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
     ((k-3)--(k-1)) THEN
    GETNOISE4_NORMALIZE_TAC THEN
    GETNOISE4_SAFE_CALL_TAC "H_CBD2"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
      `read X30 s`] k)
   [51; 55; 59] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC (60--60);;

(*** From step k ***)

let GETNOISE4_SAFE_END_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   (k--(k+27)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_EXEC
   ((k+28)--(k+39)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2784),2784] /\
           ALLPAIRS nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2784),2784]
            [seed,32; stackpointer,1; word pc,libmlkem_size;
             word(pc + got_stack_chk_guard),8;
             guard,8; word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_clang17_O2_mc /\
                     read PC s = word (pc + mlkem768_poly_getnoise_eta1_4x) /\
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
                               (word_sub stackpointer (word 2784))
                               returnaddress /\
                        memaccess_inbounds e2
                         [seed,32; stackpointer,1; r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2784),2784;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + mlkem_poly_cbd2_consts),
                          mlkem_poly_cbd2_consts_size;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          ea,el]
                         [r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2784),2784]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(r0,512); memory :> bytes(r1,512);
                   memory :> bytes(r2,512);
                   memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                   memory :> bytes(word_sub stackpointer (word 2784),2784)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
