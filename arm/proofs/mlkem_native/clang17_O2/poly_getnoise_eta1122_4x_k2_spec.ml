(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of two noise polynomials with eta = 3 and two with eta = 2 from  *)
(* a seed and nonces. This is the code for mlkem512_poly_getnoise_eta1122_4x *)
(* from mlkem-native's portable C implementation compiled by clang 17 with   *)
(* -O2 (see mlkem_native/README.md), which computes 192 bytes of SHAKE256 of *)
(* the seed and each of the four nonces into buffers on the stack with       *)
(* mlkem_shake256x4, applies mlkem_poly_cbd3 to the first two and            *)
(* mlkem_poly_cbd2 to the first 128 bytes of the others, and zeroes the      *)
(* buffers, the outputs of SHAKE256 with memset and the inputs with inline   *)
(* stores. It is verified in the whole image (see libmlkem.ml), using the    *)
(* theorems for mlkem_shake256x4, mlkem_poly_cbd3 and mlkem_poly_cbd2 in the *)
(* image and assuming the contracts for memset and memcpy in                 *)
(* utils/mlkem_native_libc.ml.                                               *)
(*                                                                           *)
(* The buffers are aligned to 32 bytes within the stack frame, which the     *)
(* code makes by rounding the stack pointer down, so the proof is by cases   *)
(* on whether the incoming stack pointer is a multiple of 32.                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/shake256x4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_cbd2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_cbd3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem512_poly_getnoise_eta1122_4x:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x440
      +0x20: and     sp, x9, #0xffffffffffffffe0
      +0x24: adrp    x8, <page>
      +0x28: ldrb    w10, [x29, #96]
      +0x2c: add     x26, sp, #0x20
      +0x30: add     x27, sp, #0x120
      +0x34: add     x9, x26, #0x80
      +0x38: add     x23, x27, #0xc0
      +0x3c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x40: add     x24, x27, #0x180
      +0x44: add     x25, x27, #0x240
      +0x48: mov     x19, x3
      +0x4c: mov     x20, x2
      +0x50: mov     x21, x1
      +0x54: ldr     x8, [x8]
      +0x58: mov     x22, x0
      +0x5c: add     x11, x26, #0xc0
      +0x60: add     x0, sp, #0x120
      +0x64: mov     x1, x23
      +0x68: mov     x2, x24
      +0x6c: str     x8, [sp, #1080]
      +0x70: add     x8, x26, #0x40
      +0x74: ldp     q0, q1, [x4]
      +0x78: strb    w5, [sp, #64]
      +0x7c: add     x5, sp, #0x20
      +0x80: strb    w6, [sp, #128]
      +0x84: mov     x3, x25
      +0x88: strb    w7, [sp, #192]
      +0x8c: mov     w4, #0xc0
      +0x90: strb    w10, [sp, #256]
      +0x94: mov     w10, #0x21
      +0x98: mov     x6, x8
      +0x9c: mov     x7, x9
      +0xa0: stp     q0, q1, [sp, #32]
      +0xa4: str     q0, [sp, #96]
      +0xa8: str     q1, [sp, #112]
      +0xac: stp     q0, q1, [sp, #160]
      +0xb0: stp     q0, q1, [sp, #224]
      +0xb4: stp     x11, x10, [sp]
      +0xb8: bl      <mlkem_shake256x4>
      +0xbc: add     x1, sp, #0x120
      +0xc0: mov     x0, x22
      +0xc4: bl      <mlkem_poly_cbd3>
      +0xc8: mov     x0, x21
      +0xcc: mov     x1, x23
      +0xd0: bl      <mlkem_poly_cbd3>
      +0xd4: mov     x0, x20
      +0xd8: mov     x1, x24
      +0xdc: bl      <mlkem_poly_cbd2>
      +0xe0: mov     x0, x19
      +0xe4: mov     x1, x25
      +0xe8: bl      <mlkem_poly_cbd2>
      +0xec: add     x0, sp, #0x120
      +0xf0: mov     w1, wzr
      +0xf4: mov     w2, #0x300
      +0xf8: bl      memset@plt
      +0xfc: movi    v0.2d, #0x0
     +0x100: adrp    x8, <page>
     +0x104: stp     q0, q0, [sp, #32]
     +0x108: stp     q0, q0, [sp, #64]
     +0x10c: stp     q0, q0, [sp, #96]
     +0x110: stp     q0, q0, [sp, #128]
     +0x114: stp     q0, q0, [sp, #160]
     +0x118: stp     q0, q0, [sp, #192]
     +0x11c: stp     q0, q0, [sp, #224]
     +0x120: stp     q0, q0, [sp, #256]
     +0x124: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x128: ldr     x9, [sp, #1080]
     +0x12c: ldr     x8, [x8]
     +0x130: cmp     x8, x9
     +0x134: b.ne    <mlkem512_poly_getnoise_eta1122_4x+0x158>
     +0x138: mov     sp, x29
     +0x13c: ldp     x20, x19, [sp, #80]
     +0x140: ldp     x22, x21, [sp, #64]
     +0x144: ldp     x24, x23, [sp, #48]
     +0x148: ldp     x26, x25, [sp, #32]
     +0x14c: ldp     x28, x27, [sp, #16]
     +0x150: ldp     x29, x30, [sp], #96
     +0x154: ret
     +0x158: bl      __stack_chk_fail

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]  // got_memset
       +0x8: add     x16, x16, #0xfe8  // got_memset
       +0xc: br      x17
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem512_poly_getnoise_eta1122_4x";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. Above the two stack arguments of mlkem_shake256x4 (the pointer to  *)
(* the fourth input and the input length) are its four inputs, the seed and  *)
(* a nonce, at intervals of 64 bytes, and then the four outputs of SHAKE256, *)
(* of 192 bytes each. The seed is copied to the inputs as two 128-bit        *)
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

(*** The input k in the buffer, at state s45, with the nonce byte b ***)

let GETNOISE4_INPUT_TAC =
  let th = CONV_RULE NUM_REDUCE_CONV GETNOISE4_INPUT in
  fun k b ->
    let a = GETNOISE4_AT (32 + 64 * k) in
    MP_TAC(SPECL [a; `sd:byte list`; b; `s46:armstate`] th) THEN
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

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let GETNOISE4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3072):int64)` THEN
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
     (mk_const(r,[]))) (19--27) THEN
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


(*** The first 128 of the 192 bytes of SHAKE256, for mlkem_poly_cbd2 ***)

let GETNOISE4_PREFIX_STMT =
  `!a (f:num->byte) s:armstate.
        read (memory :> bytes(a,192)) s = num_of_bytelist(list_of_seq f 192)
        ==> read (memory :> bytes(a,128)) s =
            num_of_bytelist(list_of_seq f 128)`;;

let GETNOISE4_PREFIX = assume_spec GETNOISE4_PREFIX_STMT;;

let GETNOISE4_PREFIX_TAC k =
  let a = GETNOISE4_AT (288 + 192 * k) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),_)
        when aa = mk_pair(a,`192`) ->
          ASSUME_TAC(MATCH_MP GETNOISE4_PREFIX th)
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy as for    *)
(* mlkem_shake256x4. The seed is 32 bytes at seed, given as a list of bytes  *)
(* sd, and the nonces are the low bytes of the sixth to eighth arguments and *)
(* of the ninth, on the stack. As in mlkem512_poly_getnoise_eta1_4x, the     *)
(* first two results are mlkem_poly_cbd3 applied to the first 192 bytes of   *)
(* shake256 of the seed followed by the nonce, and as in                     *)
(* mlkem512_poly_getnoise_eta2 the other two are mlkem_poly_cbd2 applied to  *)
(* the first 128 bytes. The stack is the 96 bytes of saved registers, 1088   *)
(* bytes of the buffers and the canary, up to 16 bytes of padding for the    *)
(* alignment, and the 1872 used by mlkem_shake256x4 below them.              *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHAKE256X4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD2_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_CBD2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let GETNOISE4_N nonce len =
  vsubst [nonce,`nonce:int64`; len,`len:num`]
   `num_of_bytelist(list_of_seq
     (shake256(APPEND (sd:byte list) [word_zx(nonce:int64)])) len)`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r0 r1 r2 r3 seed (sd:byte list) nonce0 nonce1 nonce2 nonce3
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r0,512); (r1,512); (r2,512); (r3,512);
          (word_sub stackpointer (word 3072),3072)] /\
        ALLPAIRS nonoverlapping
         [(r0,512); (r1,512); (r2,512); (r3,512);
          (word_sub stackpointer (word 3072),3072)]
         [(seed,32); (stackpointer,1); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem512_poly_getnoise_eta1122_4x) /\
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
                             (shake256 (APPEND sd [word_zx nonce2])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r2 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce3])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r3 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512); memory :> bytes(r3,512);
                memory :> bytes(word_sub stackpointer (word 3072),3072)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contracts for memset and memcpy. The events do not depend on the seed or  *)
(* the nonces.                                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let GETNOISE4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC
       (ref [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
             `seed:int64`; `guard:int64`; `mf:int64`; `mc:int64`;
             `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [r0,512; r1,512; r2,512; r3,512;
             word_sub stackpointer (word 3072),3072] /\
           ALLPAIRS nonoverlapping
            [r0,512; r1,512; r2,512; r3,512;
             word_sub stackpointer (word 3072),3072]
            [seed,32; stackpointer,1; word pc,libmlkem_size;
             word(pc + got_stack_chk_guard),8;
             guard,8; word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_clang17_O2_mc /\
                     read PC s =
                       word (pc + mlkem512_poly_getnoise_eta1122_4x) /\
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
                               (word_sub stackpointer (word 3072))
                               returnaddress /\
                        memaccess_inbounds e2
                         [seed,32; stackpointer,1; r0,512; r1,512; r2,512;
                          r3,512; word_sub stackpointer (word 3072),3072;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + mlkem_poly_cbd3_consts),
                          mlkem_poly_cbd3_consts_size;
                          word(pc + mlkem_poly_cbd2_consts),
                          mlkem_poly_cbd2_consts_size;
                          word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el]
                         [r0,512; r1,512; r2,512; r3,512;
                          word_sub stackpointer (word 3072),3072]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(r0,512); memory :> bytes(r1,512);
                   memory :> bytes(r2,512); memory :> bytes(r3,512);
                   memory :> bytes(word_sub stackpointer (word 3072),3072)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
