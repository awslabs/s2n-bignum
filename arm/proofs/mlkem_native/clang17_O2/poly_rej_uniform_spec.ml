(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial from a seed by rejection. This is the    *)
(* code for mlkem_poly_rej_uniform from mlkem-native's portable C            *)
(* implementation compiled by clang 17 with -O2 (see                         *)
(* mlkem_native/README.md), which absorbs the 34 bytes of the seed into a    *)
(* SHAKE128 state, squeezes three blocks of 168 bytes and samples the        *)
(* coefficients below 3329 from them, and then squeezes one more block and   *)
(* samples from it until there are 256, before zeroing the state and the     *)
(* buffer. As at gcc -O3, the sampling of mlk_rej_uniform_c is inlined, as   *)
(* two copies of its loop, one for the first three blocks (loop1) and one    *)
(* for each further block (loop3, inside the loop loop2 that squeezes the    *)
(* blocks). The code is in the whole image (see libmlkem.ml), and the two    *)
(* copies of the loop are verified there with the tool in rej_uniform.ml.    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/shake128_init_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/shake128_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/shake128_squeezeblocks_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/shake128_release_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/rej_uniform_spec.ml";;

(*** The code in the image:

    mlkem_poly_rej_uniform:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: stp     x28, x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0x2f0
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: mov     x19, x0
      +0x20: add     x0, sp, #0x200
      +0x24: mov     x20, x1
      +0x28: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x2c: ldr     x8, [x8]
      +0x30: str     x8, [sp, #744]
      +0x34: bl      <mlkem_shake128_init>
      +0x38: add     x0, sp, #0x200
      +0x3c: mov     x1, x20
      +0x40: mov     w2, #0x22
      +0x44: bl      <mlkem_shake128_absorb_once>
      +0x48: mov     x0, sp
      +0x4c: add     x2, sp, #0x200
      +0x50: mov     w1, #0x3
      +0x54: mov     x21, sp
      +0x58: bl      <mlkem_shake128_squeezeblocks>
      +0x5c: mov     x8, xzr
      +0x60: mov     x20, xzr
      +0x64: add     x9, x21, x8
      +0x68: ldrb    w11, [x9]
      +0x6c: ldrb    w10, [x9, #1]
      +0x70: bfi     w11, w10, #8, #4
      +0x74: cmp     w11, #0xd00
      +0x78: b.hi    <mlkem_poly_rej_uniform+0x88>
      +0x7c: add     x12, x20, #0x1
      +0x80: strh    w11, [x19, x20, lsl #1]
      +0x84: mov     x20, x12
      +0x88: cmp     x20, #0xff
      +0x8c: b.hi    <mlkem_poly_rej_uniform+0xb0>
      +0x90: ldrb    w9, [x9, #2]
      +0x94: lsr     w10, w10, #4
      +0x98: orr     w9, w10, w9, lsl #4
      +0x9c: cmp     w9, #0xd00
      +0xa0: b.hi    <mlkem_poly_rej_uniform+0xb0>
      +0xa4: add     x10, x20, #0x1
      +0xa8: strh    w9, [x19, x20, lsl #1]
      +0xac: mov     x20, x10
      +0xb0: cmp     x20, #0xff
      +0xb4: b.hi    <mlkem_poly_rej_uniform+0xc8>
      +0xb8: add     x9, x8, #0x3
      +0xbc: add     x8, x8, #0x3
      +0xc0: cmp     x9, #0x1f6
      +0xc4: b.cc    <mlkem_poly_rej_uniform+0x64>
      +0xc8: cmp     x20, #0xff
      +0xcc: b.hi    <mlkem_poly_rej_uniform+0x15c>
      +0xd0: mov     x21, sp
      +0xd4: b       <mlkem_poly_rej_uniform+0xe0>
      +0xd8: cmp     x20, #0x100
      +0xdc: b.cs    <mlkem_poly_rej_uniform+0x15c>
      +0xe0: mov     x0, sp
      +0xe4: add     x2, sp, #0x200
      +0xe8: mov     w1, #0x1
      +0xec: bl      <mlkem_shake128_squeezeblocks>
      +0xf0: mov     x8, xzr
      +0xf4: add     x10, x21, x8
      +0xf8: ldrb    w11, [x10]
      +0xfc: ldrb    w9, [x10, #1]
     +0x100: ldrb    w10, [x10, #2]
     +0x104: bfi     w11, w9, #8, #4
     +0x108: cmp     w11, #0xd00
     +0x10c: b.hi    <mlkem_poly_rej_uniform+0x11c>
     +0x110: add     x12, x20, #0x1
     +0x114: strh    w11, [x19, x20, lsl #1]
     +0x118: mov     x20, x12
     +0x11c: cmp     x20, #0xff
     +0x120: b.hi    <mlkem_poly_rej_uniform+0x140>
     +0x124: lsr     w9, w9, #4
     +0x128: orr     w9, w9, w10, lsl #4
     +0x12c: cmp     w9, #0xd00
     +0x130: b.hi    <mlkem_poly_rej_uniform+0x140>
     +0x134: add     x10, x20, #0x1
     +0x138: strh    w9, [x19, x20, lsl #1]
     +0x13c: mov     x20, x10
     +0x140: cmp     x20, #0xff
     +0x144: b.hi    <mlkem_poly_rej_uniform+0xd8>
     +0x148: add     x9, x8, #0x3
     +0x14c: add     x8, x8, #0x3
     +0x150: cmp     x9, #0xa6
     +0x154: b.cc    <mlkem_poly_rej_uniform+0xf4>
     +0x158: b       <mlkem_poly_rej_uniform+0xd8>
     +0x15c: add     x0, sp, #0x200
     +0x160: bl      <mlkem_shake128_release>
     +0x164: movi    v0.2d, #0x0
     +0x168: str     xzr, [sp, #496]
     +0x16c: mov     x8, sp
     +0x170: stp     q0, q0, [sp, #16]
     +0x174: stp     q0, q0, [sp, #48]
     +0x178: stp     q0, q0, [sp, #80]
     +0x17c: stp     q0, q0, [sp, #112]
     +0x180: stp     q0, q0, [sp, #144]
     +0x184: stp     q0, q0, [sp, #176]
     +0x188: stp     q0, q0, [sp, #208]
     +0x18c: stp     q0, q0, [sp, #240]
     +0x190: stp     q0, q0, [sp, #272]
     +0x194: stp     q0, q0, [sp, #304]
     +0x198: stp     q0, q0, [sp, #336]
     +0x19c: stp     q0, q0, [sp, #368]
     +0x1a0: stp     q0, q0, [sp, #400]
     +0x1a4: stp     q0, q0, [sp, #432]
     +0x1a8: stp     q0, q0, [sp, #464]
     +0x1ac: str     q0, [sp]
     +0x1b0: adrp    x8, <page>
     +0x1b4: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x1b8: ldr     x9, [sp, #744]
     +0x1bc: ldr     x8, [x8]
     +0x1c0: cmp     x8, x9
     +0x1c4: b.ne    <mlkem_poly_rej_uniform+0x1dc>
     +0x1c8: mov     sp, x29
     +0x1cc: ldp     x20, x19, [sp, #32]
     +0x1d0: ldp     x28, x21, [sp, #16]
     +0x1d4: ldp     x29, x30, [sp], #48
     +0x1d8: ret     
     +0x1dc: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem_poly_rej_uniform"];;

(* ------------------------------------------------------------------------- *)
(* The two copies of the sampling loop. The first samples from the three     *)
(* blocks in the buffer at X21, from offset 0, with X8 the index and X20 the *)
(* counter, and exits to loop1_exit both when there are 256 coefficients and *)
(* at the end of the buffer. The second samples from one block at X21 in the *)
(* same way, and exits to loop3_exit1 when there are 256 coefficients and to *)
(* loop3_exit2, which branches to loop3_exit1, at the end of the buffer.     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1 =
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC;
    rej_header = "mlkem_poly_rej_uniform_loop1";
    rej_full = "mlkem_poly_rej_uniform_loop1_exit";
    rej_end = "mlkem_poly_rej_uniform_loop1_exit";
    rej_base = "X21"; rej_ofs = 0; rej_idx = "X8"; rej_buflen = 504;
    rej_ctr = "X20"; rej_out = "X19";
    rej_fields = "X11","X9"; rej_flag = None;
    rej_regs = ["X8"; "X9"; "X10"; "X11"; "X12"; "X20"] };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3 =
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC;
    rej_header = "mlkem_poly_rej_uniform_loop3";
    rej_full = "mlkem_poly_rej_uniform_loop3_exit1";
    rej_end = "mlkem_poly_rej_uniform_loop3_exit2";
    rej_base = "X21"; rej_ofs = 0; rej_idx = "X8"; rej_buflen = 168;
    rej_ctr = "X20"; rej_out = "X19";
    rej_fields = "X11","X9"; rej_flag = None;
    rej_regs = ["X8"; "X9"; "X10"; "X11"; "X12"; "X20"] };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1_FULL =
  assuming_proofs (fun () ->
  REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1_CORRECT =
  assuming_proofs (fun () ->
  REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1
   MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1_FULL);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3_FULL =
  assuming_proofs (fun () ->
  REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3_CORRECT =
  assuming_proofs (fun () ->
  REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3
   MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3_FULL);;

(* ------------------------------------------------------------------------- *)
(* The bytes of SHAKE128 in blocks of 168, the rate, in terms of the         *)
(* absorbed state, as for mlkem_shake256 and mlkem_shake256x4.               *)
(* ------------------------------------------------------------------------- *)

let REJ_SPONGE_STMT =
  `!(m:byte list) k n.
        n <= 168
        ==> num_of_bytelist(list_of_seq (\j. shake128 m (168 * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor
                   (keccak_absorb 168
                     (num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                     (LENGTH m DIV 168))
                   (word((num_of_bytelist m +
                          2 EXP (8 * LENGTH m) *
                          num_of_bytelist(keccak_pad 168 0x1F (LENGTH m))) DIV
                         2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                         2 EXP (8 * 168))))) MOD 2 EXP (8 * n)`;;

let REJ_SPONGE = assume_spec REJ_SPONGE_STMT;;

let REJ_XOF_BLOCKS_STMT =
  `!(f:num->byte) n.
        num_of_bytelist(list_of_seq f (168 * n)) =
        nsum {i | i < n}
         (\i. 2 EXP (8 * 168 * i) *
              num_of_bytelist(list_of_seq (\j. f(168 * i + j)) 168))`;;

let REJ_XOF_BLOCKS = assume_spec REJ_XOF_BLOCKS_STMT;;

let REJ_SHAKE128_BLOCKS_STMT =
  `!(m:byte list) b.
        num_of_bytelist(list_of_seq (shake128 m) (168 * b)) =
        nsum {i | i < b}
         (\i. 2 EXP (8 * 168 * i) *
              val(keccak_squeeze (i + 1)
                   (word_xor
                     (keccak_absorb 168
                       (num_of_bytelist m +
                        2 EXP (8 * LENGTH m) *
                        num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                       (LENGTH m DIV 168))
                     (word((num_of_bytelist m +
                            2 EXP (8 * LENGTH m) *
                            num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                           DIV 2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                           2 EXP (8 * 168))))) MOD 2 EXP (8 * 168))`;;

let REJ_SHAKE128_BLOCKS = assume_spec REJ_SHAKE128_BLOCKS_STMT;;

let KECCAK_SQUEEZE_ADD_STMT =
  `!m n (S:1600 word).
        keccak_squeeze m (keccak_squeeze n S) = keccak_squeeze (m + n) S`;;

let KECCAK_SQUEEZE_ADD = assume_spec KECCAK_SQUEEZE_ADD_STMT;;

let REJ_NSUM_1_STMT =
  `!f. nsum {j | j < 1} f = f 0`;;

let REJ_NSUM_1 = assume_spec REJ_NSUM_1_STMT;;

(* ------------------------------------------------------------------------- *)
(* The 12-bit fields of the first 504 + 168 * j bytes, those of three blocks *)
(* and j more, and the samples from them, with REJ_SAMPLE as in              *)
(* rej_uniform.ml.                                                           *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_OF_NUM_ADD = prove
 (`!m n x. wordlist_of_num (m + n) x:(N word)list =
           APPEND (wordlist_of_num m x)
                  (wordlist_of_num n (x DIV 2 EXP (dimindex(:N) * m)))`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; wordlist_of_num; APPEND; MULT_CLAUSES; EXP;
              DIV_1] THEN
  ASM_REWRITE_TAC[CONS_11; DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `d + d * m = d * SUC m`]);;

let REJ_WORDLIST_APPEND_STMT =
  `!(f:num->byte) m n.
        8 * m = 12 * n
        ==> wordlist_of_num (n + 112)
             (num_of_bytelist(list_of_seq f (m + 168))):(12 word)list =
            APPEND (wordlist_of_num n (num_of_bytelist(list_of_seq f m)))
                   (wordlist_of_num 112
                     (num_of_bytelist(list_of_seq (\i. f(m + i)) 168)))`;;

let REJ_WORDLIST_APPEND = assume_spec REJ_WORDLIST_APPEND_STMT;;

let REJ_FIELDS_SUC_STMT =
  `!(f:num->byte) j.
        wordlist_of_num (336 + 112 * (j + 1))
         (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))):(12 word)list =
        APPEND
         (wordlist_of_num (336 + 112 * j)
           (num_of_bytelist(list_of_seq f (504 + 168 * j))))
         (wordlist_of_num 112
           (num_of_bytelist(list_of_seq (\i. f((504 + 168 * j) + i)) 168)))`;;

let REJ_FIELDS_SUC = assume_spec REJ_FIELDS_SUC_STMT;;

let REJ_FIELDS_PREFIX_STMT =
  `!(f:num->byte) j k.
        j <= k
        ==> ?t. wordlist_of_num (336 + 112 * k)
                 (num_of_bytelist(list_of_seq f (504 + 168 * k))):
                (12 word)list =
                APPEND (wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j)))) t`;;

let REJ_FIELDS_PREFIX = assume_spec REJ_FIELDS_PREFIX_STMT;;

let REJ_COUNT_MONO_STMT =
  `!(f:num->byte) j k.
        j <= k
        ==> LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <=
            LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist(list_of_seq f (504 + 168 * k)))))`;;

let REJ_COUNT_MONO = assume_spec REJ_COUNT_MONO_STMT;;

let REJ_SAMPLE_FINAL_STMT =
  `!(f:num->byte) j k.
        j <= k /\
        256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                       (num_of_bytelist(list_of_seq f (504 + 168 * j)))))
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                (num_of_bytelist(list_of_seq f (504 + 168 * k))))) =
            SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                (num_of_bytelist(list_of_seq f (504 + 168 * j)))))`;;

let REJ_SAMPLE_FINAL = assume_spec REJ_SAMPLE_FINAL_STMT;;

let REJ_SAMPLE_SUC_STMT =
  `!(f:num->byte) j.
        LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                 (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <= 256
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
                (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
            APPEND
             (SUB_LIST(0,256)
               (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                  (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
             (SUB_LIST(0,256 -
                       LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
               (REJ_SAMPLE(wordlist_of_num 112
                  (num_of_bytelist
                    (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`;;

let REJ_SAMPLE_SUC = assume_spec REJ_SAMPLE_SUC_STMT;;

(* ------------------------------------------------------------------------- *)
(* Lists of 12-bit fields and of 16-bit samples in memory.                   *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_FROM_BYTES_STMT =
  `!a m n x s:armstate.
        12 * n = 8 * m /\ read (memory :> bytes(a,m)) s = x
        ==> wordlist_from_memory(a,n) s = (wordlist_of_num n x:(12 word)list)`;;

let REJ_WORDLIST_FROM_BYTES = assume_spec REJ_WORDLIST_FROM_BYTES_STMT;;

let REJ_BYTES16_OF_WORDLIST_STMT =
  `!a n (l:int16 list) s:armstate.
        wordlist_from_memory(a,n) s = l
        ==> read (memory :> bytes(a,2 * n)) s = num_of_wordlist l`;;

let REJ_BYTES16_OF_WORDLIST = assume_spec REJ_BYTES16_OF_WORDLIST_STMT;;

let REJ_WORDLIST_OF_BYTES16_STMT =
  `!a (l:int16 list) s:armstate.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l
        ==> wordlist_from_memory(a,LENGTH l) s = l`;;

let REJ_WORDLIST_OF_BYTES16 = assume_spec REJ_WORDLIST_OF_BYTES16_STMT;;

let REJ_BYTES16_APPEND_N_STMT =
  `!a n (l1:int16 list) (l2:int16 list) s:armstate.
        LENGTH l1 = n /\
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l1 /\
        read (memory :> bytes(word_add a (word(2 * n)),2 * LENGTH l2)) s =
        num_of_wordlist l2
        ==> read (memory :> bytes(a,2 * (n + LENGTH l2))) s =
            num_of_wordlist(APPEND l1 l2)`;;

let REJ_BYTES16_APPEND_N = assume_spec REJ_BYTES16_APPEND_N_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffer for three blocks, followed by the state, is aligned to 32      *)
(* bytes within the stack frame, so its address depends on whether the stack *)
(* pointer is a multiple of 32 or just of 16. The code saves 48 bytes of     *)
(* registers and subtracts 752 more, which puts the buffer 800 or 816 bytes  *)
(* below the incoming stack pointer. The stack used is 1120 bytes, so the    *)
(* buffer is 320 or 304 bytes above its bottom.                              *)
(* ------------------------------------------------------------------------- *)

let REJ_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let REJ_ALIGNED_16_32 = assume_spec REJ_ALIGNED_16_32_STMT;;

let REJ_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 320)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 320 else 304))`;;

let REJ_BUFFER_ADDRESS = assume_spec REJ_BUFFER_ADDRESS_STMT;;

(*** The frames of the callees, 288 bytes below the buffer for ***)
(*** mlkem_shake128_absorb_once and 240 for the squeezing       ***)

let REJ_SUB_FRAMES_STMT =
  `word_sub (word(if aligned 32 (stackpointer:int64) then 320 else 304))
            (word 288):int64 =
   word((if aligned 32 stackpointer then 320 else 304) - 288) /\
   word_sub (word(if aligned 32 (stackpointer:int64) then 320 else 304))
            (word 240):int64 =
   word((if aligned 32 stackpointer then 320 else 304) - 240)`;;

let REJ_SUB_FRAMES = assume_spec REJ_SUB_FRAMES_STMT;;

let REJ_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 320))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 320 else 304))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC REJ_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let REJ_BUF = `word_add (stackpointer:int64)
                (word(if aligned 32 stackpointer then 320 else 304))`;;

let REJ_CTX = `word_add (stackpointer:int64)
                (word((if aligned 32 stackpointer then 320 else 304) + 512))`;;

let REJ_ADDRESS_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC;
               REJ_SUB_FRAMES] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let REJ_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE REJ_ADDRESS_CONV th else th);;

let REJ_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1120):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `aligned 16 (word_add (stackpointer:int64)
      (word(if aligned 32 (stackpointer:int64) then 320 else 304)):int64)`
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `304 <= (if aligned 32 (stackpointer:int64) then 320 else 304) /\
    (if aligned 32 (stackpointer:int64) then 320 else 304) <= 320`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) [19; 20; 21; 28; 29];;

(*** The address of the stack guard in the form of the precondition of ***)
(*** mlkem_shake128_absorb_once, which has the stack protector inlined ***)

let REJ_GOT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             (vsubst [mk_small_numeral(layout "got_stack_chk_guard"),`n:num`]
               `read (memory :> bytes64
                       (word_add (word (pc:num)) (word n):int64)) s =
                (g:int64)`)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as for                *)
(* mlkem_shake128x4_release. The seed is 34 bytes at seed, given as a list   *)
(* of bytes inp. The loop sampling from one more block at a time stops when  *)
(* there are 256 samples, so the theorem has the hypothesis that there are   *)
(* at least 256 samples, values below 3329, among the 12-bit fields of the   *)
(* first 504 + 168 * k bytes of shake128 of the seed for some k, and the     *)
(* result is the first 256 of those samples. The proof uses the minimal such *)
(* k, k0, as the number of iterations of loop2. The stack is the 816 bytes   *)
(* of the function (the saved registers and the buffers, with the stack      *)
(* pointer rounded down to a multiple of 32) and the 288 used by             *)
(* mlkem_shake128_absorb_once below them, 1104 bytes, taken as 1120 so that  *)
(* its bottom is a multiple of 32 if the stack pointer is. The function      *)
(* does not call memset, so the hypotheses about memset are not used.        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INIT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHAKE128_INIT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ABSORB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_LOOP1_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1_CORRECT);;

let LOCAL_LOOP3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3_CORRECT);;

let LOCAL_RELEASE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHAKE128_RELEASE_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The fields and samples, and the blocks and samples from them ***)

let rej_fields j =
  vsubst [j,`j:num`]
   `wordlist_of_num (336 + 112 * j)
     (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * j))):
    (12 word)list`;;

let rej_count j = mk_comb(`LENGTH:(16 word)list->num`,
                          mk_comb(`REJ_SAMPLE`,rej_fields j));;

let rej_block i =
  vsubst [i,`i:num`]
   `wordlist_of_num 112
     (num_of_bytelist
       (list_of_seq (\j. shake128 inp ((504 + 168 * i) + j)) 168)):
    (12 word)list`;;

let rej_l1 i =
  mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
          mk_comb(`REJ_SAMPLE`,rej_fields i));;

let rej_l2 i =
  mk_comb(`SUB_LIST(0,256 - ci):(16 word)list->(16 word)list`,
          mk_comb(`REJ_SAMPLE`,rej_block i));;

(*** The facts at the intermediate points, with the saved registers ***)

let REJ_FRAME =
 `read SP s =
  word_add stackpointer (word(if aligned 32 stackpointer then 320 else 304)) /\
  read X29 s = word_add stackpointer (word 1072) /\
  read (memory :> bytes64 (word_add stackpointer (word 1072))) s = x29_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1080))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 1088))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1096))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1104))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1112))) s = x19_init /\
  read (memory :> bytes64
   (word_add stackpointer
     (word((if aligned 32 stackpointer then 320 else 304) + 744)))) s =
  canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X21 s =
  word_add stackpointer (word(if aligned 32 stackpointer then 320 else 304)) /\
  read X19 s = entry`;;

let REJ_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,REJ_FRAME));;

(*** At the header of loop1, with the fields of the first three blocks ***)

let REJ_A0 = REJ_AT
 `\s. read X20 s = word 0 /\ read X8 s = word 0 /\
      wordlist_from_memory
       (word_add stackpointer
         (word(if aligned 32 stackpointer then 320 else 304)),336) s =
      (wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 320 else 304) + 512)),
              200)) s =
      val(keccak_squeeze 3 (S0:1600 word))`;;

(*** At the header of loop2, after 3 + i blocks ***)

let REJ_INV = REJ_AT
 `\i s. read X20 s =
        word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
          (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))) /\
        read (memory :> bytes(entry,2 * MIN 256 (LENGTH(REJ_SAMPLE
          (wordlist_of_num (336 + 112 * i)
            (num_of_bytelist(list_of_seq (shake128 inp)
                               (504 + 168 * i)))))))) s =
        num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
          (336 + 112 * i)
          (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 320 else 304) + 512)),
                200)) s =
        val(keccak_squeeze (3 + i) (S0:1600 word))`;;

(*** At loop2_exit, with the 256 coefficients ***)

let REJ_A2 = REJ_AT
 `\s. read (memory :> bytes(entry,512)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * k)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * k))))))`;;

(*** The absorbed state as S0, and the minimal number k0 of blocks ***)

let REJ_ABSORBED =
 `word_xor
   (keccak_absorb 168
     (num_of_bytelist inp +
      2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34))
     (34 DIV 168))
   (word((num_of_bytelist inp +
          2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34)) DIV
         2 EXP (8 * 168 * 34 DIV 168) MOD 2 EXP (8 * 168))):1600 word`;;

let REJ_ABSORBED_TAC =
  let len = ASSUME `LENGTH(inp:byte list) = 34` in
  ABBREV_TAC(mk_eq(`S0:1600 word`,REJ_ABSORBED)) THEN
  ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(REJ_ABSORBED,`S0:1600 word`))]
              (SPEC `inp:byte list` REJ_SPONGE)) THEN
  ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(REJ_ABSORBED,`S0:1600 word`))]
              (SPEC `inp:byte list` REJ_SHAKE128_BLOCKS));;

let REJ_MINIMAL_TAC =
  let p = mk_abs(`n:num`,
           mk_comb(mk_comb(`(<=):num->num->bool`,`256`),
             mk_comb(`LENGTH:(16 word)list->num`,
               mk_comb(`REJ_SAMPLE`,rej_fields `n:num`)))) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The samples from the first three blocks and from one more block ***)

let REJ_INPUT0_TAC s =
  SUBGOAL_THEN
   (subst [REJ_BUF,`buf:int64`; s,`s:armstate`]
     `wordlist_from_memory(buf,336) s =
      (wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `504` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `504 = 168 * 3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let REJ_BLOCK_TAC s =
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJ_BUF,`112`); s]),
          rej_block `i:num`))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `168` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `!k n. n <= 168 ==> a = b`) (concl th) then
        MP_TAC(SPECL [`3 + i`; `168`] th) else NO_TAC) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `168 * (3 + i) = 504 + 168 * i`;
                ARITH_RULE `(3 + i) + 1 = 3 + i + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let REJ_POST_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then
      STRIP_ASSUME_TAC(REWRITE_RULE[GSYM REJ_SAMPLE]
        (CONV_RULE(TOP_DEPTH_CONV let_CONV) th))
    else NO_TAC);;

let REJ_COMBINE_TAC s =
  REJ_POST_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  SUBGOAL_THEN
   (mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `i:num`),`ci:num`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`entry:int64`; `ci:num`; rej_l1 `i:num`; rej_l2 `i:num`;
                 s] REJ_BYTES16_APPEND_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (let th = MP (REWRITE_RULE[ASSUME(mk_eq(rej_count `i:num`,`ci:num`))]
                (ISPECL [`shake128 inp`; `i:num`] REJ_SAMPLE_SUC))
               (ASSUME `ci <= 256`) in
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
   MP_TAC(AP_TERM `LENGTH:(16 word)list->num` th)) THEN
  REWRITE_TAC[LENGTH_APPEND;
    ASSUME(mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `i:num`),
                 `ci:num`))] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [LENGTH_SUB_LIST] THEN
  REWRITE_TAC[SUB_0] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]));;

(*** The exit of a loop, decided by whether there are 256 samples ***)

let REJ_C0 =
  `LENGTH(REJ_SAMPLE(wordlist_of_num 336
     (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list))`
and REJ_CN = mk_comb(`MIN 256`,rej_count `i + 1`);;

let REJ_EXIT_COND_TAC c d =
  SUBGOAL_THEN (mk_eq(mk_eq(mk_comb(`MIN 256`,c),`256`),d))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    (ASM_REWRITE_TAC[] THEN NO_TAC ORELSE
     FIRST_ASSUM(fun th ->
       if is_binary "<" (concl th) && lhand(concl th) = c
       then MP_TAC th THEN ARITH_TAC else NO_TAC));
    ALL_TAC];;

let REJ_MIN_TAC =
  FIRST_ASSUM(fun th ->
    if is_binary "<" (concl th) && rand(concl th) = `256` &&
       can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE"
                               with _ -> false)) (lhand(concl th))
    then REWRITE_TAC[MATCH_MP (ARITH_RULE `x < 256 ==> MIN 256 x = x`) th]
    else NO_TAC);;

let REJ_LS_TAC =
  SUBGOAL_THEN (mk_eq(mk_eq(REJ_CN,`256`),`~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN EQ_TAC THENL
     [DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i + 1` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC];;

(*** The parts of the proof ***)

let REJ_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`entry:int64`; `seed:int64`; `inp:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1120 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

let REJ_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (1--6) THEN REJ_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC [7] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (8--14) THEN REJ_NORMALIZE_TAC THEN
  LOCAL_INIT_TAC [`read X0 s`; `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (16--19) THEN REJ_NORMALIZE_TAC THEN
  REJ_GOT_TAC THEN
  LOCAL_ABSORB_TAC [`read X0 s`; `read X1 s`; `34`;
                    `num_of_bytelist(inp:byte list)`; `guard:int64`;
                    `pc:num`; `read SP s`; `read X30 s`] 20 THEN REJ_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (21--25) THEN REJ_NORMALIZE_TAC THEN
  LOCAL_SQUEEZE_TAC [`read X0 s`; `3`; `read X2 s`; `S0:1600 word`;
                     `pc:num`; `read SP s`; `read X30 s`] 26 THEN REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (27--28) THEN
  REJ_NORMALIZE_TAC THEN REJ_INPUT0_TAC `s28:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** loop1, giving the samples from the first three blocks ***)

let REJ_LOOP1_TAC =
  ASSUME_TAC(INST_TYPE [`:12`,`:N`] (ISPECL
   [`336`; `num_of_bytelist(list_of_seq (shake128 inp) 504)`]
   LENGTH_WORDLIST_OF_NUM)) THEN
  LOCAL_LOOP1_TAC [`read X19 s`; `0`; `read X21 s`; `504`;
     `wordlist_of_num 336 (num_of_bytelist(list_of_seq (shake128 inp) 504)):
      (12 word)list`; `pc:num`] 1 THEN
  REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(entry,n) s = l:int16 list`) o
    concl));;

let REJ_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  ENSURES_INIT_TAC "s0" THEN REJ_LOOP1_TAC THEN
  REJ_EXIT_COND_TAC REJ_C0 `T` THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),`256`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`shake128 inp`; `0`; `k:num`] REJ_SAMPLE_FINAL) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[];;

let REJ_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rej_count `k0:num`),`256`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MP_TAC(ISPECL [`shake128 inp`; `k0:num`; `k:num`] REJ_SAMPLE_FINAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJ_FINAL_TAC =
  SUBGOAL_THEN
   (mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),`256`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),
                        `256`)
    then GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]
    else NO_TAC) THEN
  MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[];;

(*** One step at a time through the comparisons and branches at the end ***)
(*** of a block, deciding them from the numbers of samples              ***)

let REJ_BR_STEPS_TAC ns =
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC [n] THEN
    REJ_NORM_TAC THEN REJ_FLAGS_TAC THEN TRY DECIDE_BRANCH_TAC) ns;;

(*** Rewrite the assumptions that give a component of the state, not ***)
(*** those about the events of the segments                         ***)

let REJ_READ_RULE_TAC rule =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c &&
       (match lhs c with
          Comb(Comb(Const("read",_),_),_) -> true | _ -> false)
    then rule th else th);;

let REJ_MIN_FACT_TAC c =
  FIRST_ASSUM(fun th ->
    if concl th = mk_binop `(<):num->num->bool` c `256`
    then let mth = MATCH_MP (ARITH_RULE `x < 256 ==> MIN 256 x = x`) th in
         REJ_READ_RULE_TAC(REWRITE_RULE[mth]) THEN ASSUME_TAC mth
    else NO_TAC);;

(*** The end of the body of loop2, the test of loop2 after loop3 ***)

let REJ_ENDBODY_STEPS_TAC =
  ASM_CASES_TAC `i + 1 < k0` THENL
   [SUBGOAL_THEN (mk_binop `(<):num->num->bool` (rej_count `i + 1`) `256`)
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i + 1` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[NOT_LE];
      ALL_TAC] THEN
    REJ_MIN_FACT_TAC (rej_count `i + 1`) THEN
    REJ_STATE_RULE_TAC(REWRITE_RULE[ASSUME `i + 1 < k0`]) THEN
    REJ_BR_STEPS_TAC [8;9;10];
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rej_count `i + 1`),`256`))
    (fun th -> REJ_READ_RULE_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REJ_STATE_RULE_TAC(REWRITE_RULE[ASSUME `~(i + 1 < k0)`]) THEN
    REJ_BR_STEPS_TAC [8;9]];;

let REJ_ENDBODY_TAC =
  REJ_ENDBODY_STEPS_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** From the header of loop1 to that of loop2, if one more block is ***)
(*** needed: the samples from the first three blocks are fewer than 256 ***)

let REJ_ENTER_TAC =
  ENSURES_INIT_TAC "s0" THEN REJ_LOOP1_TAC THEN
  REJ_EXIT_COND_TAC REJ_C0 `F` THEN
  REJ_MIN_FACT_TAC REJ_C0 THEN
  REJ_BR_STEPS_TAC [2;3;4;5] THEN
  REJ_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REJ_MIN_TAC THEN ASM_REWRITE_TAC[];;

(*** The body of loop2, from 3 + i blocks to 3 + i + 1 ***)

let REJ_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` (rej_count `i:num`) `256`)
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  REJ_MIN_TAC THEN ENSURES_INIT_TAC "s0" THEN

  (*** Squeezing one more block from the state ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (1--4) THEN REJ_NORMALIZE_TAC THEN
  KECCAK_STATE_AT_TAC REJ_CTX THEN
  LOCAL_SQUEEZE_TAC [`read X0 s`; `1`; `read X2 s`;
                     `keccak_squeeze (3 + i) (S0:1600 word)`;
                     `pc:num`; `read SP s`; `read X30 s`] 5 THEN REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN

  (*** Sampling from it in loop3 after the ci samples so far ***)

  ABBREV_TAC (mk_eq(`ci:num`,rej_count `i:num`)) THEN
  SUBGOAL_THEN `ci <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `ci < 256` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC [6] THEN
  REJ_BLOCK_TAC `s6:armstate` THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rej_block `i:num`)] LENGTH_WORDLIST_OF_NUM)) THEN
  LOCAL_LOOP3_TAC [`read X19 s`; `ci:num`; `read X21 s`; `168`;
                   rej_block `i:num`; `pc:num`] 7 THEN
  REJ_COMBINE_TAC `s7:armstate` THEN

  (*** The exit of loop3, decided by whether there are 256 samples now, ***)
  (*** and the test of loop2 at the end of the block                    ***)

  REJ_LS_TAC THEN
  REJ_ENDBODY_TAC;;

(*** loop2, if one more block is needed ***)

let REJ_LOOP_TAC =
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` REJ_C0 `256`) ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NOT_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `k0:num` `pc + mlkem_poly_rej_uniform_loop2`
   `pc + mlkem_poly_rej_uniform_loop2_exit` REJ_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REJ_ENTER_TAC;
    REJ_BODY_TAC;
    REJ_EXIT_TAC];;

(*** Releasing the state, zeroing the buffer, the stack guard, return ***)

let REJ_PART3_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (1--2) THEN REJ_NORMALIZE_TAC THEN
  LOCAL_RELEASE_TAC [`read X0 s`; `pc:num`; `read X30 s`] 3 THEN REJ_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (4--23) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (24--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REJ_FINAL_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!entry seed (inp:byte list) k guard mf ea el ev pc stackpointer
   returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH inp = 34 /\
        256 <= LENGTH(FILTER (\x. val x < 3329)
                       (MAP (word_zx:12 word->16 word)
                         (wordlist_of_num (336 + 112 * k)
                           (num_of_bytelist
                             (list_of_seq (shake128 inp)
                                          (504 + 168 * k)))))) /\
        nonoverlapping (entry,512) (word_sub stackpointer (word 1120),1120) /\
        ALLPAIRS nonoverlapping
         [(entry,512); (word_sub stackpointer (word 1120),1120)]
         [(seed,34); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem_poly_rej_uniform) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [entry; seed] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,34)) s = num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(entry,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp) (504 + 168 * k)))))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(entry,512);
                memory :> bytes(word_sub stackpointer (word 1120),1120)])`;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the addresses and on the   *)
(* seed, which is public, through the samples and the number of iterations   *)
(* of loop2, the least k for which there are 256 samples, and the            *)
(* hypothesis about the samples is still needed for the loop to terminate.   *)
(* The events are given by a template with the parts before loop1, in loop1  *)
(* if no more block is needed, in loop1 and from it to loop2 otherwise, in   *)
(* loop2 and after it, and the proof uses the combined theorems for the hash *)
(* functions and for loop1 and loop3, with the facts of the correctness      *)
(* proof. The test at the end of the body of loop2 leaves the loop in the    *)
(* last iteration, so its events (and those of the exit of loop3 before it)  *)
(* differ from those of the other iterations, and the template has a case    *)
(* for the last iteration. The check that the accesses are in bounds is done *)
(* separately for the two alignments of the stack pointer, as its arithmetic *)
(* is slow with the conditional in the offsets.                              *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/subroutine_signatures.ml";;

(*** The events of single steps are consed to the events of a call, as ***)
(*** CONS ev (APPEND ...), but the unification of the events needs     ***)
(*** them as APPEND [ev] (APPEND ...)                                  ***)

let CONS_APPEND_EVENT = prove
 (`!(h:uarch_event) t. CONS h t = APPEND [h] t`,
  REWRITE_TAC[APPEND]);;

let PREJ_CONS_CONV tm =
  match tm with
    Comb(Comb(Const("CONS",_),h),t)
      when type_of h = `:uarch_event` && not(is_const t) ->
        REWR_CONV CONS_APPEND_EVENT tm
  | _ -> failwith "PREJ_CONS_CONV";;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, with only the facts about events  ***)
(*** for the check of the memory accesses, as the arithmetic of each  ***)
(*** failed attempt to place an access in a region is slow with all   ***)
(*** the assumptions. The existential witness for the events is       ***)
(*** renamed first to a name used nowhere else, as one of the         ***)
(*** instantiations can otherwise clash with the variable of a later  ***)
(*** case                                                             ***)

let PREJ_KEEP_EVENTS_TAC (asl,w) =
  let keep th =
    let c = concl th in
    (match strip_comb c with
       Const("memaccess_inbounds",_),_ -> true | _ -> false) ||
    (is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list`) ||
    (is_binary "<=" c && rand c = `256` &&
     (match lhand c with Comb(Const("LENGTH",_),_) -> true | _ -> false)) in
  null_meta,[filter (keep o snd) asl,w],(fun i ths -> hd ths);;

(*** The buffer is 320 or 304 bytes above the bottom of the frame, ***)
(*** depending on the alignment of the stack pointer. The check of ***)
(*** the memory accesses is slow with the conditional in the       ***)
(*** offsets, so it is done separately in the two cases            ***)

let PREJ_ALIGN_CASES_TAC tac =
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THEN
  FIRST_X_ASSUM(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
    CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_SUB_CONV)) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_SUB_CONV)))) THEN
  tac;;

let PREJ_META_COUNT = ref 0;;

let PREJ_DISCHARGE_TAC =
  CONV_TAC(DEPTH_CONV PREJ_CONS_CONV) THEN
  REWRITE_TAC[ENUMERATEL_APPEND_ZERO; GSYM APPEND_ASSOC] THEN
  W(fun (asl,w) ->
    let v,_ = dest_exists w in
    PREJ_META_COUNT := !PREJ_META_COUNT + 1;
    CONV_TAC(GEN_ALPHA_CONV
      (mk_var("e2_seg" ^ string_of_int(!PREJ_META_COUNT),type_of v)))) THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    PREJ_KEEP_EVENTS_TAC THEN
    RULE_ASSUM_TAC(fun th ->
      if is_eq(concl th) && lhs(concl th) = `e2:(uarch_event)list`
      then REWRITE_RULE[GSYM APPEND_ASSOC] th else th) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    PREJ_ALIGN_CASES_TAC DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(*** The trace e2 before a segment is kept as a variable: at the start  ***)
(*** of the segment, the same expression in the postcondition is folded ***)
(*** into e2, and its definition is taken out of the assumptions, so    ***)
(*** that the unification of the events of the segment does not look at ***)
(*** the earlier ones. The bound e2 of the postcondition is renamed     ***)
(*** first, as the folding can't be done under its binder               ***)

let PREJ_E2_TAC =
  let is_e2eq th =
    let c = concl th in
    is_eq c && is_var(lhs c) && fst(dest_var(lhs c)) = "e2" in
  let rename t =
    let v,_ = dest_exists t in
    if fst(dest_var v) = "e2" then GEN_ALPHA_CONV (mk_var("e2'",type_of v)) t
    else failwith "rename" in
  let fold th = CHANGED_TAC(GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM th]) in
  CONV_TAC(ONCE_DEPTH_CONV rename) THEN
  FIRST_X_ASSUM(fun th ->
    if is_e2eq th then
      fold th ORELSE
      (REWRITE_TAC[GSYM APPEND_ASSOC] THEN
       fold(REWRITE_RULE[GSYM APPEND_ASSOC] th))
    else NO_TAC);;

let PREJ_SAFE_TEMPLATE =
 `\(entry:int64) (seed:int64) (inp:byte list) (guard:int64) (mf:int64)
   (pc:num) (stackpointer:int64) (returnaddress:int64).
   APPEND (f_ev_p3 entry seed inp guard mf pc stackpointer returnaddress)
    (APPEND
      (if (minimal n.
             256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * n)
                     (num_of_bytelist
                       (list_of_seq (shake128 inp) (504 + 168 * n)))))) = 0
       then f_ev_skip entry seed inp guard mf pc stackpointer returnaddress
       else
        APPEND
         (f_ev_exit entry seed inp guard mf pc stackpointer returnaddress)
         (APPEND
           (ENUMERATEL
             (minimal n.
                256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * n)
                        (num_of_bytelist
                          (list_of_seq (shake128 inp) (504 + 168 * n))))))
             (\i. if i + 1 <
                      (minimal n.
                        256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * n)
                                (num_of_bytelist
                                  (list_of_seq (shake128 inp)
                                               (504 + 168 * n))))))
                   then f_ev_loop entry seed inp guard mf pc stackpointer
                          returnaddress i
                   else f_ev_last entry seed inp guard mf pc stackpointer
                          returnaddress i))
           (f_ev_enter entry seed inp guard mf pc stackpointer returnaddress)))
      (f_ev_p1 entry seed inp guard mf pc stackpointer returnaddress))
   :(uarch_event)list`;;

let PREJ_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_INIT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_CLANG17_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP1_FULL "H_LOOP1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_LOOP3_FULL "H_LOOP3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128_RELEASE_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_RELEASE" THEN
  CONCRETIZE_F_EVENTS_TAC PREJ_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REJ_SETUP_TAC THEN REJ_ABSORBED_TAC THEN REJ_MINIMAL_TAC;;

let PREJ_ALLOWED =
  [`pc:num`; `entry:int64`; `seed:int64`; `inp:byte list`; `guard:int64`;
   `mf:int64`; `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `e2:(uarch_event)list`; `k0:num`;
   `f_ev_loop:int64->int64->byte list->int64->int64->num->int64->int64->
              num->(uarch_event)list`;
   `f_ev_last:int64->int64->byte list->int64->int64->num->int64->int64->
              num->(uarch_event)list`];;

let PREJ_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,
       MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref PREJ_ALLOWED); LABEL_TAC name safety_th]);;

let PREJ_SAFE_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (1--6) THEN REJ_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC [7] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (8--14) THEN REJ_NORMALIZE_TAC THEN
  PREJ_SAFE_CALL_TAC "H_INIT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (16--19) THEN REJ_NORMALIZE_TAC THEN
  REJ_GOT_TAC THEN
  PREJ_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `34`;
    `num_of_bytelist(inp:byte list)`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 20 THEN REJ_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (21--25) THEN REJ_NORMALIZE_TAC THEN
  PREJ_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `3`; `read X2 s`; `S0:1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] 26 THEN REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (27--28) THEN
  REJ_NORMALIZE_TAC THEN REJ_INPUT0_TAC `s28:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PREJ_DISCHARGE_TAC;;

let PREJ_SAFE_LOOP1_TAC =
  ASSUME_TAC(INST_TYPE [`:12`,`:N`] (ISPECL
   [`336`; `num_of_bytelist(list_of_seq (shake128 inp) 504)`]
   LENGTH_WORDLIST_OF_NUM)) THEN
  PREJ_SAFE_CALL_TAC "H_LOOP1"
   [`e:(uarch_event)list`; `read X19 s`; `0`; `read X21 s`; `504`;
    `wordlist_of_num 336 (num_of_bytelist(list_of_seq (shake128 inp) 504)):
     (12 word)list`; `pc:num`] 1 THEN
  REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(entry,n) s = l:int16 list`) o
    concl));;

let PREJ_SAFE_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ_SAFE_LOOP1_TAC THEN
  REJ_EXIT_COND_TAC REJ_C0 `T` THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),`256`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`shake128 inp`; `0`; `k:num`] REJ_SAMPLE_FINAL) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[] THEN PREJ_DISCHARGE_TAC;;

let PREJ_SAFE_ENTER_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ_E2_TAC THEN
  PREJ_SAFE_LOOP1_TAC THEN
  REJ_EXIT_COND_TAC REJ_C0 `F` THEN
  REJ_MIN_FACT_TAC REJ_C0 THEN
  REJ_BR_STEPS_TAC [2;3;4;5] THEN
  REJ_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REJ_MIN_TAC THEN ASM_REWRITE_TAC[] THEN
  PREJ_DISCHARGE_TAC;;

let PREJ_SUB_LIST_256 = prove
 (`!l:(16 word)list. LENGTH(SUB_LIST(0,256) l) <= 256`,
  REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

let PREJ_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` (rej_count `i:num`) `256`)
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  REJ_MIN_TAC THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (1--4) THEN REJ_NORMALIZE_TAC THEN
  KECCAK_STATE_AT_TAC REJ_CTX THEN
  PREJ_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `1`; `read X2 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `pc:num`; `read SP s`; `read X30 s`] 5 THEN REJ_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  ABBREV_TAC (mk_eq(`ci:num`,rej_count `i:num`)) THEN
  SUBGOAL_THEN `ci <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `ci < 256` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC [6] THEN
  REJ_BLOCK_TAC `s6:armstate` THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rej_block `i:num`)] LENGTH_WORDLIST_OF_NUM)) THEN
  PREJ_SAFE_CALL_TAC "H_LOOP3"
   [`e:(uarch_event)list`; `read X19 s`; `ci:num`; `read X21 s`; `168`;
    rej_block `i:num`; `pc:num`] 7 THEN
  REJ_COMBINE_TAC `s7:armstate` THEN
  REJ_LS_TAC THEN
  REJ_ENDBODY_STEPS_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `ci:num`))) THEN
  ASSUME_TAC(SPEC(mk_comb(`REJ_SAMPLE:(12 word)list->(16 word)list`,
                          rej_fields `i:num`)) PREJ_SUB_LIST_256) THEN
  REJ_DECIDE_CONDS_TAC THEN REJ_DECIDE_CONDS_TAC THEN
  PREJ_DISCHARGE_TAC;;

let PREJ_SAFE_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` REJ_C0 `256`) ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NOT_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + mlkem_poly_rej_uniform_loop2`
   `pc + mlkem_poly_rej_uniform_loop2_exit` REJ_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    PREJ_SAFE_ENTER_TAC;
    PREJ_SAFE_BODY_TAC;
    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rej_count `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    MP_TAC(ISPECL [`shake128 inp`; `k0:num`; `k:num`] REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PREJ_DISCHARGE_TAC];;

let PREJ_SAFE_PART3_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (1--2) THEN REJ_NORMALIZE_TAC THEN
  PREJ_SAFE_CALL_TAC "H_RELEASE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 3 THEN REJ_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (4--23) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_EXEC (24--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && lhs(concl th) = `e2:(uarch_event)list`
    then REWRITE_RULE[ADD_ASSOC] th else th) THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  PREJ_DISCHARGE_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e entry seed (inp:byte list) k guard pc stackpointer
               returnaddress.
         aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
         aligned 16 stackpointer /\ LENGTH inp = 34 /\
         256 <= LENGTH(FILTER (\x. val x < 3329)
                        (MAP (word_zx:12 word->16 word)
                          (wordlist_of_num (336 + 112 * k)
                            (num_of_bytelist
                              (list_of_seq (shake128 inp)
                                           (504 + 168 * k)))))) /\
         nonoverlapping (entry,512) (word_sub stackpointer (word 1120),1120) /\
         ALLPAIRS nonoverlapping
          [(entry,512); (word_sub stackpointer (word 1120),1120)]
          [(seed,34); (word pc,libmlkem_size);
           (word(pc + got_stack_chk_guard),8); (guard,8);
           (word(pc + got_memset),8); (ea,el)]
         ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_clang17_O2_mc /\
                   read PC s = word (pc + mlkem_poly_rej_uniform) /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [entry; seed] s /\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                     guard /\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                   read (memory :> bytes(ea,el)) s = ev /\
                   read (memory :> bytes(seed,34)) s = num_of_bytelist inp /\
                   read events s = e)
              (\s. read PC s = returnaddress /\
                   (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events entry seed inp guard mf pc
                             (word_sub stackpointer (word 1120))
                             returnaddress /\
                      memaccess_inbounds e2
                       [seed,34; entry,512;
                        word_sub stackpointer (word 1120),1120;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8;
                        ea,el;
                        word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                       [entry,512; word_sub stackpointer (word 1120),1120]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
               MAYCHANGE
                [memory :> bytes(entry,512);
                 memory :> bytes(word_sub stackpointer (word 1120),1120)])`;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
