(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of data into four Keccak states. This is the code for                 *)
(* mlkem_keccakf1600x4_xor_bytes from mlkem-native's portable C              *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md),*)
(* which XORs len bytes of each of four inputs into its 200-byte state,      *)
(* starting at byte off. Where gcc calls mlkem_keccakf1600_xor_bytes for     *)
(* each state, clang has inlined four copies of its code, each with the two  *)
(* tests of overlap and the three loops (blocks of 32 bytes, blocks of 8     *)
(* bytes, single bytes) described in keccakf1600_xor_bytes.ml, so it uses no *)
(* stack. The copies differ in their registers and address arithmetic, but   *)
(* the same tactics, parametrized by the copy, verify all four, as in        *)
(* keccakf1600x4_extract_bytes.ml. The specifications are those for gcc      *)
(* without the stack frame. It is verified in the whole image (see           *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600_xor_bytes.ml";;
needs "arm/proofs/mlkem_native/copies.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600x4_xor_bytes:
      +0x0: cbz     w6, join12
      +0x4: mov     w8, w5
      +0x8: mov     w9, w6
      +0xc: cmp     w6, #0x8
     +0x10: b.cc    join1
     +0x14: add     x10, x0, x8
     +0x18: add     x11, x1, x9
     +0x1c: cmp     x10, x11
     +0x20: b.cs    join13
     +0x24: add     x10, x9, x8
     +0x28: add     x10, x0, x10
     +0x2c: cmp     x10, x1
     +0x30: b.ls    join13
     +0x34: mov     x10, xzr
     +0x38: add     x12, x0, x10
     +0x3c: sub     x11, x9, x10
     +0x40: add     x12, x12, x8
     +0x44: add     x10, x1, x10
     +0x48: ldrb    w13, [x10], #1
     +0x4c: ldrb    w14, [x12]
     +0x50: subs    x11, x11, #0x1
     +0x54: eor     w13, w14, w13
     +0x58: strb    w13, [x12], #1
     +0x5c: b.ne    loop1
     +0x60: cmp     w6, #0x8
     +0x64: b.cc    join4
     +0x68: add     x10, x0, x8
     +0x6c: add     x11, x2, x9
     +0x70: add     x10, x10, #0xc8
     +0x74: cmp     x10, x11
     +0x78: b.cs    join14
     +0x7c: add     x10, x9, x8
     +0x80: add     x10, x10, x0
     +0x84: add     x10, x10, #0xc8
     +0x88: cmp     x10, x2
     +0x8c: b.ls    join14
     +0x90: mov     x10, xzr
     +0x94: add     x12, x10, x8
     +0x98: sub     x11, x9, x10
     +0x9c: add     x12, x12, x0
     +0xa0: add     x10, x2, x10
     +0xa4: add     x12, x12, #0xc8
     +0xa8: ldrb    w13, [x10], #1
     +0xac: ldrb    w14, [x12]
     +0xb0: subs    x11, x11, #0x1
     +0xb4: eor     w13, w14, w13
     +0xb8: strb    w13, [x12], #1
     +0xbc: b.ne    loop2
     +0xc0: cmp     w6, #0x8
     +0xc4: b.cc    join7
     +0xc8: add     x10, x0, x8
     +0xcc: add     x11, x3, x9
     +0xd0: add     x10, x10, #0x190
     +0xd4: cmp     x10, x11
     +0xd8: b.cs    join15
     +0xdc: add     x10, x9, x8
     +0xe0: add     x10, x10, x0
     +0xe4: add     x10, x10, #0x190
     +0xe8: cmp     x10, x3
     +0xec: b.ls    join15
     +0xf0: mov     x10, xzr
     +0xf4: add     x12, x10, x8
     +0xf8: sub     x11, x9, x10
     +0xfc: add     x12, x12, x0
    +0x100: add     x10, x3, x10
    +0x104: add     x12, x12, #0x190
    +0x108: ldrb    w13, [x10], #1
    +0x10c: ldrb    w14, [x12]
    +0x110: subs    x11, x11, #0x1
    +0x114: eor     w13, w14, w13
    +0x118: strb    w13, [x12], #1
    +0x11c: b.ne    loop3
    +0x120: cmp     w6, #0x8
    +0x124: b.cc    join10
    +0x128: add     x10, x0, x8
    +0x12c: add     x11, x10, #0x258
    +0x130: add     x10, x4, x9
    +0x134: cmp     x11, x10
    +0x138: b.cs    join16
    +0x13c: add     x10, x9, x8
    +0x140: add     x10, x10, x0
    +0x144: add     x10, x10, #0x258
    +0x148: cmp     x10, x4
    +0x14c: b.ls    join16
    +0x150: mov     x10, xzr
    +0x154: add     x11, x10, x8
    +0x158: sub     x8, x9, x10
    +0x15c: add     x9, x11, x0
    +0x160: add     x10, x4, x10
    +0x164: add     x9, x9, #0x258
    +0x168: ldrb    w11, [x10], #1
    +0x16c: ldrb    w12, [x9]
    +0x170: subs    x8, x8, #0x1
    +0x174: eor     w11, w12, w11
    +0x178: strb    w11, [x9], #1
    +0x17c: b.ne    loop4
    +0x180: ret
    +0x184: cmp     w6, #0x20
    +0x188: b.cs    +0x1c4
    +0x18c: mov     x10, xzr
    +0x190: b       join17
    +0x194: cmp     w6, #0x20
    +0x198: b.cs    +0x248
    +0x19c: mov     x10, xzr
    +0x1a0: b       join18
    +0x1a4: cmp     w6, #0x20
    +0x1a8: b.cs    +0x2d0
    +0x1ac: mov     x10, xzr
    +0x1b0: b       join19
    +0x1b4: cmp     w6, #0x20
    +0x1b8: b.cs    +0x358
    +0x1bc: mov     x10, xzr
    +0x1c0: b       join20
    +0x1c4: and     x10, x9, #0xffffffe0
    +0x1c8: add     x12, x8, x0
    +0x1cc: add     x11, x1, #0x10
    +0x1d0: add     x12, x12, #0x10
    +0x1d4: mov     x13, x10
    +0x1d8: ldp     q0, q1, [x11, #-16]
    +0x1dc: add     x11, x11, #0x20
    +0x1e0: subs    x13, x13, #0x20
    +0x1e4: ldp     q2, q3, [x12, #-16]
    +0x1e8: eor     v0.16b, v2.16b, v0.16b
    +0x1ec: eor     v1.16b, v3.16b, v1.16b
    +0x1f0: stp     q0, q1, [x12, #-16]
    +0x1f4: add     x12, x12, #0x20
    +0x1f8: b.ne    loop5
    +0x1fc: cmp     x10, x9
    +0x200: b.eq    join3
    +0x204: tst     x9, #0x18
    +0x208: b.eq    join2
    +0x20c: mov     x13, x10
    +0x210: and     x10, x9, #0xfffffff8
    +0x214: add     x12, x0, x13
    +0x218: add     x11, x1, x13
    +0x21c: add     x12, x12, x8
    +0x220: sub     x13, x13, x10
    +0x224: ldr     d0, [x11], #8
    +0x228: ldr     d1, [x12]
    +0x22c: adds    x13, x13, #0x8
    +0x230: eor     v0.8b, v1.8b, v0.8b
    +0x234: str     d0, [x12], #8
    +0x238: b.ne    loop6
    +0x23c: cmp     x10, x9
    +0x240: b.eq    join3
    +0x244: b       join2
    +0x248: and     x10, x9, #0xffffffe0
    +0x24c: add     x12, x8, x0
    +0x250: add     x11, x2, #0x10
    +0x254: add     x12, x12, #0xd8
    +0x258: mov     x13, x10
    +0x25c: ldp     q0, q1, [x11, #-16]
    +0x260: add     x11, x11, #0x20
    +0x264: subs    x13, x13, #0x20
    +0x268: ldp     q2, q3, [x12, #-16]
    +0x26c: eor     v0.16b, v2.16b, v0.16b
    +0x270: eor     v1.16b, v3.16b, v1.16b
    +0x274: stp     q0, q1, [x12, #-16]
    +0x278: add     x12, x12, #0x20
    +0x27c: b.ne    loop7
    +0x280: cmp     x10, x9
    +0x284: b.eq    join6
    +0x288: tst     x9, #0x18
    +0x28c: b.eq    join5
    +0x290: mov     x13, x10
    +0x294: and     x10, x9, #0xfffffff8
    +0x298: add     x12, x13, x8
    +0x29c: add     x11, x2, x13
    +0x2a0: add     x12, x12, x0
    +0x2a4: sub     x13, x13, x10
    +0x2a8: add     x12, x12, #0xc8
    +0x2ac: ldr     d0, [x11], #8
    +0x2b0: ldr     d1, [x12]
    +0x2b4: adds    x13, x13, #0x8
    +0x2b8: eor     v0.8b, v1.8b, v0.8b
    +0x2bc: str     d0, [x12], #8
    +0x2c0: b.ne    loop8
    +0x2c4: cmp     x10, x9
    +0x2c8: b.eq    join6
    +0x2cc: b       join5
    +0x2d0: and     x10, x9, #0xffffffe0
    +0x2d4: add     x12, x8, x0
    +0x2d8: add     x11, x3, #0x10
    +0x2dc: add     x12, x12, #0x1a0
    +0x2e0: mov     x13, x10
    +0x2e4: ldp     q0, q1, [x11, #-16]
    +0x2e8: add     x11, x11, #0x20
    +0x2ec: subs    x13, x13, #0x20
    +0x2f0: ldp     q2, q3, [x12, #-16]
    +0x2f4: eor     v0.16b, v2.16b, v0.16b
    +0x2f8: eor     v1.16b, v3.16b, v1.16b
    +0x2fc: stp     q0, q1, [x12, #-16]
    +0x300: add     x12, x12, #0x20
    +0x304: b.ne    loop9
    +0x308: cmp     x10, x9
    +0x30c: b.eq    join9
    +0x310: tst     x9, #0x18
    +0x314: b.eq    join8
    +0x318: mov     x13, x10
    +0x31c: and     x10, x9, #0xfffffff8
    +0x320: add     x12, x13, x8
    +0x324: add     x11, x3, x13
    +0x328: add     x12, x12, x0
    +0x32c: sub     x13, x13, x10
    +0x330: add     x12, x12, #0x190
    +0x334: ldr     d0, [x11], #8
    +0x338: ldr     d1, [x12]
    +0x33c: adds    x13, x13, #0x8
    +0x340: eor     v0.8b, v1.8b, v0.8b
    +0x344: str     d0, [x12], #8
    +0x348: b.ne    loop10
    +0x34c: cmp     x10, x9
    +0x350: b.eq    join9
    +0x354: b       join8
    +0x358: and     x10, x9, #0xffffffe0
    +0x35c: add     x12, x4, #0x10
    +0x360: mov     x13, x10
    +0x364: ldp     q0, q1, [x12, #-16]
    +0x368: add     x12, x12, #0x20
    +0x36c: subs    x13, x13, #0x20
    +0x370: ldp     q2, q3, [x11]
    +0x374: eor     v0.16b, v2.16b, v0.16b
    +0x378: eor     v1.16b, v3.16b, v1.16b
    +0x37c: stp     q0, q1, [x11], #32
    +0x380: b.ne    loop11
    +0x384: cmp     x10, x9
    +0x388: b.eq    join12
    +0x38c: tst     x9, #0x18
    +0x390: b.eq    join11
    +0x394: mov     x13, x10
    +0x398: and     x10, x9, #0xfffffff8
    +0x39c: add     x12, x13, x8
    +0x3a0: add     x11, x4, x13
    +0x3a4: add     x12, x12, x0
    +0x3a8: sub     x13, x13, x10
    +0x3ac: add     x12, x12, #0x258
    +0x3b0: ldr     d0, [x11], #8
    +0x3b4: ldr     d1, [x12]
    +0x3b8: adds    x13, x13, #0x8
    +0x3bc: eor     v0.8b, v1.8b, v0.8b
    +0x3c0: str     d0, [x12], #8
    +0x3c4: b.ne    loop12
    +0x3c8: cmp     x10, x9
    +0x3cc: b.eq    join12
    +0x3d0: b       join11
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_keccakf1600x4_xor_bytes"];;

let XOR4_EXEC = MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The four copies of the code of mlkem_keccakf1600_xor_bytes. Copy k XORs   *)
(* the len bytes at dk into state k, at a + 200 * k, from byte off. Each has *)
(* a loop of single bytes (loop k + 1), the tests of overlap, which jump to  *)
(* join(13 + k) where the vectorized code starts, a loop of blocks of 32     *)
(* bytes (loop 5 + 2 * k) and a loop of blocks of 8 bytes (loop 6 + 2 * k),  *)
(* and ends at the next copy (join3, join6, join9) or at the return. They    *)
(* differ in the registers of the loop of single bytes (data, state and      *)
(* counter) and of the loop of 32 bytes (data and state; in copy 3 the       *)
(* state pointer is post-incremented), and in the numbers of instructions of *)
(* the paths, recorded as (b1,b2,j1,j2,a3,v2,t21,t3,t31,v2body): from the    *)
(* start of the copy to the loop of single bytes when len <= 7 or after the  *)
(* two tests of overlap, to join(13 + k) after the first or the second test, *)
(* from there to the loop of 8 bytes or of 32 bytes, from the end of the     *)
(* loop of 32 bytes to the loop of single bytes or of 8 bytes, from the end  *)
(* of the loop of 8 bytes to that of single bytes, and the length of the     *)
(* body of the loop of 32 bytes.                                             *)
(* ------------------------------------------------------------------------- *)

type xor4_block =
  { xk : int; xdat : string; xst : string; xcnt : string;
    xvdat : string; xvst : string;
    xsteps : int * int * int * int * int * int * int * int * int * int };;

let xor4_blocks =
  [{xk = 0; xdat = "X10"; xst = "X12"; xcnt = "X11";
    xvdat = "X11"; xvst = "X12"; xsteps = (10,18,9,13,10,7,8,10,7,9)};
   {xk = 1; xdat = "X10"; xst = "X12"; xcnt = "X11";
    xvdat = "X11"; xvst = "X12"; xsteps = (8,18,7,12,11,7,9,11,8,9)};
   {xk = 2; xdat = "X10"; xst = "X12"; xcnt = "X11";
    xvdat = "X11"; xvst = "X12"; xsteps = (8,18,7,12,11,7,9,11,8,9)};
   {xk = 3; xdat = "X10"; xst = "X9"; xcnt = "X8";
    xvdat = "X12"; xvst = "X11"; xsteps = (8,18,7,12,11,5,9,11,8,8)}];;

let xor4_label l = parse_term("pc + mlkem_keccakf1600x4_xor_bytes_" ^ l);;
let xor4_lb b = "loop" ^ string_of_int(b.xk + 1);;
let xor4_l32 b = "loop" ^ string_of_int(5 + 2 * b.xk);;
let xor4_l8 b = "loop" ^ string_of_int(6 + 2 * b.xk);;
let xor4_jv b = "join" ^ string_of_int(13 + b.xk);;

let xor4_ks k = string_of_int k;;
let xor4_base_str k =
  if k = 0 then "(a:int64)"
  else "word_add (a:int64) (word " ^ string_of_int(200 * k) ^ ")";;
let xor4_base k = parse_term(xor4_base_str k);;
let xor4_d k = mk_var("d" ^ xor4_ks k,`:int64`);;
let xor4_s k = mk_var("S" ^ xor4_ks k,`:1600 word`);;
let xor4_m k = mk_var("m" ^ xor4_ks k,`:num`);;

(*** The address a + 200 * k + ofs in the form of the simulation ***)

let xor4_src_str k ofs =
  if k = 0 then "word_add (a:int64) (word(" ^ ofs ^ "))"
  else "word_add (a:int64) (word(" ^ string_of_int(200 * k) ^ " + " ^
       ofs ^ "))";;

let xor4_conj l = String.concat " /\\ " l;;

let xor4_common =
  ["read X0 s = (a:int64)"; "read X1 s = (d0:int64)"; "read X2 s = (d1:int64)";
   "read X3 s = (d2:int64)"; "read X4 s = (d3:int64)"; "read X6 s = word len";
   "read X30 s = (returnaddress:int64)"];;

let xor4_offlen = ["read X8 s = word off"; "read X9 s = word len"];;

let xor4_fs k =
  "val(word_xor (S" ^ xor4_ks k ^ ":1600 word) (word(2 EXP (8 * off) * m" ^
  xor4_ks k ^ ")))";;

let xor4_state_old j =
  "read (memory :> bytes(" ^ xor4_base_str j ^ ",200)) s = val(S" ^
  xor4_ks j ^ ":1600 word)";;

let xor4_state_new j =
  "read (memory :> bytes(" ^ xor4_base_str j ^ ",200)) s = " ^ xor4_fs j;;

let xor4_data j =
  "read (memory :> bytes(d" ^ xor4_ks j ^ ",len)) s = m" ^ xor4_ks j;;

(*** State k after the bytes before byte p (a string) are done ***)

let xor4_split k p =
  ["read (memory :> bytes(" ^ xor4_base_str k ^ "," ^ p ^ ")) s = " ^
   xor4_fs k ^ " MOD 2 EXP (8 * (" ^ p ^ "))";
   "read (memory :> bytes(word_add (" ^ xor4_base_str k ^ ") (word(" ^ p ^
   ")),200 - (" ^ p ^ "))) s = val(S" ^ xor4_ks k ^ ":1600 word) DIV " ^
   "2 EXP (8 * (" ^ p ^ "))"];;

(*** The facts kept by copy k: the other states and all the data ***)

let xor4_frame k =
  xor4_common @ map xor4_state_new (0--(k-1)) @
  map xor4_state_old ((k+1)--3) @ map xor4_data (0--3);;

(*** The invariant at the start of copy j and at the return ***)

let XOR4_INV j =
  parse_term("\\s:armstate. " ^ xor4_conj
   (xor4_common @ map xor4_state_new (0--(j-1)) @
    map xor4_state_old (j--3) @ map xor4_data (0--3) @
    (if j < 4 then xor4_offlen else [])));;

(* ------------------------------------------------------------------------- *)
(* The events, by path as for mlkem_keccakf1600_xor_bytes, per copy. The two *)
(* tests of overlap are in the form that the code computes them.             *)
(* ------------------------------------------------------------------------- *)

let xor4_c1 k =
  let d = "(d" ^ xor4_ks k ^ ":int64)" in
  if k = 0 then
    "val(word_add " ^ d ^ " (word len)) <= val(word_add (a:int64) (word off))"
  else
    "val(word_add " ^ d ^ " (word len)) <= " ^
    "val(word_add (word_add (a:int64) (word off)) (word " ^
    string_of_int(200 * k) ^ "))";;

let xor4_c2 k =
  let d = "(d" ^ xor4_ks k ^ ":int64)" in
  if k = 0 then
    "val(word_add (a:int64) (word(len + off))) <= val " ^ d
  else
    "val(word_add (word_add (word(len + off)) (a:int64)) (word " ^
    string_of_int(200 * k) ^ ")) <= val " ^ d;;

let XOR4_EVENTS_TERM =
  let args = "a d0 d1 d2 d3 off len pc returnaddress" in
  let ev nm = "f_ev_" ^ nm ^ " " ^ args in
  let byteloop p cnt =
    "APPEND (" ^ ev (p ^ "e") ^ ") (APPEND (ENUMERATEL (" ^ cnt ^
    ") (\\i. " ^ ev (p ^ "l") ^ " i)) (" ^ ev (p ^ "p") ^ "))" in
  let tail3 p =
    "(if len MOD 8 = 0 then " ^ ev (p ^ "0") ^ " else " ^
    byteloop (p ^ "1") "len MOD 8" ^ ")" in
  let loop3 p cnt =
    "APPEND " ^ tail3 (p ^ "t") ^ " (APPEND (" ^ ev (p ^ "e") ^
    ") (APPEND (ENUMERATEL (" ^ cnt ^ ") (\\i. " ^ ev (p ^ "l") ^
    " i)) (" ^ ev (p ^ "p") ^ ")))" in
  let block k =
    let p = "k" ^ xor4_ks k ^ "_" in
    let tail2 =
      "(if len MOD 32 = 0 then " ^ ev (p ^ "t20") ^
      " else if len MOD 32 < 8 then " ^ byteloop (p ^ "t21") "len MOD 32" ^
      " else " ^ loop3 (p ^ "t3") "(len MOD 32) DIV 8" ^ ")" in
    let vec =
      "(if len < 32 then " ^ loop3 (p ^ "a3") "len DIV 8" ^
      " else APPEND " ^ tail2 ^ " (APPEND (" ^ ev (p ^ "v2e") ^
      ") (APPEND (ENUMERATEL (len DIV 32) (\\i. " ^ ev (p ^ "v2l") ^
      " i)) (" ^ ev (p ^ "v2p") ^ "))))" in
    "(if len <= 7 then " ^ byteloop (p ^ "b1") "len" ^
    " else if " ^ xor4_c1 k ^ " \\/ " ^ xor4_c2 k ^ " then APPEND " ^ vec ^
    " (if " ^ xor4_c1 k ^ " then " ^ ev (p ^ "j1") ^ " else " ^
    ev (p ^ "j2") ^ ") else " ^ byteloop (p ^ "b2") "len" ^ ")" in
  parse_term
   ("\\(a:int64) (d0:int64) (d1:int64) (d2:int64) (d3:int64) (off:num) " ^
    "(len:num) (pc:num) (returnaddress:int64). " ^
    "if len = 0 then " ^ ev "len0" ^ " else APPEND (" ^ ev "ret" ^
    ") (APPEND " ^ block 3 ^ " (APPEND " ^ block 2 ^ " (APPEND " ^
    block 1 ^ " " ^ block 0 ^ "))) :(uarch_event)list");;

(* ------------------------------------------------------------------------- *)
(* Steps, branches and the arithmetic on the words of the state.             *)
(* ------------------------------------------------------------------------- *)

let XOR4_STEP_TAC n =
  ARM_STEPS_TAC XOR4_EXEC [n] THEN
  XOR_NORM_TAC THEN XOR_FOLD_TAC THEN
  TRY XOR_W32_DECIDE_TAC THEN XOR_BRANCH_TAC;;

(*** The last test of overlap, b.ls ***)

let XOR4_LS_STEP_TAC n =
  ARM_STEPS_TAC XOR4_EXEC [n] THEN
  COPIES_STATE_RULE_TAC(REWRITE_RULE[XOR_LS_LEMMA]) THEN XOR_BRANCH_TAC;;

(*** The steps from the start of copy k ***)

let XOR4_ENTRY_TAC b n =
  if b.xk = 0 then
    ARM_STEPS_TAC XOR4_EXEC (1--1) THEN XOR_ARGS_TAC THEN
    ARM_STEPS_TAC XOR4_EXEC (2--3) THEN MAP_EVERY XOR4_STEP_TAC (4--n)
  else MAP_EVERY XOR4_STEP_TAC (1--n);;

let XOR4_WORD_TAC =
  (REWRITE_TAC[WORD_SUB_MOD32; WORD_SUB_MOD8] THEN
   REWRITE_TAC[WORD_ADD; ADD_CLAUSES; WORD_ADD_0] THEN
   CONV_TAC WORD_RULE) ORELSE
  (AP_TERM_TAC THEN ARITH_TAC);;

let XOR4_CLOSE_TAC ths =
  REWRITE_TAC ths THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  XOR4_WORD_TAC;;

(*** State k split at byte off + 0, from the start state ***)

let XOR4_START_TAC k =
  MP_TAC(SPECL [xor4_base k; xor4_s k; xor4_m k; `off:num`; `s0:armstate`]
               XOR_START) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  COPIES_STATE_RULE_TAC(REWRITE_RULE[ADD_CLAUSES]);;

(*** The rest of state k from byte p' on, before the stores ***)

let XOR4_REST_TAC k p p' =
  MP_TAC(SPECL [xor4_base k; mk_comb(`val:1600 word->num`,xor4_s k);
                p; p'; `s0:armstate`] XOR_REST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** The loads of state k at byte q, given the state from byte p on, in   ***)
(*** the address form of the simulation, and of the data at byte j. For   ***)
(*** the second register of an LDP of Q registers (kind 129) the state is ***)
(*** at (200 * k + q) + 16 with q given.                                  ***)

let XOR4_LD k kind p q j =
  let s = `s0:armstate` in
  let lth,dth =
    match kind with
      1 -> XOR_LOAD8,READ_MEMORY_BYTES8_OF_NUM
    | 8 -> XOR_LOAD64,READ_MEMORY_BYTES64_OF_NUM
    | _ -> XOR_LOAD128,READ_MEMORY_BYTES128_OF_NUM in
  let q' = if kind = 129 then mk_binop `(+):num->num->num` q `16` else q in
  let flat =
    if k = 0 then mk_comb(`word_add (a:int64)`,mk_comb(`word:num->int64`,q'))
    else
      let b = mk_small_numeral(200 * k) in
      let ofs = if kind = 129 then
                mk_binop `(+):num->num->num`
                 (mk_binop `(+):num->num->num` b q) `16`
              else mk_binop `(+):num->num->num` b q in
      mk_comb(`word_add (a:int64)`,mk_comb(`word:num->int64`,ofs)) in
  let fix th =
    let x = rand(rand(rand(rator(lhand(concl th))))) in
    if x = flat then th else
    ONCE_REWRITE_RULE[COPIES_ADDR_EQ x flat] th in
  MP_TAC(SPECL [xor4_base k; mk_comb(`val:1600 word->num`,xor4_s k);
                p; q'; s] lth) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(ASSUME_TAC o fix)] THEN
  MP_TAC(SPECL [xor4_d k; `len:num`; xor4_m k; j; s] dth) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** After a store of sz bytes at byte off + j of state k, those bytes as ***)
(*** a number at a + 200 * k + (off + j), as the bytes of the final state ***)

let XOR4_STORE_TAC k j sz =
  let base = xor4_base k and sk = xor4_s k and mk = xor4_m k in
  let ix = mk_binop `(+):num->num->num` `off:num` j in
  let nested = mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
                       mk_comb(`word:num->int64`,ix)) in
  let pat,bth,cth =
    match sz with
      1 -> `read (memory :> bytes8 x) s = y`,
           READ_MEMORY_BYTES_OF_WORD8,XOR_CHUNK_1
    | 8 -> `read (memory :> bytes64 x) s = y`,
           READ_MEMORY_BYTES_OF_WORD64,XOR_CHUNK_8
    | _ -> `read (memory :> bytes128 x) s = y`,
           READ_MEMORY_BYTES_OF_WORD128,XOR_CHUNK_16 in
  let target = subst [sk,`S:1600 word`; mk,`m:num`; j,`j:num`;
                      mk_small_numeral sz,`k:num`]
   `(val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) DIV
     2 EXP (8 * (off + j))) MOD 2 EXP (8 * k)` in
  let addr_eq x =
    if x = nested then REFL x else
    prove(mk_eq(x,nested),
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_CLAUSES] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
  let is_xor t = can (find_term (fun u -> is_const u &&
                                          fst(dest_const u) = "word_xor")) t in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(can (term_match [] pat) c) || not(is_xor(rand c)) then NO_TAC else
    let x = rand(rand(rand(rator(lhand c)))) in
    match (try Some(addr_eq x) with Failure _ -> None) with
      None -> NO_TAC
    | Some eq ->
        let th1 = MATCH_MP bth th in
        let th2 = if x = nested then th1 else ONCE_REWRITE_RULE[eq] th1 in
        let w = rand c in
        let vw = mk_icomb(`val:N word->num`,w) in
        SUBGOAL_THEN (mk_eq(vw,target))
         (fun eth -> ASSUME_TAC(REWRITE_RULE[eth] th2)) THENL
         [MP_TAC(SPECL [sk; mk; `off:num`; j] cth) THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          AP_TERM_TAC THEN XOR_WORD_TAC;
          ALL_TAC]);;

(*** The bytes of state k up to byte off + jn, after those up to off + j ***)
(*** and the sz bytes from off + j                                       ***)

let XOR4_EXTEND_TAC k j sz jn =
  let base = xor4_base k in
  let ix j = mk_binop `(+):num->num->num` `off:num` j in
  let kt = mk_small_numeral sz in
  let pcomp = subst [base,`b:int64`; ix j,`P:num`] `memory :> bytes(b,P)`
  and ccomp = subst [base,`b:int64`; ix j,`P:num`; kt,`k:num`]
    `memory :> bytes(word_add (b:int64) (word P),k)` in
  let eth = ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` (ix j) kt,ix jn)) in
  let comp_of th =
    let c = concl th in
    if is_eq c && is_comb(lhs c) && is_comb(rator(lhs c))
    then rand(rator(lhs c)) else `F` in
  FIRST_ASSUM(fun pth ->
    if comp_of pth <> pcomp then NO_TAC else
    FIRST_ASSUM(fun cth ->
      if comp_of cth <> ccomp then NO_TAC else
      ASSUME_TAC(REWRITE_RULE[eth]
        (MATCH_MP READ_MEMORY_BYTES_EXTEND (CONJ pth cth)))));;

(*** The final state k, from the bytes up to off + lt and those after ***)

let XOR4_FINISH_STATE_TAC k lt =
  let base = xor4_base k in
  let ix = mk_binop `(+):num->num->num` `off:num` lt in
  let pcomp = subst [base,`b:int64`; ix,`P:num`] `memory :> bytes(b,P)` in
  let comp_of th =
    let c = concl th in
    if is_eq c && is_comb(lhs c) && is_comb(rator(lhs c))
    then rand(rator(lhs c)) else `F` in
  FIRST_ASSUM(fun pth ->
    if comp_of pth <> pcomp then NO_TAC else
    let s = rand(lhs(concl pth)) in
    MP_TAC(SPECL [base; xor4_d k; xor4_s k; xor4_m k; `off:num`; lt; s]
                 XOR_FINAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC]);;

(*** The end of copy k: the final state k, and the state at the next copy ***)

let XOR4_END_TAC k =
  XOR4_FINISH_STATE_TAC k `len:num` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop of single bytes of copy k, after n0 + i bytes, cnt in all.      *)
(* ------------------------------------------------------------------------- *)

let XOR4_INV1 b n0 cnt =
  let k = b.xk in
  let t = parse_term("\\(i:num) (s:armstate). " ^ xor4_conj
    (xor4_frame k @ (if k < 3 then xor4_offlen else []) @
     ["read " ^ b.xst ^ " s = " ^ xor4_src_str k "off + (n0 + i)";
      "read " ^ b.xcnt ^ " s = word(cnt - i)";
      "read " ^ b.xdat ^ " s = word_add d" ^ xor4_ks k ^ " (word(n0 + i))"] @
     xor4_split k "off + (n0 + i)")) in
  subst [n0,`n0:num`; cnt,`cnt:num`] t;;

let XOR4_BYTE_BODY b n0 cnt =
  let k = b.xk in
  let sb = subst [n0,`n0:num`; cnt,`cnt:num`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR4_LD k 1 (sb `off + (n0 + i)`) (sb `off + (n0 + i)`) (sb `n0 + i`) THEN
  XOR4_REST_TAC k (sb `off + (n0 + i)`) (sb `off + (n0 + (i + 1))`) THEN
  ARM_STEPS_TAC XOR4_EXEC (1--6) THEN
  BYTE_CNT_TAC cnt THEN
  XOR4_STORE_TAC k (sb `n0 + i`) 1 THEN
  XOR4_EXTEND_TAC k (sb `n0 + i`) 1 (sb `n0 + (i + 1)`) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (sb `~(i + 1 = cnt) <=> i + 1 < cnt`)
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC (sb `i < cnt`) THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [COPIES_SAFETY_TAC;
         COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
         XOR_PTR_EQ_TAC THEN NO_TAC;
         XOR4_WORD_TAC THEN NO_TAC];;

let XOR4_BYTE_EXIT k n0 cnt =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (subst [n0,`n0:num`; cnt,`cnt:num`] `n0 + cnt = len`)
    (fun th -> COPIES_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [ARITH_TAC; ALL_TAC] THEN
  XOR4_END_TAC k;;

let XOR4_BYTELOOP_TAC b n0 cnt (pos:tactic) (pro:tactic) =
  ENSURES_EVENTS_WHILE_UP2_TAC cnt (xor4_label(xor4_lb b))
   (xor4_label(xor4_lb b ^ "_exit")) (XOR4_INV1 b n0 cnt) THEN
  REPEAT CONJ_TAC THENL
   [pos; pro; XOR4_BYTE_BODY b n0 cnt; XOR4_BYTE_EXIT b.xk n0 cnt];;

(* ------------------------------------------------------------------------- *)
(* The loop of blocks of 32 bytes of copy k, len DIV 32 iterations.         *)
(* ------------------------------------------------------------------------- *)

let XOR4_INV2 b =
  let k = b.xk in
  parse_term("\\(i:num) (s:armstate). " ^ xor4_conj
   (xor4_frame k @ xor4_offlen @
    ["read X10 s = word(32 * (len DIV 32))";
     "read " ^ b.xvdat ^ " s = word_add (word_add d" ^ xor4_ks k ^
     " (word(32 * i))) (word 16)";
     (if k < 3 then
        "read " ^ b.xvst ^ " s = word_add (" ^
        xor4_src_str k "off + 32 * i" ^ ") (word 16)"
      else "read " ^ b.xvst ^ " s = " ^ xor4_src_str k "off + 32 * i");
     "read X13 s = word(32 * (len DIV 32 - i))"] @
    xor4_split k "off + 32 * i"));;

let XOR4_MIDV b =
  let k = b.xk in
  parse_term("\\(s:armstate). " ^ xor4_conj
   (xor4_frame k @ xor4_offlen @
    ["read X10 s = word(32 * (len DIV 32))"] @
    xor4_split k "off + 32 * (len DIV 32)"));;

let XOR4_V2_BODY b =
  let k = b.xk in
  let (_,_,_,_,_,_,_,_,_,nb) = b.xsteps in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * i + 32 <= len` ASSUME_TAC THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  XOR4_LD k 16 `off + 32 * i` `off + 32 * i` `32 * i` THEN
  XOR4_LD k 129 `off + 32 * i` `off + 32 * i` `32 * i + 16` THEN
  XOR4_REST_TAC k `off + 32 * i` `off + 32 * (i + 1)` THEN
  ARM_STEPS_TAC XOR4_EXEC (1--nb) THEN
  LOOP2_CNT_TAC THEN
  XOR4_STORE_TAC k `32 * i` 16 THEN
  XOR4_STORE_TAC k `32 * i + 16` 16 THEN
  XOR4_EXTEND_TAC k `32 * i` 16 `32 * i + 16` THEN
  XOR4_EXTEND_TAC k `32 * i + 16` 16 `32 * (i + 1)` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(i + 1 = len DIV 32) <=> i + 1 < len DIV 32`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [COPIES_SAFETY_TAC;
         COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[ARITH_RULE `off + 32 * (i + 1) = (off + 32 * i) + 32`;
                     ARITH_RULE `32 * (i + 1) = 32 * i + 32`; WORD_ADD] THEN
         CONV_TAC WORD_RULE THEN NO_TAC];;

(* ------------------------------------------------------------------------- *)
(* The loop of blocks of 8 bytes of copy k, after n0 bytes, k3 iterations.  *)
(* ------------------------------------------------------------------------- *)

let XOR4_INV3 b n0 k3 =
  let k = b.xk in
  let t = parse_term("\\(i:num) (s:armstate). " ^ xor4_conj
   (xor4_frame k @ xor4_offlen @
    ["read X10 s = word(n0 + 8 * k3)";
     "read X11 s = word_add d" ^ xor4_ks k ^ " (word(n0 + 8 * i))";
     "read X12 s = " ^ xor4_src_str k "off + (n0 + 8 * i)";
     "read X13 s = word_sub (word(n0 + 8 * i)) (word(n0 + 8 * k3))"] @
    xor4_split k "off + (n0 + 8 * i)")) in
  subst [n0,`n0:num`; k3,`k3:num`] t;;

let XOR4_MID3 b =
  let k = b.xk in
  parse_term("\\(s:armstate). " ^ xor4_conj
   (xor4_frame k @ xor4_offlen @
    ["read X10 s = word(8 * (len DIV 8))"] @
    xor4_split k "off + 8 * (len DIV 8)"));;

let XOR4_LOOP3_BODY b n0 k3 =
  let k = b.xk in
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 <= len`) ASSUME_TAC THENL
   [SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`) SUBST1_TAC THENL
     [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT));
             REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (sb `n0 + 8 * i + 8 <= len`) ASSUME_TAC THENL
   [UNDISCH_TAC (sb `n0 + 8 * k3 <= len`) THEN
    UNDISCH_TAC (sb `i < k3`) THEN
    SPEC_TAC(k3,`k:num`) THEN SPEC_TAC(n0,`m:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  XOR4_LD k 8 (sb `off + (n0 + 8 * i)`) (sb `off + (n0 + 8 * i)`)
    (sb `n0 + 8 * i`) THEN
  XOR4_REST_TAC k (sb `off + (n0 + 8 * i)`)
    (sb `off + (n0 + 8 * (i + 1))`) THEN
  ARM_STEPS_TAC XOR4_EXEC (1--6) THEN
  LOOP3_CNT_TAC n0 k3 THEN
  XOR4_STORE_TAC k (sb `n0 + 8 * i`) 8 THEN
  XOR4_EXTEND_TAC k (sb `n0 + 8 * i`) 8 (sb `n0 + 8 * (i + 1)`) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (sb `~(i + 1 = k3) <=> i + 1 < k3`)
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC (sb `i < k3`) THEN SPEC_TAC(k3,`k:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [COPIES_SAFETY_TAC;
         COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
         SPEC_TAC(n0,`m:num`) THEN ARITH_TAC;
         XOR4_WORD_TAC THEN NO_TAC];;

let XOR4_LOOP3_EXIT n0 k3 =
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`)
    (fun th -> COPIES_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT));
           REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR4_LOOP3_PHASE b n0 k3 (pos:tactic) (pro:tactic) (tail:tactic) =
  COPIES_POST_REASSOC_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC (xor4_label(xor4_l8 b ^ "_exit"))
    (XOR4_MID3 b) THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC k3 (xor4_label(xor4_l8 b))
      (xor4_label(xor4_l8 b ^ "_exit")) (XOR4_INV3 b n0 k3) THEN
    REPEAT CONJ_TAC THENL
     [pos; pro; XOR4_LOOP3_BODY b n0 k3; XOR4_LOOP3_EXIT n0 k3];
    tail];;

(* ------------------------------------------------------------------------- *)
(* The tails after the loops, and the paths of copy k.                      *)
(* ------------------------------------------------------------------------- *)

let XOR4_T30_TAC b =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `8 * (len DIV 8) = len`
    (fun th -> COPIES_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 8 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY XOR4_STEP_TAC (1--2) THEN
  XOR4_END_TAC b.xk;;

let XOR4_T31_PRO b =
  let (_,_,_,_,_,_,_,_,n,_) = b.xsteps in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (1--1) THEN TAIL3_CMP_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (2--n) THEN
  XOR_NORM_TAC THEN
  COPIES_FINISH_TAC
   (XOR4_CLOSE_TAC[ADD_0; SUB_0; WORD_SUB_MOD8]);;

let XOR4_TAIL3_TAC b =
  ASM_CASES_TAC `len MOD 8 = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR4_T30_TAC b;
    XOR4_BYTELOOP_TAC b `8 * (len DIV 8)` `(len MOD 8):num`
     (UNDISCH_TAC `~(len MOD 8 = 0)` THEN ARITH_TAC) (XOR4_T31_PRO b)];;

let XOR4_T20_TAC b =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * (len DIV 32) = len`
    (fun th -> COPIES_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 32 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY XOR4_STEP_TAC (1--2) THEN
  XOR4_END_TAC b.xk;;

let XOR4_T21_PRO b =
  let (_,_,_,_,_,_,n,_,_,_) = b.xsteps in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (1--1) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (2--3) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (4--n) THEN
  XOR_NORM_TAC THEN
  COPIES_FINISH_TAC
   (XOR4_CLOSE_TAC[ADD_CLAUSES; SUB_0; WORD_SUB_MOD32]);;

let XOR4_T3_PRO b =
  let (_,_,_,_,_,_,_,n,_,_) = b.xsteps in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (1--1) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (2--3) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (4--n) THEN
  XOR_NORM_TAC THEN
  COPIES_FINISH_TAC
   (TRY(ASM_SIMP_TAC[WORD_AND_FFFFFFF8_64]) THEN
    TRY(SUBST1_TAC(SPEC `len:num` DIV8_SPLIT)) THEN
    XOR4_CLOSE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0]);;

let XOR4_TAIL2_TAC b =
  ASM_CASES_TAC `len MOD 32 = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR4_T20_TAC b; ALL_TAC] THEN
  ASM_CASES_TAC `len MOD 32 < 8` THEN ASM_REWRITE_TAC[] THENL
   [XOR4_BYTELOOP_TAC b `32 * (len DIV 32)` `(len MOD 32):num`
      (UNDISCH_TAC `~(len MOD 32 = 0)` THEN ARITH_TAC) (XOR4_T21_PRO b);
    XOR4_LOOP3_PHASE b `32 * (len DIV 32)` `(len MOD 32) DIV 8`
      (UNDISCH_TAC `~(len MOD 32 < 8)` THEN
       SPEC_TAC(`len MOD 32`,`r:num`) THEN ARITH_TAC)
      (XOR4_T3_PRO b) (XOR4_TAIL3_TAC b)];;

(*** From join(13 + k) to the loop of 8 bytes or of 32 bytes ***)

let XOR4_VPRO_TAC b n =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR4_START_TAC b.xk THEN
  MAP_EVERY XOR4_STEP_TAC (1--n) THEN
  COPIES_FINISH_TAC
   (TRY(ASM_SIMP_TAC[WORD_AND_FFFFFFE0_64; WORD_AND_FFFFFFF8_64]) THEN
    XOR4_CLOSE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; SUB_0]);;

let XOR4_PATH_A_TAC b =
  let (_,_,_,_,n,_,_,_,_,_) = b.xsteps in
  XOR4_LOOP3_PHASE b `0` `len DIV 8`
    (UNDISCH_TAC `~(len <= 7)` THEN ARITH_TAC)
    (XOR4_VPRO_TAC b n) (XOR4_TAIL3_TAC b);;

let XOR4_V2_EXIT =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR4_PATH_B_TAC b =
  let (_,_,_,_,_,n,_,_,_,_) = b.xsteps in
  COPIES_POST_REASSOC_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC (xor4_label(xor4_l32 b ^ "_exit"))
    (XOR4_MIDV b) THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 32` (xor4_label(xor4_l32 b))
      (xor4_label(xor4_l32 b ^ "_exit")) (XOR4_INV2 b) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(len < 32)` THEN ARITH_TAC;
      XOR4_VPRO_TAC b n; XOR4_V2_BODY b; XOR4_V2_EXIT];
    XOR4_TAIL2_TAC b];;

(*** From the start of the copy to the loop of single bytes ***)

let XOR4_BPRO_TAC b n =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR4_START_TAC b.xk THEN
  XOR4_ENTRY_TAC b n THEN
  COPIES_FINISH_TAC
   (XOR4_CLOSE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0]);;

let XOR4_B2PRO_TAC b n =
  let (_,_,_,j2,_,_,_,_,_,_) = b.xsteps in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR4_START_TAC b.xk THEN
  FIRST_X_ASSUM(fun th ->
    if is_neg(concl th) && is_disj(dest_neg(concl th))
    then STRIP_ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM] th) else NO_TAC) THEN
  XOR4_ENTRY_TAC b (j2 - 1) THEN XOR4_LS_STEP_TAC j2 THEN
  MAP_EVERY XOR4_STEP_TAC ((j2+1)--n) THEN
  COPIES_FINISH_TAC
   (XOR4_CLOSE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0]);;

(*** From the start of the copy to join(13 + k) after the tests ***)

let XOR4_MIDJ b =
  let k = b.xk in
  parse_term("\\(s:armstate). " ^ xor4_conj
   (xor4_common @ map xor4_state_new (0--(k-1)) @
    map xor4_state_old (k--3) @ map xor4_data (0--3) @ xor4_offlen @
    (if k = 3 then
       ["read X11 s = word_add (word_add (a:int64) (word off)) (word 600)"]
     else [])));;

let XOR4_J_TAC b =
  let (_,_,j1,j2,_,_,_,_,_,_) = b.xsteps in
  let c1 = parse_term(xor4_c1 b.xk) in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ASM_CASES_TAC c1 THEN ASM_REWRITE_TAC[] THENL
   [XOR4_ENTRY_TAC b j1 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FIRST_X_ASSUM(fun th ->
      if is_disj(concl th) then
        SUBGOAL_THEN (parse_term(xor4_c2 b.xk)) ASSUME_TAC THENL
         [MP_TAC th THEN ASM_REWRITE_TAC[]; ALL_TAC]
      else NO_TAC) THEN
    XOR4_ENTRY_TAC b (j2 - 1) THEN XOR4_LS_STEP_TAC j2 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let XOR4_BLOCK_TAC b =
  let (n1,n2,_,_,_,_,_,_,_,_) = b.xsteps in
  let c12 = mk_disj(parse_term(xor4_c1 b.xk),parse_term(xor4_c2 b.xk)) in
  ASM_CASES_TAC `len <= 7` THEN ASM_REWRITE_TAC[] THENL
   [XOR4_BYTELOOP_TAC b `0` `len:num` XOR_POS0_TAC (XOR4_BPRO_TAC b n1);
    ALL_TAC] THEN
  ASM_CASES_TAC c12 THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    XOR4_BYTELOOP_TAC b `0` `len:num` XOR_POS0_TAC (XOR4_B2PRO_TAC b n2)] THEN
  (if b.xk > 0 then COPIES_POST_REASSOC_TAC else ALL_TAC) THEN
  ENSURES_EVENTS_SEQUENCE_TAC (xor4_label(xor4_jv b)) (XOR4_MIDJ b) THEN
  CONJ_TAC THENL
   [XOR4_J_TAC b;
    ASM_CASES_TAC `len < 32` THEN ASM_REWRITE_TAC[] THENL
     [XOR4_PATH_A_TAC b; XOR4_PATH_B_TAC b]];;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

let XOR4_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC XOR4_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL; fst XOR4_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC];;

let XOR4_LEN0_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] o
    check (fun th -> is_eq(concl th) && is_var(rand(concl th)) &&
                     can (term_match [] `read (memory :> bytes(d,0)) s`)
                         (lhs(concl th))))) THEN
  ARM_STEPS_TAC XOR4_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; WORD_XOR_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR4_RET_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR4_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR4_MAIN_TAC =
  XOR4_INTRO_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR4_LEN0_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC (xor4_label "ret") (XOR4_INV 4) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC (xor4_label "join9") (XOR4_INV 3) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC (xor4_label "join6") (XOR4_INV 2) THEN
      CONJ_TAC THENL
       [ENSURES_EVENTS_SEQUENCE_TAC (xor4_label "join3") (XOR4_INV 1) THEN
        CONJ_TAC THENL
         [XOR4_BLOCK_TAC (el 0 xor4_blocks);
          XOR4_BLOCK_TAC (el 1 xor4_blocks)];
        XOR4_BLOCK_TAC (el 2 xor4_blocks)];
      XOR4_BLOCK_TAC (el 3 xor4_blocks)];
    XOR4_RET_TAC];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof. The four     *)
(* states, each a 1600-bit word as for mlkem_keccakf1600_xor_bytes, are      *)
(* consecutive in memory, and the data of state k, len bytes as the number   *)
(* mk, is at dk; the data may overlap each other but not the states. The     *)
(* events are those of the copies for the paths that they take, which depend *)
(* only on len and on the tests of overlap.                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word)
            (S2:1600 word) (S3:1600 word) m0 m1 m2 m3 pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       off + len <= 200 /\
       ALLPAIRS nonoverlapping
        [a,800]
        [word pc,libmlkem_size; d0,len; d1,len; d2,len; d3,len]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_keccakf1600x4_xor_bytes) /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                 read (memory :> wbytes a) s = S0 /\
                 read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                 read (memory :> bytes(d0,len)) s = m0 /\
                 read (memory :> bytes(d1,len)) s = m1 /\
                 read (memory :> bytes(d2,len)) s = m2 /\
                 read (memory :> bytes(d3,len)) s = m3 /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes a) s =
                 word_xor S0 (word(2 EXP (8 * off) * m0)) /\
                 read (memory :> wbytes (word_add a (word 200))) s =
                 word_xor S1 (word(2 EXP (8 * off) * m1)) /\
                 read (memory :> wbytes (word_add a (word 400))) s =
                 word_xor S2 (word(2 EXP (8 * off) * m2)) /\
                 read (memory :> wbytes (word_add a (word 600))) s =
                 word_xor S3 (word(2 EXP (8 * off) * m3)) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len] [a,800]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800)])`,
  XOR4_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) m0 m1 m2 m3 pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALLPAIRS nonoverlapping
         [(a,800)]
         [(word pc,libmlkem_size); (d0,len); (d1,len); (d2,len); (d3,len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600x4_xor_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                  read (memory :> bytes(d0,len)) s = m0 /\
                  read (memory :> bytes(d1,len)) s = m1 /\
                  read (memory :> bytes(d2,len)) s = m2 /\
                  read (memory :> bytes(d3,len)) s = m3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s =
                  word_xor S0 (word(2 EXP (8 * off) * m0)) /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  word_xor S1 (word(2 EXP (8 * off) * m1)) /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  word_xor S2 (word(2 EXP (8 * off) * m2)) /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  word_xor S3 (word(2 EXP (8 * off) * m3)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,800)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->int64->int64->int64->num->num->num->int64->
      (uarch_event)list`
   MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`;
    `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       off + len <= 200 /\
       ALLPAIRS nonoverlapping
        [a,800]
        [word pc,libmlkem_size; d0,len; d1,len; d2,len; d3,len]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_keccakf1600x4_xor_bytes) /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len] [a,800]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800)])`,
  MP_TAC
   MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (v,t) -> GHOST_INTRO_TAC v t)
   [`S0:1600 word`,`read (memory :> wbytes a):armstate->1600 word`;
    `S1:1600 word`,
    `read (memory :> wbytes (word_add a (word 200))):armstate->1600 word`;
    `S2:1600 word`,
    `read (memory :> wbytes (word_add a (word 400))):armstate->1600 word`;
    `S3:1600 word`,
    `read (memory :> wbytes (word_add a (word 600))):armstate->1600 word`;
    `m0:num`,`read (memory :> bytes(d0,len))`;
    `m1:num`,`read (memory :> bytes(d1,len))`;
    `m2:num`,`read (memory :> bytes(d2,len))`;
    `m3:num`,`read (memory :> bytes(d3,len))`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`;
    `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
