(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Partial RV32IM instruction decoding.                                      *)
(* ========================================================================= *)

(* Field and immediate layouts follow "Base Instruction Formats" in "RV32I
   Base Integer Instruction Set, Version 2.1" of The RISC-V Instruction Set
   Manual, Volume I: Unprivileged Architecture. Exact opcode, funct3, and
   funct7 values follow the manual's "RV32/64G Instruction Set Listings". MUL
   and MULH follow "Multiplication Operations" in "M Extension for Integer
   Multiplication and Division, Version 2.0".

   https://docs.riscv.org/reference/isa/unpriv/rv32.html
   https://docs.riscv.org/reference/isa/unpriv/m-st-ext.html *)

(* Extract len bits beginning at bit lo and return their unsigned value. *)

let riscv_field = new_definition
 `riscv_field lo len (w:int32) = (val w DIV 2 EXP lo) MOD 2 EXP len`;;

(* Convert a bits-bit unsigned immediate to its 32-bit two's-complement
   representation as a natural number. *)

let riscv_signext = new_definition
 `riscv_signext bits n =
    if n < 2 EXP (bits - 1) then n else (2 EXP 32 - 2 EXP bits) + n`;;

(* I-type immediate: sign-extend inst[31:20]. *)

let riscv_imm_i = new_definition
 `riscv_imm_i (w:int32) : int32 =
    word (riscv_signext 12 (riscv_field 20 12 w))`;;

(* S-type immediate: sign-extend inst[31:25] || inst[11:7]. *)

let riscv_imm_s = new_definition
 `riscv_imm_s (w:int32) : int32 =
    word (riscv_signext 12
      (riscv_field 7 5 w + 2 EXP 5 * riscv_field 25 7 w))`;;

(* B-type immediate: sign-extend
   inst[31] || inst[7] || inst[30:25] || inst[11:8] || 0. *)

let riscv_imm_b = new_definition
 `riscv_imm_b (w:int32) : int32 =
    word (riscv_signext 13
      (2 * riscv_field 8 4 w +
       2 EXP 5 * riscv_field 25 6 w +
       2 EXP 11 * riscv_field 7 1 w +
       2 EXP 12 * riscv_field 31 1 w))`;;

(* U-type immediate: inst[31:12] followed by twelve zero bits. *)

let riscv_imm_u = new_definition
 `riscv_imm_u (w:int32) : int32 =
    word (2 EXP 12 * riscv_field 12 20 w)`;;

(* Name the fixed fields from the base instruction formats. Register fields
   are mapped directly to the corresponding state component. *)

let riscv_opcode = new_definition
 `riscv_opcode (w:int32) = riscv_field 0 7 w`;;

let riscv_funct3 = new_definition
 `riscv_funct3 (w:int32) = riscv_field 12 3 w`;;

let riscv_funct7 = new_definition
 `riscv_funct7 (w:int32) = riscv_field 25 7 w`;;

let riscv_rd = new_definition
 `riscv_rd (w:int32) =
    riscv_gpr (word (riscv_field 7 5 w):5 word)`;;

let riscv_rs1 = new_definition
 `riscv_rs1 (w:int32) =
    riscv_gpr (word (riscv_field 15 5 w):5 word)`;;

let riscv_rs2 = new_definition
 `riscv_rs2 (w:int32) =
    riscv_gpr (word (riscv_field 20 5 w):5 word)`;;

let riscv_shamt = new_definition
 `riscv_shamt (w:int32) = riscv_field 20 5 w`;;

(* Opcode values use the hexadecimal spelling from the instruction listings:

     0x03  LOAD       0x13  OP-IMM       0x23  STORE
     0x33  OP         0x37  LUI          0x63  BRANCH
     0x67  JALR

   The supported selectors are:

     ADD   0x33 / 0x0 / 0x00    SUB   0x33 / 0x0 / 0x20
     MUL   0x33 / 0x0 / 0x01    MULH  0x33 / 0x1 / 0x01
     ADDI  0x13 / 0x0           SLLI  0x13 / 0x1 / 0x00
     SRAI  0x13 / 0x5 / 0x20    LW    0x03 / 0x2
     SW    0x23 / 0x2           BNE   0x63 / 0x1
     LUI   0x37                 JALR  0x67 / 0x0

   Entries give opcode, funct3, and funct7 where those fields apply. For
   example, 0x33 is the seven-bit OP opcode 0110011. Unsupported opcodes and
   unsupported variants return NONE. *)

let decode = new_definition
 `decode (w:int32) =
    if riscv_opcode w = 0x33 then
      if riscv_funct3 w = 0x0 /\ riscv_funct7 w = 0x00 then
        SOME (riscv_ADD
          (riscv_rd w) (riscv_rs1 w) (riscv_rs2 w))
      else if riscv_funct3 w = 0x0 /\ riscv_funct7 w = 0x20 then
        SOME (riscv_SUB
          (riscv_rd w) (riscv_rs1 w) (riscv_rs2 w))
      else if riscv_funct3 w = 0x0 /\ riscv_funct7 w = 0x01 then
        SOME (riscv_MUL
          (riscv_rd w) (riscv_rs1 w) (riscv_rs2 w))
      else if riscv_funct3 w = 0x1 /\ riscv_funct7 w = 0x01 then
        SOME (riscv_MULH
          (riscv_rd w) (riscv_rs1 w) (riscv_rs2 w))
      else NONE
    else if riscv_opcode w = 0x13 then
      if riscv_funct3 w = 0x0 then
        SOME (riscv_ADDI
          (riscv_rd w) (riscv_rs1 w) (riscv_imm_i w))
      else if riscv_funct3 w = 0x1 /\ riscv_funct7 w = 0x00 then
        SOME (riscv_SLLI
          (riscv_rd w) (riscv_rs1 w) (riscv_shamt w))
      else if riscv_funct3 w = 0x5 /\ riscv_funct7 w = 0x20 then
        SOME (riscv_SRAI
          (riscv_rd w) (riscv_rs1 w) (riscv_shamt w))
      else NONE
    else if riscv_opcode w = 0x03 then
      if riscv_funct3 w = 0x2 then
        SOME (riscv_LW
          (riscv_rd w) (riscv_rs1 w) (riscv_imm_i w))
      else NONE
    else if riscv_opcode w = 0x23 then
      if riscv_funct3 w = 0x2 then
        SOME (riscv_SW
          (riscv_rs2 w) (riscv_rs1 w) (riscv_imm_s w))
      else NONE
    else if riscv_opcode w = 0x63 then
      if riscv_funct3 w = 0x1 then
        SOME (riscv_BNE
          (riscv_rs1 w) (riscv_rs2 w) (riscv_imm_b w))
      else NONE
    else if riscv_opcode w = 0x37 then
      SOME (riscv_LUI
        (riscv_rd w) (riscv_imm_u w))
    else if riscv_opcode w = 0x67 then
      if riscv_funct3 w = 0x0 then
        SOME (riscv_JALR
          (riscv_rd w) (riscv_rs1 w) (riscv_imm_i w))
      else NONE
    else NONE`;;

open Compute;;

(* Prove the result of decoding one concrete 32-bit instruction word. The
   input must have the form `decode (word n)`, and the conversion fails when
   the encoding is unsupported. For example, applying `PURE_DECODE_CONV` to

     `decode (word 0x00b50533)`

   proves that 0x00b50533 decodes to `riscv_ADD A0 A0 A1`. *)

let PURE_DECODE_CONV =
  let decode_rw =
    let rw = bool_compset() in
    (* Evaluate only the selected arm of each decoder conditional. *)
    set_skip rw `COND:bool->A->A->A` (Some 1);
    word_compute_add_convs rw;
    num_compute_add_convs rw;
    add_thms
      [decode; riscv_field; riscv_signext; riscv_imm_i; riscv_imm_s;
       riscv_imm_b; riscv_imm_u; riscv_opcode; riscv_funct3; riscv_funct7;
       riscv_rd; riscv_rs1; riscv_rs2; riscv_shamt; riscv_gpr] rw;
    rw in
  let base_conv = WEAK_CBV_CONV decode_rw in
  fun t ->
    try
      let th = base_conv t in
      let c = concl th in
      let r,_ = dest_comb (rhs c) in
      if is_const r && name_of r = "SOME" then th else failwith ""
    with Failure _ -> failwith ("PURE_DECODE_CONV: " ^ string_of_term t);;

let DECODE_CONV = PURE_DECODE_CONV;;

(* Keep one explicit encoding test for every supported instruction form. These
   examples exercise the opcode and funct selectors as well as positive and
   negative I-, S-, and B-type immediates. Loading this file fails if a
   conversion result differs from the stated instruction. *)

let RISCV_DECODE_TESTS =
  let cases =
   [`decode (word 0x00b50533)`,
      `SOME (riscv_ADD A0 A0 A1)`;
    `decode (word 0x40b50533)`,
      `SOME (riscv_SUB A0 A0 A1)`;
    `decode (word 0x02b50533)`,
      `SOME (riscv_MUL A0 A0 A1)`;
    `decode (word 0x02b51533)`,
      `SOME (riscv_MULH A0 A0 A1)`;
    `decode (word 0x00150513)`,
      `SOME (riscv_ADDI A0 A0 (word 1))`;
    `decode (word 0xfff50513)`,
      `SOME (riscv_ADDI A0 A0 (word 0xffffffff))`;
    `decode (word 0x00359513)`,
      `SOME (riscv_SLLI A0 A1 3)`;
    `decode (word 0x4035d513)`,
      `SOME (riscv_SRAI A0 A1 3)`;
    `decode (word 0x0045a503)`,
      `SOME (riscv_LW A0 A1 (word 4))`;
    `decode (word 0x00a5a223)`,
      `SOME (riscv_SW A0 A1 (word 4))`;
    `decode (word 0xfea5ae23)`,
      `SOME (riscv_SW A0 A1 (word 0xfffffffc))`;
    `decode (word 0x00b51463)`,
      `SOME (riscv_BNE A0 A1 (word 8))`;
    `decode (word 0xfeb51ee3)`,
      `SOME (riscv_BNE A0 A1 (word 0xfffffffc))`;
    `decode (word 0x12345537)`,
      `SOME (riscv_LUI A0 (word 0x12345000))`;
    `decode (word 0x00008067)`,
      `SOME (riscv_JALR ZERO RA (word 0))`] in
  end_itlist CONJ
   (map
     (fun tm,expected ->
        let th = DECODE_CONV tm in
        if rhs(concl th) = expected then th
        else
          failwith
           ("RISCV_DECODE_TESTS: expected " ^
            string_of_term expected ^ " but got " ^
            string_of_term(rhs(concl th))))
     cases);;

loadt "common/decode32.ml";;

(* `decode32` is the shared four-byte fetch relation. It reads one
   little-endian word from an aligned address and applies the backend decoder;
   this specialization supplies the RV32IM `decode` function above. *)

let riscv_decode = new_definition
 `riscv_decode s pc inst <=> decode32 decode s pc inst`;;

let RISCV_DECODE_CONS = prove
 (`!s pc l i inst l'.
      aligned_bytes_loaded s (word pc) l ==>
      read_int32 l = SOME (i,l') ==>
      decode i = SOME inst ==>
      riscv_decode s (word pc) inst /\
      aligned_bytes_loaded s (word (pc + 4)) l'`,
  REWRITE_TAC[riscv_decode] THEN MATCH_ACCEPT_TAC DECODE32_CONS);;

let riscv_decode_unique = prove
 (`!s pc x y. riscv_decode s pc x ==> riscv_decode s pc y ==> x = y`,
  REWRITE_TAC[riscv_decode] THEN MESON_TAC[decode32_unique]);;

(* Turn a concrete byte-list definition into one decode theorem per
   instruction. For the word at byte offset n, the result has the form

     !s pc. aligned_bytes_loaded s (word pc) code
            ==> riscv_decode s (word (pc + n)) instruction

   paired with n. The recursive step advances by four bytes and proves the
   loading fact for the unconsumed suffix; the returned offsets are therefore
   0, 4, 8, and so on. *)

let RISCV_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc) l ==>
     read_int32 l = SOME (a,l') ==> decode a = SOME i ==>
     riscv_decode s (word pc) i' /\
     aligned_bytes_loaded s (word pc') l'`,
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC RISCV_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + 4 = p ==> (pc + n) + 4 = pc + p`
  and r32,dec,n4 = `read_int32`,`decode`,`4`
  and ei,ei' =
    `i:riscvstate->riscvstate->bool`,`i':riscvstate->riscvstate->bool`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and ea,en,ep,epc,epc' =
    `a:int32`,`n:num`,`p:num`,`pc:num`,`pc':num` in
  let rec go th: (thm*term) list =
    let pc,l = (rand o rand F_F I) (dest_comb (concl th)) in
    let th1 = READ_WORD_CONV (mk_comb (r32,l)) in
    let a,l' = dest_pair (rand (rhs (concl th1))) in
    let th2 = DECODE_CONV (mk_comb (dec,a)) in
    let i = rand (rhs (concl th2)) in
    let ith = REFL i in
    let th4,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl,a),n4)) in
      PROVE_HYP th (INST [pc,epc; a,en; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl,pc),n4)),`0` in
    let pc' = rhs (concl th4) in
    let th' = itlist PROVE_HYP [ith; th4; th; th1; th2]
      (INST [i,ei; i,ei'; pc,epc; pc',epc'; l,el; a,ea; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ ->
        let dth,bth = CONJ_PAIR th' in
        (dth,pcofs)::go bth in
  fun th ->
    let decodes:(thm*term) list =
      (go o
       (fun dth -> EQ_MP dth (ASSUME (lhs (concl dth)))) o
       AP_TERM `aligned_bytes_loaded s (word pc)`) th in
    map
      (fun th,pcofs ->
        ((GENL [`s:riscvstate`; `pc:num`] o DISCH_ALL) th,pcofs))
      decodes;;

(* Build the code-length theorem and an array containing the decode theorem
   for each instruction at its byte offset. Array entries between aligned
   instruction offsets are left as NONE. *)

let RISCV_MK_EXEC_RULE th0:thm * thm option array =
  GEN_MK_EXEC_RULE
    [LENGTH_BYTELIST_OF_NUM; LENGTH; LENGTH_APPEND]
    RISCV_DECODES_THM th0;;

(* ------------------------------------------------------------------------- *)
(* Testing and preparation.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Decode every four-byte word in a concrete byte-list term. *)

let rec decode_all = function
| Const("NIL",_) -> []
| tm ->
  let th1 = READ_WORD_CONV (mk_comb (`read_int32`,tm)) in
  let a,next = dest_pair (rand (rhs (concl th1))) in
  let th = DECODE_CONV (mk_comb (`decode`,a)) in
  let h = rand (rhs (concl th)) in
  h::decode_all next;;

(* Define the checked byte list only after `assert_word_list` has confirmed
   that the supplied 32-bit words are exactly its little-endian contents. *)

let define_assert_word_list name tm ls =
  define_word_list name (assert_word_list tm ls);;
