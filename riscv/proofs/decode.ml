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

(* Map a five-bit register field to its state component. *)

let riscv_xreg = new_definition
 `riscv_xreg (r:5 word) = riscv_gpr r`;;

(* Instruction words are decoded with `bitmatch`, as in the ARM and x86
   models: each clause lists the 32-bit fields from most- to least-significant
   bit, binding the register and immediate sub-fields positionally and pinning
   the opcode / funct3 / funct7 selectors as literals. The scrambled RISC-V
   immediate formats are reassembled with `word_join` and sign-extended with
   `word_sx`, following the "Base Instruction Formats" and "Immediate Encoding
   Variants" tables:

     R-type  [funct7:7; rs2:5; rs1:5; funct3:3; rd:5; opcode:7]
     I-type  [imm[11:0]:12; rs1:5; funct3:3; rd:5; opcode:7]
     I-shift [funct7:7; shamt:5; rs1:5; funct3:3; rd:5; opcode:7]
     S-type  [imm[11:5]:7; rs2:5; rs1:5; funct3:3; imm[4:0]:5; opcode:7]
     B-type  [imm[12]; imm[10:5]:6; rs2:5; rs1:5; funct3:3; imm[4:1]:4;
              imm[11]; opcode:7]
     U-type  [imm[31:12]:20; rd:5; opcode:7]

   Opcode / funct selectors (binary):

     ADD   0110011 / 000 / 0000000   SUB   0110011 / 000 / 0100000
     MUL   0110011 / 000 / 0000001   MULH  0110011 / 001 / 0000001
     ADDI  0010011 / 000             SLLI  0010011 / 001 / 0000000
     SRAI  0010011 / 101 / 0100000   LW    0000011 / 010
     SW    0100011 / 010             BNE   1100011 / 001
     LUI   0110111                   JALR  1100111 / 000

   Unsupported opcodes and unsupported variants fall through to `NONE`. *)

let decode = new_definition
 `decode (w:int32) =
    bitmatch w:int32 with
    | [0b0000000:7; rs2:5; rs1:5; 0b000:3; rd:5; 0b0110011:7] ->
        SOME (riscv_ADD (riscv_xreg rd) (riscv_xreg rs1) (riscv_xreg rs2))
    | [0b0100000:7; rs2:5; rs1:5; 0b000:3; rd:5; 0b0110011:7] ->
        SOME (riscv_SUB (riscv_xreg rd) (riscv_xreg rs1) (riscv_xreg rs2))
    | [0b0000001:7; rs2:5; rs1:5; 0b000:3; rd:5; 0b0110011:7] ->
        SOME (riscv_MUL (riscv_xreg rd) (riscv_xreg rs1) (riscv_xreg rs2))
    | [0b0000001:7; rs2:5; rs1:5; 0b001:3; rd:5; 0b0110011:7] ->
        SOME (riscv_MULH (riscv_xreg rd) (riscv_xreg rs1) (riscv_xreg rs2))
    | [imm:12; rs1:5; 0b000:3; rd:5; 0b0010011:7] ->
        SOME (riscv_ADDI (riscv_xreg rd) (riscv_xreg rs1) (word_sx imm))
    | [0b0000000:7; shamt:5; rs1:5; 0b001:3; rd:5; 0b0010011:7] ->
        SOME (riscv_SLLI (riscv_xreg rd) (riscv_xreg rs1) (val shamt))
    | [0b0100000:7; shamt:5; rs1:5; 0b101:3; rd:5; 0b0010011:7] ->
        SOME (riscv_SRAI (riscv_xreg rd) (riscv_xreg rs1) (val shamt))
    | [imm:12; rs1:5; 0b010:3; rd:5; 0b0000011:7] ->
        SOME (riscv_LW (riscv_xreg rd) (riscv_xreg rs1) (word_sx imm))
    | [immhi:7; rs2:5; rs1:5; 0b010:3; immlo:5; 0b0100011:7] ->
        SOME (riscv_SW (riscv_xreg rs2) (riscv_xreg rs1)
          (word_sx (word_join immhi immlo:12 word)))
    | [imm12:1; imm10_5:6; rs2:5; rs1:5; 0b001:3; imm4_1:4; imm11:1;
       0b1100011:7] ->
        SOME (riscv_BNE (riscv_xreg rs1) (riscv_xreg rs2)
          (word_sx (word_join
             (word_join (word_join imm12 imm11:2 word) imm10_5:8 word)
             (word_join imm4_1 (word 0:1 word):5 word):13 word)))
    | [imm:20; rd:5; 0b0110111:7] ->
        SOME (riscv_LUI (riscv_xreg rd)
          (word_join imm (word 0:12 word):int32))
    | [imm:12; rs1:5; 0b000:3; rd:5; 0b1100111:7] ->
        SOME (riscv_JALR (riscv_xreg rd) (riscv_xreg rs1) (word_sx imm))
    | _ -> NONE`;;

open Compute;;

(* Prove the result of decoding one concrete 32-bit instruction word. The
   input must have the form `decode (word n)`, and the conversion fails when
   the encoding is unsupported. For example, applying `PURE_DECODE_CONV` to

     `decode (word 0x00b50533)`

   proves that 0x00b50533 decodes to `riscv_ADD A0 A0 A1`. *)

let PURE_DECODE_CONV =
  let decode_rw =
    let rw = bool_compset() in
    (* Evaluate only the selected arm of a conditional or (bit)match before
       folding its branches. *)
    set_skip rw `COND:bool->A->A->A` (Some 1);
    set_skip rw `_MATCH:A->(A->B->bool)->B` (Some 1);
    set_skip rw `_BITMATCH:(N)word->(num->B->bool)->B` (Some 1);
    (* basic word/num expression evaluation *)
    word_compute_add_convs rw;
    num_compute_add_convs rw;
    add_conv (`_MATCH:A->(A->B->bool)->B`, 2, MATCH_CONV) rw;
    add_thms [riscv_gpr; riscv_xreg] rw;
    (* `decode` carries a bitmatch, so conceal it under an opaque constant and
       supply the matching reducer, as ARM's PURE_DECODE_CONV does. *)
    (let Some (conceal_th, opaque_const, opaque_arity, _, opaque_conv) =
        conceal_bitmatch (concl decode) in
     add_thms [GEN_REWRITE_RULE I [conceal_th] decode] rw;
     add_conv (opaque_const, opaque_arity, opaque_conv) rw);
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

(* ------------------------------------------------------------------------- *)
(* ELF32 object loading.                                                     *)
(* ------------------------------------------------------------------------- *)

(* ELF machine IDs, flags, and relocation numbers follow the "ELF Object
   Files" and "Relocations" sections of the RISC-V ABIs Specification:

   https://riscv-non-isa.github.io/riscv-elf-psabi-doc/ *)

let elf_machine_riscv = 243;;
let ef_riscv_rvc = 0x1;;
let ef_riscv_rve = 0x8;;
let r_riscv_branch = 16;;

let set_int32_le bs off n =
  if off < 0 || off + 4 > Bytes.length bs then
    failwith "set_int32_le: offset outside byte array"
  else
    for i = 0 to 3 do
      Bytes.set bs (off + i)
        (Char.chr ((n lsr (8 * i)) land 0xff))
    done;;

let riscv_apply_elf_relocation text (relocation:elf_relocation) =
  let off = relocation.elf_relocation_offset
  and symbol = relocation.elf_relocation_symbol in
  if relocation.elf_relocation_type <> r_riscv_branch then
    failwith (Printf.sprintf "unexpected RISC-V relocation type: %d"
      relocation.elf_relocation_type)
  else if symbol.elf_symbol_section_name <> ".text" then
    failwith "R_RISCV_BRANCH target is not in .text"
  else if off land 3 <> 0 then
    failwith "R_RISCV_BRANCH offset is not four-byte aligned"
  else if off < 0 || off + 4 > Bytes.length text then
    failwith "R_RISCV_BRANCH offset is outside .text"
  else
    let target =
      symbol.elf_symbol_value + relocation.elf_relocation_addend in
    let displacement = target - off in
    let instruction = get_int_le text off 4 in
    if target < 0 || target >= Bytes.length text then
      failwith "R_RISCV_BRANCH target is outside .text"
    else if target land 3 <> 0 then
      failwith "R_RISCV_BRANCH target is not four-byte aligned"
    else if instruction land 0x7f <> 0x63 then
      failwith "R_RISCV_BRANCH does not refer to a branch instruction"
    else if displacement < -4096 || displacement > 4094 ||
            displacement land 1 <> 0 then
      failwith "R_RISCV_BRANCH displacement does not fit"
    else
      (* Place immediate bits 12, 10:5, 4:1, and 11 in the B-type fields
         inst[31], inst[30:25], inst[11:8], and inst[7], respectively. *)
      let imm = displacement land 0x1fff in
      let encoded =
        ((imm land 0x1000) lsl 19) lor
        ((imm land 0x07e0) lsl 20) lor
        ((imm land 0x001e) lsl 7) lor
        ((imm land 0x0800) lsr 4) in
      let relocated =
        (instruction land (lnot 0xfe000f80)) lor encoded in
      set_int32_le text off relocated;;

let load_elf_contents_riscv path =
  let file = load_file path in
  let text,_,relocations =
    load_elf32_raw elf_machine_riscv file in
  let flags = get_int_le file 0x24 4 in
  if flags land ef_riscv_rvc <> 0 then
    failwith "RISC-V compressed instructions are not supported"
  else if flags land ef_riscv_rve <> 0 then
    failwith "RISC-V RV32E ABI is not supported"
  else if Bytes.length text mod 4 <> 0 then
    failwith "RISC-V .text size is not a multiple of four"
  else
    let relocated_text = Bytes.copy text in
    List.iter (riscv_apply_elf_relocation relocated_text) relocations;
    relocated_text;;

(* Define machine code from relocated ELF text, with an optional explicit
   word list that is checked against those bytes before the definition is
   created. *)

let define_from_elf name file =
  define_word_list name (term_of_bytes (load_elf_contents_riscv file));;

let define_assert_from_elf name file =
  define_assert_word_list name
    (term_of_bytes (load_elf_contents_riscv file));;
