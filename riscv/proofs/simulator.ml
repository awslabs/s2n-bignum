(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Persistent QEMU-system cosimulation tests for the RV32IM model.
 *
 * The HOL-side client generates a short instruction sequence and one
 * concrete machine state, sends both to the external execution backend, and
 * then checks the returned state against one symbolic HOL execution. The
 * backend is started once through common/cosim.ml; by default it is
 * riscv/proofs/cosim-runner, which runs the freestanding monitor under QEMU.
 * The backend's output is an independent concrete execution result, not
 * the proof: the result is inserted into a HOL theorem statement, and the
 * RV32 model must prove that the same input produces that output.
 *
 * This follows the Arm and x86 frontends' three-stage structure:
 *
 *   choose case -> execute concrete state -> instantiate theorem -> prove
 *                                                        symbolic agreement
 *
 * The RV32 transport contains the 31 non-SP registers and 64 scratch
 * words, for 95 words in total. SP remains private to the executor and
 * points at the scratch buffer. PC remains part of the HOL machine state
 * and is fixed to symbolic `pc` in the theorem, but it is not part of this
 * straight-line conformance transport, just as in the Arm and x86
 * frontends.
 *)

needs "common/cosim.ml";;
needs "common/sematest.ml";;
needs "riscv/proofs/base.ml";;

(* The transport contains the non-SP registers and 64 scratch words. *)

let regfile = new_definition
 `regfile scratch s =
   [val(read ZERO s); val(read RA s); val(read GP s);
    val(read TP s); val(read T0 s); val(read T1 s); val(read T2 s);
    val(read S0 s); val(read S1 s); val(read A0 s); val(read A1 s);
    val(read A2 s); val(read A3 s); val(read A4 s); val(read A5 s);
    val(read A6 s); val(read A7 s); val(read S2 s); val(read S3 s);
    val(read S4 s); val(read S5 s); val(read S6 s); val(read S7 s);
    val(read S8 s); val(read S9 s); val(read S10 s); val(read S11 s);
    val(read T3 s); val(read T4 s); val(read T5 s); val(read T6 s);
    val(read (memory :> bytes32 scratch) s);
    val(read (memory :> bytes32(word_add scratch (word 4))) s);
    val(read (memory :> bytes32(word_add scratch (word 8))) s);
    val(read (memory :> bytes32(word_add scratch (word 12))) s);
    val(read (memory :> bytes32(word_add scratch (word 16))) s);
    val(read (memory :> bytes32(word_add scratch (word 20))) s);
    val(read (memory :> bytes32(word_add scratch (word 24))) s);
    val(read (memory :> bytes32(word_add scratch (word 28))) s);
    val(read (memory :> bytes32(word_add scratch (word 32))) s);
    val(read (memory :> bytes32(word_add scratch (word 36))) s);
    val(read (memory :> bytes32(word_add scratch (word 40))) s);
    val(read (memory :> bytes32(word_add scratch (word 44))) s);
    val(read (memory :> bytes32(word_add scratch (word 48))) s);
    val(read (memory :> bytes32(word_add scratch (word 52))) s);
    val(read (memory :> bytes32(word_add scratch (word 56))) s);
    val(read (memory :> bytes32(word_add scratch (word 60))) s);
    val(read (memory :> bytes32(word_add scratch (word 64))) s);
    val(read (memory :> bytes32(word_add scratch (word 68))) s);
    val(read (memory :> bytes32(word_add scratch (word 72))) s);
    val(read (memory :> bytes32(word_add scratch (word 76))) s);
    val(read (memory :> bytes32(word_add scratch (word 80))) s);
    val(read (memory :> bytes32(word_add scratch (word 84))) s);
    val(read (memory :> bytes32(word_add scratch (word 88))) s);
    val(read (memory :> bytes32(word_add scratch (word 92))) s);
    val(read (memory :> bytes32(word_add scratch (word 96))) s);
    val(read (memory :> bytes32(word_add scratch (word 100))) s);
    val(read (memory :> bytes32(word_add scratch (word 104))) s);
    val(read (memory :> bytes32(word_add scratch (word 108))) s);
    val(read (memory :> bytes32(word_add scratch (word 112))) s);
    val(read (memory :> bytes32(word_add scratch (word 116))) s);
    val(read (memory :> bytes32(word_add scratch (word 120))) s);
    val(read (memory :> bytes32(word_add scratch (word 124))) s);
    val(read (memory :> bytes32(word_add scratch (word 128))) s);
    val(read (memory :> bytes32(word_add scratch (word 132))) s);
    val(read (memory :> bytes32(word_add scratch (word 136))) s);
    val(read (memory :> bytes32(word_add scratch (word 140))) s);
    val(read (memory :> bytes32(word_add scratch (word 144))) s);
    val(read (memory :> bytes32(word_add scratch (word 148))) s);
    val(read (memory :> bytes32(word_add scratch (word 152))) s);
    val(read (memory :> bytes32(word_add scratch (word 156))) s);
    val(read (memory :> bytes32(word_add scratch (word 160))) s);
    val(read (memory :> bytes32(word_add scratch (word 164))) s);
    val(read (memory :> bytes32(word_add scratch (word 168))) s);
    val(read (memory :> bytes32(word_add scratch (word 172))) s);
    val(read (memory :> bytes32(word_add scratch (word 176))) s);
    val(read (memory :> bytes32(word_add scratch (word 180))) s);
    val(read (memory :> bytes32(word_add scratch (word 184))) s);
    val(read (memory :> bytes32(word_add scratch (word 188))) s);
    val(read (memory :> bytes32(word_add scratch (word 192))) s);
    val(read (memory :> bytes32(word_add scratch (word 196))) s);
    val(read (memory :> bytes32(word_add scratch (word 200))) s);
    val(read (memory :> bytes32(word_add scratch (word 204))) s);
    val(read (memory :> bytes32(word_add scratch (word 208))) s);
    val(read (memory :> bytes32(word_add scratch (word 212))) s);
    val(read (memory :> bytes32(word_add scratch (word 216))) s);
    val(read (memory :> bytes32(word_add scratch (word 220))) s);
    val(read (memory :> bytes32(word_add scratch (word 224))) s);
    val(read (memory :> bytes32(word_add scratch (word 228))) s);
    val(read (memory :> bytes32(word_add scratch (word 232))) s);
    val(read (memory :> bytes32(word_add scratch (word 236))) s);
    val(read (memory :> bytes32(word_add scratch (word 240))) s);
    val(read (memory :> bytes32(word_add scratch (word 244))) s);
    val(read (memory :> bytes32(word_add scratch (word 248))) s);
    val(read (memory :> bytes32(word_add scratch (word 252))) s)]`;;

(* The runner places the instruction in an internal code slot and uses an
   EBREAK at the next instruction to return to the monitor. The HOL statement
   remains parameterized by symbolic `pc`, as in the Arm and x86 frontends. *)
let template =
 `nonoverlapping (word pc,LENGTH ibytes) (scratchpointer,256)
 ==> ensures riscv
       (\s. aligned_bytes_loaded s (word pc) ibytes /\
            aligned 4 scratchpointer /\
            read PC s = word pc /\
            read SP s = scratchpointer /\
            regfile scratchpointer s = input_state)
       (\s. read SP s = scratchpointer /\
            regfile scratchpointer s = output_state)
       (MAYCHANGE [PC] ,,
        MAYCHANGE [RA; SP; GP; TP; T0; T1; T2; S0; S1; A0; A1; A2;
                   A3; A4; A5; A6; A7; S2; S3; S4; S5; S6; S7; S8;
                   S9; S10; S11; T3; T4; T5; T6] ,,
        MAYCHANGE [memory :> bytes(scratchpointer,256)] ,,
        MAYCHANGE [events])`;;

let random_boold d = Random.int 64 < d;;

let randomnd n density =
  funpow n
    (fun value ->
      (if random_boold density then num_1 else num_0) +/ num_2 */ value)
    num_0;;

let random32 density = randomnd 32 density;;

let encode_r funct7 rs2 rs1 funct3 rd =
  ((funct7 land 0x7f) lsl 25) lor
  ((rs2 land 0x1f) lsl 20) lor
  ((rs1 land 0x1f) lsl 15) lor
  ((funct3 land 7) lsl 12) lor
  ((rd land 0x1f) lsl 7) lor 0x33;;

let encode_i immediate rs1 funct3 rd opcode =
  ((immediate land 0xfff) lsl 20) lor
  ((rs1 land 0x1f) lsl 15) lor
  ((funct3 land 7) lsl 12) lor
  ((rd land 0x1f) lsl 7) lor (opcode land 0x7f);;

let encode_s immediate rs2 rs1 funct3 =
  let bits = immediate land 0xfff in
  (((bits lsr 5) land 0x7f) lsl 25) lor
  ((rs2 land 0x1f) lsl 20) lor
  ((rs1 land 0x1f) lsl 15) lor
  ((funct3 land 7) lsl 12) lor
  ((bits land 0x1f) lsl 7) lor 0x23;;

let instruction_bytes instruction =
  [instruction land 0xff;
   (instruction lsr 8) land 0xff;
   (instruction lsr 16) land 0xff;
   (instruction lsr 24) land 0xff];;

let random_register () =
  let register = Random.int 31 in
  if register < 2 then register else register + 1;;

type rv32_test_case =
 { case_setup: int list;
   case_instruction: int;
   case_cleanup: int list;
   case_memop_index: int option;
   case_input: num list };;

type rv32_case_builder = unit -> rv32_test_case;;

let make_input_state density =
  [num_0] @
  [random32 density] @
  map (fun _ -> random32 density) (3--31) @
  map (fun _ -> random32 density) (0--63);;

let rec list_update index value values =
  match index,values with
  | 0,_::tail -> value::tail
  | n,head::tail when n > 0 -> head::list_update (n - 1) value tail
  | _ -> failwith "list_update: index outside list";;

let transport_register_index register =
  if register < 0 || register > 31 then
    failwith "transport_register_index: bad register"
  else if register = 2 then
    failwith "transport_register_index: SP is not transported"
  else if register < 2 then register
  else register - 1;;

let set_input_register register value state =
  if register = 0 && value <> num_0 then
    failwith "set_input_register: x0 must remain zero"
  else
    list_update (transport_register_index register) value state;;

let directed_input_state assignments =
  itlist
    (fun (register,value) state -> set_input_register register value state)
    assignments
    (map (fun _ -> num_0) (1--95));;

(* Choose an address aligned to the access size in the scratch buffer, a
   four-byte SP adjustment, and the 12-bit immediate that reaches the address
   from the adjusted SP. *)

let rec memory_operands size =
  let address = size * Random.int (256 / size)
  and setup = 4 * (Random.int 1024 - 512) in
  let immediate = address - setup in
  if immediate < -2048 || immediate > 2047
  then memory_operands size
  else address,setup,immediate;;

(* Register-only builders choose the register fields at random. The R-type,
   I-type, and shift-immediate ALU forms differ only in their function bits,
   so one builder covers each format. *)

let make_r_case funct7 funct3 input =
  let rd = random_register ()
  and rs1 = random_register ()
  and rs2 = random_register () in
  { case_setup = [];
    case_instruction = encode_r funct7 rs2 rs1 funct3 rd; case_cleanup = [];
    case_memop_index = None;
    case_input = input };;

let make_i_case funct3 input =
  let rd = random_register ()
  and rs1 = random_register ()
  and immediate = Random.int 4096 - 2048 in
  { case_setup = [];
    case_instruction = encode_i immediate rs1 funct3 rd 0x13;
    case_cleanup = []; case_memop_index = None;
    case_input = input };;

let make_shift_case funct7 funct3 input =
  let rd = random_register ()
  and rs1 = random_register ()
  and shift = Random.int 32 in
  { case_setup = [];
    case_instruction = encode_i ((funct7 lsl 5) lor shift) rs1 funct3 rd 0x13;
    case_cleanup = []; case_memop_index = None;
    case_input = input };;

let make_lui_case input =
  let rd = random_register ()
  and immediate = Random.int 0x100000 in
  { case_setup = [];
    case_instruction = (immediate lsl 12) lor (rd lsl 7) lor 0x37;
    case_cleanup = []; case_memop_index = None;
    case_input = input };;

let make_load_case funct3 size input =
  let rd = random_register () in
  let _,setup,immediate = memory_operands size in
  { case_setup = [encode_i setup 2 0 2 0x13];
    case_instruction = encode_i immediate 2 funct3 rd 0x03;
    case_cleanup = [encode_i (-setup) 2 0 2 0x13];
    case_memop_index = Some 1;
    case_input = input };;

let make_store_case funct3 size input =
  let rs2 = random_register () in
  let _,setup,immediate = memory_operands size in
  { case_setup = [encode_i setup 2 0 2 0x13];
    case_instruction = encode_s immediate rs2 2 funct3;
    case_cleanup = [encode_i (-setup) 2 0 2 0x13];
    case_memop_index = Some 1;
    case_input = input };;

let regclasses : rv32_case_builder list =
  map (fun make -> fun () -> make (make_input_state (Random.int 65)))
   [make_r_case 0 0;               (* ADD    *)
    make_i_case 0;                 (* ADDI   *)
    make_r_case 0x20 0;            (* SUB    *)
    make_shift_case 0 1;           (* SLLI   *)
    make_shift_case 0x20 5;        (* SRAI   *)
    make_lui_case;
    make_r_case 1 0;               (* MUL    *)
    make_r_case 1 1;               (* MULH   *)
    make_r_case 0 1;               (* SLL    *)
    make_r_case 0 2;               (* SLT    *)
    make_r_case 0 3;               (* SLTU   *)
    make_r_case 0 4;               (* XOR    *)
    make_r_case 0 5;               (* SRL    *)
    make_r_case 0x20 5;            (* SRA    *)
    make_r_case 0 6;               (* OR     *)
    make_r_case 0 7;               (* AND    *)
    make_i_case 2;                 (* SLTI   *)
    make_i_case 3;                 (* SLTIU  *)
    make_i_case 4;                 (* XORI   *)
    make_i_case 6;                 (* ORI    *)
    make_i_case 7;                 (* ANDI   *)
    make_shift_case 0 5];;         (* SRLI   *)

let memclasses : rv32_case_builder list =
  map (fun make -> fun () -> make (make_input_state (Random.int 65)))
   [make_load_case 0 1;            (* LB     *)
    make_load_case 1 2;            (* LH     *)
    make_load_case 2 4;            (* LW     *)
    make_load_case 4 1;            (* LBU    *)
    make_load_case 5 2;            (* LHU    *)
    make_store_case 0 1;           (* SB     *)
    make_store_case 1 2;           (* SH     *)
    make_store_case 2 4];;         (* SW     *)

let caseclasses = regclasses @ memclasses;;

let make_case kind =
  if kind < 0 || kind >= length caseclasses
  then failwith "make_case: bad instruction kind"
  else el kind caseclasses ();;

let directed_r_case funct7 funct3 rd rs1 rs2 assignments =
  { case_setup = [];
    case_instruction = encode_r funct7 rs2 rs1 funct3 rd;
    case_cleanup = []; case_memop_index = None;
    case_input = directed_input_state assignments };;

let directed_i_case funct3 rd rs1 immediate assignments =
  { case_setup = [];
    case_instruction = encode_i immediate rs1 funct3 rd 0x13;
    case_cleanup = []; case_memop_index = None;
    case_input = directed_input_state assignments };;

let directed_lui_case rd immediate =
  { case_setup = [];
    case_instruction = (immediate lsl 12) lor (rd lsl 7) lor 0x37;
    case_cleanup = []; case_memop_index = None;
    case_input = directed_input_state [] };;

(* Run one load or store with SP adjusted by `setup` around it, as the random
   memory cases do, after setting the listed registers and scratch words.
   The directed loads write x4, and the directed stores store x4. *)

let directed_memory_case setup instruction assignments words =
  { case_setup = [encode_i setup 2 0 2 0x13];
    case_instruction = instruction;
    case_cleanup = [encode_i (-setup) 2 0 2 0x13];
    case_memop_index = Some 1;
    case_input =
      itlist (fun (index,value) -> list_update (31 + index) value)
        words (directed_input_state assignments) };;

let directed_load_case funct3 setup immediate words =
  directed_memory_case setup (encode_i immediate 2 funct3 4 0x03) [] words;;

let directed_store_case funct3 setup immediate value words =
  directed_memory_case setup (encode_s immediate 4 2 funct3) [4,value] words;;

(*** Run a fixed prelude before random sampling so x0 behavior, operand
 *** aliasing, immediate extremes, signed wraparound, and the extension and
 *** placement of byte and halfword accesses do not rely on chance. The
 *** subsequent random campaign keeps probing the wider state space and
 *** memory harnesses.
 ***)

let directed_cases =
  [(* ADD value cases: x0 destination, wraparound, signed overflow. *)
   directed_r_case 0 0 0 1 3      (* add  x0, 0x00000001, 0x00000001 *)
     [1,num 1; 3,num 1];
   directed_r_case 0 0 1 1 3      (* add  x1, 0xffffffff, 0x00000001 *)
     [1,num 0xffffffff; 3,num 1];
   directed_r_case 0 0 3 1 3      (* add  x3, 0x7fffffff, 0x00000001 *)
     [1,num 0x7fffffff; 3,num 1];
   (* ADD register-shape case: rd = rs2. *)
   directed_r_case 0 0 4 1 1      (* add  x4, x1, x1                 *)
     [1,num 0x80000000];
   (* ADDI value cases: x0 destination, sign extension, immediate extremes. *)
   directed_i_case 0 0 1 1        (* addi x0, 0xffffffff, 1          *)
     [1,num 0xffffffff];
   directed_i_case 0 1 0 (-1)     (* addi x1, 0x00000000, -1         *)
     [];
   directed_i_case 0 1 1 2047     (* addi x1, 0x80000000, 2047       *)
     [1,num 0x80000000];
   directed_i_case 0 3 1 (-2048)  (* addi x3, 0x7fffffff, -2048      *)
     [1,num 0x7fffffff];
   (* SUB value cases: self-subtraction, zero source, INT_MIN wraparound. *)
   directed_r_case 0x20 0 1 1 1   (* sub  x1, x1, x1                 *)
     [1,num 0x80000000];
   directed_r_case 0x20 0 0 1 3   (* sub  x0, 0x00000001, 0x00000001 *)
     [1,num 1; 3,num 1];
   directed_r_case 0x20 0 1 0 3   (* sub  x1, 0x00000000, 0x00000001 *)
     [3,num 1];
   directed_r_case 0x20 0 3 1 4   (* sub  x3, 0x80000000, 0x00000001 *)
     [1,num 0x80000000; 4,num 1];
   (* SLLI value cases: zero shift, sign-bit entry, top-bit retention. *)
   directed_i_case 1 1 1 0        (* slli x1, 0xaaaaaaaa, 0          *)
     [1,num 0xaaaaaaaa];
   directed_i_case 1 3 1 31       (* slli x3, 0x00000001, 31         *)
     [1,num 1];
   directed_i_case 1 1 1 31       (* slli x1, 0xffffffff, 31         *)
     [1,num 0xffffffff];
   (* SLLI register-shape case: rd = rs1. *)
   directed_i_case 1 4 4 1        (* slli x4, x4, 1                  *)
     [4,num 0x80000000];
   (* SRAI value cases: zero shift, sign fill, maximal positive clear. *)
   directed_i_case 5 1 1 0x400          (* srai x1, 0x55555555, 0     *)
     [1,num 0x55555555];
   directed_i_case 5 3 1 (0x400 lor 31) (* srai x3, 0x80000000, 31    *)
     [1,num 0x80000000];
   directed_i_case 5 4 1 (0x400 lor 31) (* srai x4, 0xffffffff, 31    *)
     [1,num 0xffffffff];
   directed_i_case 5 1 1 (0x400 lor 31) (* srai x1, 0x7fffffff, 31    *)
     [1,num 0x7fffffff];
   (* SRAI register-shape case: rd = rs1. *)
   directed_i_case 5 3 3 (0x400 lor 1)  (* srai x3, x3, 1             *)
     [3,num 0x80000001];
   (* LUI value cases: zero, low bit, sign bit, all upper bits. *)
   directed_lui_case 1 0x00000;    (* lui  x1, 0x00000               *)
   directed_lui_case 3 0x00001;    (* lui  x3, 0x00001               *)
   directed_lui_case 4 0x80000;    (* lui  x4, 0x80000               *)
   directed_lui_case 5 0xfffff;    (* lui  x5, 0xfffff               *)
   (* LUI register-shape case: x0 destination must remain zero. *)
   directed_lui_case 0 0x7ffff;    (* lui  x0, 0x7ffff               *)
   (* MUL value cases: zero source, mixed sign, low-word wraparound. *)
   directed_r_case 1 0 1 0 3       (* mul  x1, 0x00000000, 0xffffffff *)
     [3,num 0xffffffff];
   directed_r_case 1 0 3 1 4       (* mul  x3, 0xffffffff, 0x7fffffff *)
     [1,num 0xffffffff; 4,num 0x7fffffff];
   directed_r_case 1 0 1 1 3       (* mul  x1, 0x80000000, 0xffffffff *)
     [1,num 0x80000000; 3,num 0xffffffff];
   directed_r_case 1 0 4 1 3       (* mul  x4, 0x00010000, 0x00010000 *)
     [1,num 0x00010000; 3,num 0x00010000];
   directed_r_case 1 0 1 1 4       (* mul  x1, 0x80000000, 0x00000002 *)
     [1,num 0x80000000; 4,num 2];
   (* MULH value cases: zero high word, sign fill, signed extremes. *)
   directed_r_case 1 1 4 1 3       (* mulh x4, 0x00000001, 0x00000001 *)
     [1,num 1; 3,num 1];
   directed_r_case 1 1 4 1 3       (* mulh x4, 0xffffffff, 0xffffffff *)
     [1,num 0xffffffff; 3,num 0xffffffff];
   directed_r_case 1 1 4 1 3       (* mulh x4, 0xffffffff, 0x00000002 *)
     [1,num 0xffffffff; 3,num 2];
   directed_r_case 1 1 4 1 3       (* mulh x4, 0x80000000, 0x00000002 *)
     [1,num 0x80000000; 3,num 2];
   directed_r_case 1 1 4 1 3       (* mulh x4, 0x80000000, 0xffffffff *)
     [1,num 0x80000000; 3,num 0xffffffff];
   directed_r_case 1 1 4 1 3       (* mulh x4, 0x80000000, 0x80000000 *)
     [1,num 0x80000000; 3,num 0x80000000];
   directed_r_case 1 1 4 1 3       (* mulh x4, 0x7fffffff, 0x7fffffff *)
     [1,num 0x7fffffff; 3,num 0x7fffffff];
   (* SLT and SLTU: the same operands compare differently signed and
      unsigned; equal operands and x0 sources give zero. *)
   directed_r_case 0 2 4 1 3       (* slt  x4, 0x80000000, 0x00000001 *)
     [1,num 0x80000000; 3,num 1];
   directed_r_case 0 3 4 1 3       (* sltu x4, 0x80000000, 0x00000001 *)
     [1,num 0x80000000; 3,num 1];
   directed_r_case 0 2 4 1 1       (* slt  x4, x1, x1                 *)
     [1,num 0x7fffffff];
   directed_r_case 0 3 4 0 1       (* sltu x4, x0, 0x00000001 (snez)  *)
     [1,num 1];
   (* SLTI and SLTIU sign-extend the immediate; SLTIU then compares
      unsigned, so -1 is the largest value. *)
   directed_i_case 2 4 1 (-1)      (* slti  x4, 0xfffffffe, -1        *)
     [1,num 0xfffffffe];
   directed_i_case 2 4 1 (-2048)   (* slti  x4, 0x7fffffff, -2048     *)
     [1,num 0x7fffffff];
   directed_i_case 3 4 1 (-1)      (* sltiu x4, 0x7fffffff, -1        *)
     [1,num 0x7fffffff];
   directed_i_case 3 4 1 1         (* sltiu x4, 0x00000000, 1 (seqz)  *)
     [];
   (* XORI, ORI, ANDI: sign-extended immediate extremes. *)
   directed_i_case 4 4 1 (-1)      (* xori x4, 0x12345678, -1 (not)   *)
     [1,num 0x12345678];
   directed_i_case 6 4 1 (-2048)   (* ori  x4, 0x00000001, -2048      *)
     [1,num 1];
   directed_i_case 7 4 1 (-2048)   (* andi x4, 0xffffffff, -2048      *)
     [1,num 0xffffffff];
   directed_i_case 7 4 1 2047      (* andi x4, 0xffffffff, 2047       *)
     [1,num 0xffffffff];
   (* XOR, OR, AND: self-operation and complementary operands. *)
   directed_r_case 0 4 4 1 1       (* xor  x4, x1, x1                 *)
     [1,num 0xdeadbeef];
   directed_r_case 0 6 4 1 3       (* or   x4, 0x0f0f0f0f, 0xf0f0f0f0 *)
     [1,num 0x0f0f0f0f; 3,num 0xf0f0f0f0];
   directed_r_case 0 7 4 1 3       (* and  x4, 0x0f0f0f0f, 0xf0f0f0f0 *)
     [1,num 0x0f0f0f0f; 3,num 0xf0f0f0f0];
   (* SRLI: zero fill from the sign bit and a zero shift. *)
   directed_i_case 5 4 1 31        (* srli x4, 0x80000000, 31         *)
     [1,num 0x80000000];
   directed_i_case 5 4 1 0         (* srli x4, 0xffffffff, 0          *)
     [1,num 0xffffffff];
   (* SLL, SRL, SRA use only the low five bits of rs2. *)
   directed_r_case 0 1 4 1 3       (* sll  x4, 0x00000001, 33         *)
     [1,num 1; 3,num 33];
   directed_r_case 0 1 4 1 3       (* sll  x4, 0x00000001, 0xffffffff *)
     [1,num 1; 3,num 0xffffffff];
   directed_r_case 0 5 4 1 3       (* srl  x4, 0x80000000, 31         *)
     [1,num 0x80000000; 3,num 31];
   directed_r_case 0 5 4 1 3       (* srl  x4, 0x80000000, 32         *)
     [1,num 0x80000000; 3,num 32];
   directed_r_case 0x20 5 4 1 3    (* sra  x4, 0x80000000, 31         *)
     [1,num 0x80000000; 3,num 31];
   directed_r_case 0x20 5 4 1 3    (* sra  x4, 0x80000000, 0xffffffe1 *)
     [1,num 0x80000000; 3,num 0xffffffe1];
   (* LB, LBU, LH, LHU: sign and zero extension at the top bit, the first
      and last scratch bytes, and negative offsets. *)
   directed_load_case 0 0 1        (* lb  x4, 1(sp)                   *)
     [0,num 0x00008000];
   directed_load_case 4 0 1        (* lbu x4, 1(sp)                   *)
     [0,num 0x00008000];
   directed_load_case 0 0 255      (* lb  x4, 255(sp)                 *)
     [63,num 0x7f000000];
   directed_load_case 4 256 (-256) (* lbu x4, -256(sp+256)            *)
     [0,num 0x000000ff];
   directed_load_case 1 0 2        (* lh  x4, 2(sp)                   *)
     [0,num 0x80000000];
   directed_load_case 5 0 2        (* lhu x4, 2(sp)                   *)
     [0,num 0x80000000];
   directed_load_case 1 256 (-2)   (* lh  x4, -2(sp+256)              *)
     [63,num 0x7fff0000];
   directed_load_case 5 256 (-2)   (* lhu x4, -2(sp+256)              *)
     [63,num 0xffff0000];
   (* SB, SH: only the low bits of x4 reach memory, and the other bytes of
      the surrounding word keep their values. *)
   directed_store_case 0 0 3       (* sb  x4, 3(sp)                   *)
     (num 0x12345678) [0,num 0xaaaaaaaa];
   directed_store_case 0 256 (-1)  (* sb  x4, -1(sp+256)              *)
     (num 0x123456ff) [63,num 0x55555555];
   directed_store_case 1 0 2       (* sh  x4, 2(sp)                   *)
     (num 0x12348765) [0,num 0xaaaaaaaa];
   directed_store_case 1 256 (-256) (* sh x4, -256(sp+256)            *)
     (num 0xffff8000) [0,num 0x55555555]];;

(*** The RV32 frontend constructs complete instructions directly from their
 *** encoding fields; it has no Arm-style bit templates or x86-style byte
 *** corpus. For example, an `ADD` case chooses `rd`, `rs1`, and `rs2` and
 *** calls `encode_r` with the ADD function bits. An `ADDI` case chooses
 *** the same register fields plus a signed 12-bit immediate and calls
 *** `encode_i`. The resulting 32-bit word is serialized in little-endian
 *** byte order for the executor.
 ***
 *** The campaign separates register-only and memory classes, following the
 *** Arm/x86 frontend split between register coverage and dedicated memory
 *** harness families. The selected straight-line forms are the RV32I
 *** register-register and register-immediate ALU instructions, `LUI`, `MUL`,
 *** `MULH`, and the loads and stores. `AUIPC`, `BNE`, and `JALR` are modeled
 *** by RV32 but are not selected here because they read or change the PC,
 *** which this campaign does not transport or check.
 ***
 *** Memory cases illustrate the difference from register-only cases. For
 *** one `LW` harness, `make_case` builds:
 ***
 ***   ADDI SP,SP,setup; LW rd,offset(SP); ADDI SP,SP,-setup
 ***
 *** The other loads and the stores use the same setup and cleanup. The chosen
 *** offset identifies one byte, halfword, or word, aligned to its size, in
 *** the private 256-byte scratch buffer, and `case_memop_index` tells the
 *** evaluator which instruction is the target.
 *** Thus setup and cleanup establish and restore the address while the target
 *** instruction is the operation whose memory behavior is checked.
 ***)

let rv32_cosim_executor = lazy
  (start_cosim_executor "S2N_BIGNUM_RV32IM_EXECUTOR"
    "riscv/proofs/cosim-runner" "rv32im" 95);;

let rec chop_list n values =
  if n = 0 then [],values
  else
    match values with
    | head::tail ->
        let prefix,suffix = chop_list (n - 1) tail in
        head::prefix,suffix
    | [] -> failwith "chop_list: index outside list";;

let RV32_MEMORY_SPLIT_TAC k =
  let tac =
    STRIP_ASSUME_TAC o
    CONV_RULE (BINOP_CONV(BINOP2_CONV
       (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) WORD_REDUCE_CONV)) o
    GEN_REWRITE_RULE I [el k (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] in
  EVERY_ASSUM (fun th -> try tac th with Failure _ -> ALL_TAC);;

let tac_before memop =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[regfile; CONS_11; VAL_WORD_GALOIS;
              RISCV_ZERO_REGISTER; READ_RVALUE] THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ENSURES_INIT_TAC "s0" THEN
  (if memop then MAP_EVERY RV32_MEMORY_SPLIT_TAC (1--4) else ALL_TAC)
and tac_main (memopidx: int option) execth states =
  begin match memopidx with
  | Some index ->
      let before,after = chop_list index states in
      (if before <> [] then RISCV_STEPS_TAC execth before else ALL_TAC) THEN
      (if after <> [] then RISCV_VSTEPS_TAC execth after else ALL_TAC)
  | None -> RISCV_STEPS_TAC execth states
  end
and tac_after memop =
  (if memop then MAP_EVERY RV32_MEMORY_SPLIT_TAC (0--4) else ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (if memop then CONV_TAC(ONCE_DEPTH_CONV READ_MEMORY_FULLMERGE_CONV)
   else ALL_TAC) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  (* After a byte or halfword store, the merged scratch word is a
     `word_join` of the byte values just substituted; evaluate it. *)
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[] THEN
  TRY(MONOTONE_MAYCHANGE_TAC) THEN
  PRINT_GOAL_TAC THEN NO_TAC;;

let cosimulate_case test_case =
  (*** The concrete and formal paths meet only after concrete execution:
   ***
   ***   bytes + input state -> RV32 executor -> output state
   ***        |                                      |
   ***        +--------- instantiate `template` -----+
   ***                               |
   ***                               v
   ***                       HOL proof obligation
   ***
   *** `template` is instantiated with the instruction bytes, input state,
   *** and returned output state. It therefore states, in effect, that the
   *** RV32 model terminates in exactly the state independently observed by
   *** the executor. `RISCV_MK_EXEC_RULE` derives symbolic execution rules
   *** for the same bytes; the setup, target, and cleanup are stepped in HOL,
   *** and the resulting theorem is proved with the RV32 state and memory
   *** model.
   ***)
  let instructions =
    test_case.case_setup @ [test_case.case_instruction] @
    test_case.case_cleanup in
  let bytes =
    itlist (fun instruction tail -> instruction_bytes instruction @ tail)
      instructions [] in
  let ibyteterm =
    mk_flist
      (map (curry mk_comb `word:num->byte` o mk_small_numeral) bytes) in
  let execution =
    cosim_execute (Lazy.force rv32_cosim_executor)
      (cosim_hex_of_bytes bytes)
      (map string_of_num test_case.case_input) in
  match execution with
  | Cosim_trap details ->
      Printf.printf "Unexpected RV32 trap: %s\n" (String.concat " " details);
      mk_numeral (num test_case.case_instruction),false
  | Cosim_ok output_words ->
      let output_state = map num_of_string output_words in
      let goal = subst
        [ibyteterm,`ibytes:byte list`;
         mk_flist (map mk_numeral test_case.case_input),
         `input_state:num list`;
         mk_flist (map mk_numeral output_state),`output_state:num list`]
        template in
      let execth = RISCV_MK_EXEC_RULE (REFL ibyteterm) in
      let target_index =
        match test_case.case_memop_index with
        | Some index -> index
        | None -> 0 in
      (* `case_memop_index` is an instruction index, while the theorem
         array returned by `RISCV_MK_EXEC_RULE` is indexed by byte offset. *)
      let target_offset = 4 * target_index in
      let decoded =
        (rand o rand o snd o strip_forall o concl o option_get)
          (snd execth).(target_offset) in
      let proof_tactic =
        PURE_REWRITE_TAC [fst execth] THEN
        tac_before (test_case.case_memop_index <> None) THEN
        tac_main test_case.case_memop_index execth (1--length instructions) THEN
        tac_after (test_case.case_memop_index <> None) in
      let result =
        try
          ignore (prove (goal,proof_tactic));
          true
        with error ->
          Printf.printf "RV32 proof failure: %s\n"
            (Printexc.to_string error);
          false in
      decoded,result;;

let instruction_kinds = length caseclasses;;
let time_limit_sec = sematest_seconds 2400.0;;
let case_limit = sematest_case_limit ();;

let run_case test_case count =
  let decoded,result = cosimulate_case test_case in
  if not result then begin
    Printf.printf "Error: term `%s`\n" (string_of_term decoded);
    failwith "RV32 simulator"
  end;
  Printf.printf "OK: %s\n" (string_of_term decoded);
  count + 1;;

let rec run_directed_cases start_time count cases =
  match cases with
  | [] -> count
  | test_case::rest ->
      let tested = run_case test_case count in
      if sematest_finished time_limit_sec case_limit start_time tested then
        tested
      else run_directed_cases start_time tested rest;;

let rec run_random_simulations start_time count =
  let kind = count mod instruction_kinds in
  let test_case = make_case kind in
  let tested = run_case test_case count in
  if sematest_finished time_limit_sec case_limit start_time tested then
    tested
  else run_random_simulations start_time tested;;

sematest_random_init ();;

let start_time = Unix.gettimeofday () in
let tested = run_directed_cases start_time 0 directed_cases in
let tested =
  if sematest_finished time_limit_sec case_limit start_time tested then tested
  else run_random_simulations start_time tested in
  Printf.printf "Finished RV32IM cosimulation testing: %d cases\n" tested;
  close_cosim_executor (Lazy.force rv32_cosim_executor);;
