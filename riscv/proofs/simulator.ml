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
 * points at the scratch buffer. PC is not transported: the code starts at
 * symbolic `pc` in the theorem, and the executor accepts only an ending at
 * the EBREAK it appends after the code, so the theorem requires the final
 * PC to be `pc` plus the code length. Cases for instructions that read or
 * change the PC subtract a PC-derived base before the end, so that every
 * transported value is independent of where the executor places the code.
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

(* The runner places the code in an internal code slot and uses an EBREAK
   right after it to return to the monitor. The HOL statement remains
   parameterized by symbolic `pc`, as in the Arm and x86 frontends. *)
let template =
 `nonoverlapping (word pc,LENGTH ibytes) (scratchpointer,256)
 ==> ensures riscv
       (\s. aligned_bytes_loaded s (word pc) ibytes /\
            aligned 4 scratchpointer /\
            read PC s = word pc /\
            read SP s = scratchpointer /\
            regfile scratchpointer s = input_state)
       (\s. read PC s = word (pc + LENGTH ibytes) /\
            read SP s = scratchpointer /\
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

(* B-type and J-type offsets are byte offsets with bit 0 implicit. *)

let encode_b offset rs2 rs1 funct3 =
  let bits = offset land 0x1fff in
  (((bits lsr 12) land 1) lsl 31) lor
  (((bits lsr 5) land 0x3f) lsl 25) lor
  ((rs2 land 0x1f) lsl 20) lor
  ((rs1 land 0x1f) lsl 15) lor
  ((funct3 land 7) lsl 12) lor
  (((bits lsr 1) land 0xf) lsl 8) lor
  (((bits lsr 11) land 1) lsl 7) lor 0x63;;

let encode_u immediate rd opcode =
  ((immediate land 0xfffff) lsl 12) lor ((rd land 0x1f) lsl 7) lor opcode;;

let encode_j offset rd =
  let bits = offset land 0x1fffff in
  (((bits lsr 20) land 1) lsl 31) lor
  (((bits lsr 1) land 0x3ff) lsl 21) lor
  (((bits lsr 11) land 1) lsl 20) lor
  (((bits lsr 12) land 0xff) lsl 12) lor
  ((rd land 0x1f) lsl 7) lor 0x6f;;

let instruction_bytes instruction =
  [instruction land 0xff;
   (instruction lsr 8) land 0xff;
   (instruction lsr 16) land 0xff;
   (instruction lsr 24) land 0xff];;

let random_register () =
  let register = Random.int 31 in
  if register < 2 then register else register + 1;;

(* A random transported register other than x0 and the listed ones. *)

let rec random_register_except registers =
  let register = random_register () in
  if register = 0 || mem register registers
  then random_register_except registers
  else register;;

(* `case_setup` and `case_cleanup` are the instructions placed before and
   after the instruction under test. Straight-line cases execute all of
   them once, in order; control-flow cases jump over some of them.
   `case_steps` is the number of instructions executed before the EBREAK
   that the executor appends after the code. *)

type rv32_test_case =
 { case_setup: int list;
   case_instruction: int;
   case_cleanup: int list;
   case_steps: int;
   case_memop_index: int option;
   case_input: num list };;

type rv32_case_builder = unit -> rv32_test_case;;

let straight_case setup instruction cleanup memop input =
  { case_setup = setup; case_instruction = instruction;
    case_cleanup = cleanup;
    case_steps = length setup + 1 + length cleanup;
    case_memop_index = memop; case_input = input };;

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
  straight_case [] (encode_r funct7 rs2 rs1 funct3 rd) [] None input;;

let make_i_case funct3 input =
  let rd = random_register ()
  and rs1 = random_register ()
  and immediate = Random.int 4096 - 2048 in
  straight_case [] (encode_i immediate rs1 funct3 rd 0x13) [] None input;;

let make_shift_case funct7 funct3 input =
  let rd = random_register ()
  and rs1 = random_register ()
  and shift = Random.int 32 in
  straight_case []
    (encode_i ((funct7 lsl 5) lor shift) rs1 funct3 rd 0x13) [] None input;;

let make_lui_case input =
  let rd = random_register ()
  and immediate = Random.int 0x100000 in
  straight_case [] (encode_u immediate rd 0x37) [] None input;;

let make_load_case funct3 size input =
  let rd = random_register () in
  let _,setup,immediate = memory_operands size in
  straight_case [encode_i setup 2 0 2 0x13]
    (encode_i immediate 2 funct3 rd 0x03)
    [encode_i (-setup) 2 0 2 0x13] (Some 1) input;;

let make_store_case funct3 size input =
  let rs2 = random_register () in
  let _,setup,immediate = memory_operands size in
  straight_case [encode_i setup 2 0 2 0x13]
    (encode_s immediate rs2 2 funct3)
    [encode_i (-setup) 2 0 2 0x13] (Some 1) input;;

(*** AUIPC, the branches, JAL, and JALR read or change the PC. The executor
 *** places the code at an address that the theorem leaves symbolic, so
 *** these cases must not leave a PC-dependent value in a transported
 *** register. An AUIPC result or a link address is turned into an offset
 *** by subtracting a base register, and the base is then cleared. The base
 *** always comes from a different instruction from the one under test: an
 *** AUIPC result is measured against a JAL link, and the links against an
 *** AUIPC result. A model that used the wrong PC in one of them therefore
 *** gets a different offset, while all of them using the same wrong PC
 *** would make the control flow land on the wrong instruction.
 ***
 *** The instructions that a correct jump skips are fillers that write 3 to
 *** a marker register, and the theorem fixes both the number of executed
 *** instructions and the final PC, so a jump to the wrong place fails the
 *** proof. Offsets are limited by the Sail executor's code slot, which has
 *** room for 63 instructions before its EBREAK.
 ***)

let rv32_code_words = 63;;

let filler marker count =
  map (fun _ -> encode_i 3 0 0 marker 0x13) (1--count);;

(* SUB r, r, base for each listed register, then SUB base, base, base. *)

let rebase registers base =
  map (fun register -> encode_r 0x20 base register 0 register) registers @
  [encode_r 0x20 base base 0 base];;

(* `jal base, 4` puts the address of the AUIPC into `base`, so the final
   `rd` is the immediate shifted left by 12. *)

let auipc_case rd base immediate input =
  straight_case [encode_j 4 base] (encode_u immediate rd 0x17)
    (rebase [rd] base) None input;;

let make_auipc_case input =
  let rd = random_register () in
  let base = random_register_except [rd] in
  auipc_case rd base (Random.int 0x100000) input;;

(* A branch with a positive `words` is the first instruction and jumps
   forward by `words` instructions when taken:

     0         B rs1, rs2, 4 * words
     1         JAL x0, 4 * words           (to the end)
     2..w-1    ADDI marker, x0, 3
     w         ADDI marker, x0, 2

   With `words` = 1 the code is the branch and the last ADDI only. A branch
   with a negative `words` sits at index b = 1 - words and jumps back to
   index 1:

     0         JAL x0, 4 * b               (to the branch)
     1         JAL x0, 4 * (b + 1)         (to the end)
     2..b-1    ADDI marker, x0, 3
     b         B rs1, rs2, 4 * words
     b+1       ADDI marker, x0, 1

   Both paths execute the same number of instructions. The marker, which
   starts at 0, shows which one was taken, except for `words` = 1: there
   the target is the next instruction, so both paths are the same. *)

let branch_case funct3 rs1 rs2 marker words input =
  let branch = encode_b (4 * words) rs2 rs1 funct3
  and input = set_input_register marker num_0 input in
  if words = 1 then
    { case_setup = []; case_instruction = branch;
      case_cleanup = [encode_i 2 0 0 marker 0x13];
      case_steps = 2; case_memop_index = None; case_input = input }
  else if words > 1 then
    { case_setup = []; case_instruction = branch;
      case_cleanup =
        [encode_j (4 * words) 0] @ filler marker (words - 2) @
        [encode_i 2 0 0 marker 0x13];
      case_steps = 2; case_memop_index = None; case_input = input }
  else if words < 0 then
    let b = 1 - words in
    { case_setup =
        [encode_j (4 * b) 0; encode_j (4 * (b + 1)) 0] @
        filler marker (b - 2);
      case_instruction = branch;
      case_cleanup = [encode_i 1 0 0 marker 0x13];
      case_steps = 3; case_memop_index = None; case_input = input }
  else failwith "branch_case: a taken branch to itself does not end";;

(* Random operands are rarely equal, so make the second operand a copy of
   the first in a quarter of the cases. *)

let make_branch_case funct3 input =
  let rs1 = random_register ()
  and rs2 = random_register () in
  let marker = random_register_except [rs1; rs2] in
  let input =
    if Random.int 4 <> 0 || rs1 = rs2 then input
    else if rs2 = 0 then set_input_register rs1 num_0 input
    else set_input_register rs2
           (el (transport_register_index rs1) input) input in
  let words =
    if Random.bool () then 1 + Random.int (rv32_code_words - 1)
    else -1 - Random.int (rv32_code_words - 3) in
  branch_case funct3 rs1 rs2 marker words input;;

(* A JAL with a positive `words` jumps forward over `words - 1` fillers.
   One with a negative `words` sits at index b = 2 - words and jumps back
   to index 2, which jumps to the end:

     0         AUIPC base, 0
     1         JAL x0, 4 * (b - 1)         (to the JAL under test)
     2         JAL x0, 4 * (b - 1)         (to the end)
     3..b-1    ADDI marker, x0, 3
     b         JAL rd, 4 * words
     b+1       SUB rd, rd, base
     b+2       SUB base, base, base *)

let jal_case rd base marker words input =
  let input = set_input_register marker num_0 input in
  if words > 0 then
    { case_setup = [encode_u 0 base 0x17];
      case_instruction = encode_j (4 * words) rd;
      case_cleanup = filler marker (words - 1) @ rebase [rd] base;
      case_steps = 4; case_memop_index = None; case_input = input }
  else if words < 0 then
    let b = 2 - words in
    { case_setup =
        [encode_u 0 base 0x17; encode_j (4 * (b - 1)) 0;
         encode_j (4 * (b - 1)) 0] @ filler marker (b - 3);
      case_instruction = encode_j (4 * words) rd;
      case_cleanup = rebase [rd] base;
      case_steps = 6; case_memop_index = None; case_input = input }
  else failwith "jal_case: a JAL to itself does not end";;

let make_jal_case input =
  let rd = random_register () in
  let base = random_register_except [rd] in
  let marker = random_register_except [rd; base] in
  let words =
    if Random.bool () then 1 + Random.int (rv32_code_words - 3)
    else -1 - Random.int (rv32_code_words - 5) in
  jal_case rd base marker words input;;

(* JALR jumps to the first instruction after `words - 1` fillers. AUIPC and
   ADDI set `rs1` so that `rs1 + immediate` is that address plus `low`
   (0 or 1), which JALR clears:

     0         AUIPC base, 0
     1         AUIPC rs1, hi
     2         ADDI rs1, rs1, lo
     3         JALR rd, rs1, immediate
     4..       fillers, then SUB rd, rd, base; SUB rs1, rs1, base (unless
               rs1 = rd); SUB base, base, base *)

let jalr_case rd rs1 base marker words immediate low input =
  let offset = 4 * (3 + words) - 4 - immediate + low in
  let hi = (offset + 0x800) asr 12 in
  let lo = offset - (hi lsl 12) in
  let cleanup =
    filler marker (words - 1) @
    rebase (if rs1 = rd then [rd] else [rd; rs1]) base in
  { case_setup =
      [encode_u 0 base 0x17; encode_u hi rs1 0x17;
       encode_i lo rs1 0 rs1 0x13];
    case_instruction = encode_i immediate rs1 0 rd 0x67;
    case_cleanup = cleanup;
    case_steps = 4 + length cleanup - (words - 1);
    case_memop_index = None;
    case_input = set_input_register marker num_0 input };;

let make_jalr_case input =
  let rd = random_register () in
  let rs1 = random_register_except [] in
  let base = random_register_except [rd; rs1] in
  let marker = random_register_except [rd; rs1; base] in
  jalr_case rd rs1 base marker (1 + Random.int (rv32_code_words - 6))
    (Random.int 4096 - 2048) (Random.int 2) input;;

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
    make_shift_case 0 5;           (* SRLI   *)
    make_r_case 1 2;               (* MULHSU *)
    make_r_case 1 3;               (* MULHU  *)
    make_r_case 1 4;               (* DIV    *)
    make_r_case 1 5;               (* DIVU   *)
    make_r_case 1 6;               (* REM    *)
    make_r_case 1 7];;             (* REMU   *)

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

let controlclasses : rv32_case_builder list =
  map (fun make -> fun () -> make (make_input_state (Random.int 65)))
   [make_auipc_case;
    make_branch_case 0;            (* BEQ    *)
    make_branch_case 1;            (* BNE    *)
    make_branch_case 4;            (* BLT    *)
    make_branch_case 5;            (* BGE    *)
    make_branch_case 6;            (* BLTU   *)
    make_branch_case 7;            (* BGEU   *)
    make_jal_case;
    make_jalr_case];;

let caseclasses = regclasses @ memclasses @ controlclasses;;

let make_case kind =
  if kind < 0 || kind >= length caseclasses
  then failwith "make_case: bad instruction kind"
  else el kind caseclasses ();;

let directed_r_case funct7 funct3 rd rs1 rs2 assignments =
  straight_case [] (encode_r funct7 rs2 rs1 funct3 rd) [] None
    (directed_input_state assignments);;

let directed_i_case funct3 rd rs1 immediate assignments =
  straight_case [] (encode_i immediate rs1 funct3 rd 0x13) [] None
    (directed_input_state assignments);;

let directed_lui_case rd immediate =
  straight_case [] (encode_u immediate rd 0x37) [] None
    (directed_input_state []);;

(* Run one load or store with SP adjusted by `setup` around it, as the random
   memory cases do, after setting the listed registers and scratch words.
   The directed loads write x4, and the directed stores store x4. *)

let directed_memory_case setup instruction assignments words =
  straight_case [encode_i setup 2 0 2 0x13] instruction
    [encode_i (-setup) 2 0 2 0x13] (Some 1)
    (itlist (fun (index,value) -> list_update (31 + index) value)
       words (directed_input_state assignments));;

let directed_load_case funct3 setup immediate words =
  directed_memory_case setup (encode_i immediate 2 funct3 4 0x03) [] words;;

let directed_store_case funct3 setup immediate value words =
  directed_memory_case setup (encode_s immediate 4 2 funct3) [4,value] words;;

(* The directed branches compare x1 with x3 and mark the path in x4, with
   the layouts of the random branches. A branch that is not taken ignores
   its offset, so the untaken cases can use offsets that no layout reaches
   or that are not multiples of four. *)

let directed_branch_case funct3 words x1 x3 =
  branch_case funct3 1 3 4 words
    (directed_input_state [1,num x1; 3,num x3]);;

let directed_untaken_case funct3 offset x1 x3 =
  straight_case [] (encode_b offset 3 1 funct3) [encode_i 1 0 0 4 0x13] None
    (directed_input_state [1,num x1; 3,num x3]);;

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
     (num 0xffff8000) [0,num 0x55555555];
   (* MULHSU: rs1 signed, rs2 unsigned, so 0xffffffff is -1 only as rs1. *)
   directed_r_case 1 2 4 1 3       (* mulhsu x4, 0xffffffff, 0xffffffff *)
     [1,num 0xffffffff; 3,num 0xffffffff];
   directed_r_case 1 2 4 1 3       (* mulhsu x4, 0x80000000, 0xffffffff *)
     [1,num 0x80000000; 3,num 0xffffffff];
   directed_r_case 1 2 4 1 3       (* mulhsu x4, 0x7fffffff, 0x80000000 *)
     [1,num 0x7fffffff; 3,num 0x80000000];
   (* MULHU: unsigned extremes. *)
   directed_r_case 1 3 4 1 3       (* mulhu  x4, 0xffffffff, 0xffffffff *)
     [1,num 0xffffffff; 3,num 0xffffffff];
   directed_r_case 1 3 4 1 3       (* mulhu  x4, 0x80000000, 0x00000002 *)
     [1,num 0x80000000; 3,num 2];
   (* DIV, DIVU, REM, REMU: zero divisor, signed overflow, and rounding
      toward zero with each sign. *)
   directed_r_case 1 4 4 1 0       (* div  x4, 0x12345678, x0         *)
     [1,num 0x12345678];
   directed_r_case 1 5 4 1 0       (* divu x4, 0x12345678, x0         *)
     [1,num 0x12345678];
   directed_r_case 1 6 4 1 0       (* rem  x4, 0x12345678, x0         *)
     [1,num 0x12345678];
   directed_r_case 1 7 4 1 0       (* remu x4, 0x87654321, x0         *)
     [1,num 0x87654321];
   directed_r_case 1 4 4 1 3       (* div  x4, 0x87654321, 0          *)
     [1,num 0x87654321];
   directed_r_case 1 6 4 1 3       (* rem  x4, 0x87654321, 0          *)
     [1,num 0x87654321];
   directed_r_case 1 4 4 1 3       (* div  x4, 0x80000000, 0xffffffff *)
     [1,num 0x80000000; 3,num 0xffffffff];
   directed_r_case 1 6 4 1 3       (* rem  x4, 0x80000000, 0xffffffff *)
     [1,num 0x80000000; 3,num 0xffffffff];
   directed_r_case 1 4 4 1 3       (* div  x4, -7, 2                  *)
     [1,num 0xfffffff9; 3,num 2];
   directed_r_case 1 6 4 1 3       (* rem  x4, -7, 2                  *)
     [1,num 0xfffffff9; 3,num 2];
   directed_r_case 1 4 4 1 3       (* div  x4, 7, -2                  *)
     [1,num 7; 3,num 0xfffffffe];
   directed_r_case 1 6 4 1 3       (* rem  x4, 7, -2                  *)
     [1,num 7; 3,num 0xfffffffe];
   directed_r_case 1 5 4 1 3       (* divu x4, 0xfffffff9, 2          *)
     [1,num 0xfffffff9; 3,num 2];
   directed_r_case 1 7 4 1 3       (* remu x4, 0xfffffff9, 2          *)
     [1,num 0xfffffff9; 3,num 2];
   (* AUIPC: zero, the sign bit, all upper bits, and an x0 destination. *)
   auipc_case 1 3 0x00000 (directed_input_state []);
   auipc_case 4 5 0x80000 (directed_input_state []);
   auipc_case 5 1 0xfffff (directed_input_state []);
   auipc_case 0 1 0x12345 (directed_input_state []);
   (* Branches: each condition taken and not taken, signed against unsigned
      order, equal and x0 operands, and the shortest and longest offsets
      forward and backward. *)
   directed_branch_case 0 (rv32_code_words - 1) 5 5;
                                   (* beq  5, 5: taken                *)
   directed_branch_case 0 (3 - rv32_code_words) 5 6;
                                   (* beq  5, 6: not taken            *)
   branch_case 0 0 0 4 (-1)        (* beq  x0, x0: taken              *)
     (directed_input_state []);
   directed_branch_case 0 1 5 5;   (* beq  5, 5, +4: next instruction *)
   branch_case 1 0 0 4 2           (* bne  x0, x0: not taken          *)
     (directed_input_state []);
   directed_branch_case 1 2 0 0xffffffff;
                                   (* bne  0, -1: taken               *)
   directed_branch_case 4 3 0x80000000 1;
                                   (* blt  -2^31, 1: taken            *)
   directed_branch_case 6 3 0x80000000 1;
                                   (* bltu 2^31, 1: not taken         *)
   directed_branch_case 4 (-2) 7 7;
                                   (* blt  7, 7: not taken            *)
   directed_branch_case 5 (-2) 7 7;
                                   (* bge  7, 7: taken                *)
   directed_branch_case 5 5 0x7fffffff 0x80000000;
                                   (* bge  2^31-1, -2^31: taken       *)
   directed_branch_case 7 (-5) 0xffffffff 1;
                                   (* bgeu 2^32-1, 1: taken           *)
   directed_branch_case 7 5 0 1;   (* bgeu 0, 1: not taken            *)
   directed_branch_case 6 (-3) 0 0xffffffff;
                                   (* bltu 0, 2^32-1: taken           *)
   directed_untaken_case 0 2 1 2;  (* beq  1, 2, +2                   *)
   directed_untaken_case 1 (-4096) 7 7;
                                   (* bne  7, 7, -4096                *)
   directed_untaken_case 6 4094 2 1;
                                   (* bltu 2, 1, +4094                *)
   directed_untaken_case 5 (-4094) 1 2;
                                   (* bge  1, 2, -4094                *)
   (* JAL: the shortest and longest offsets both ways, and an x0 link. *)
   jal_case 1 5 6 1 (directed_input_state []);
   jal_case 0 5 6 (rv32_code_words - 3) (directed_input_state []);
   jal_case 31 5 6 (-1) (directed_input_state []);
   jal_case 4 5 6 (5 - rv32_code_words) (directed_input_state []);
   (* JALR: bit 0 of the sum set or clear, immediate extremes, rd = rs1,
      and an x0 link. *)
   jalr_case 1 3 5 6 1 0 1 (directed_input_state []);
   jalr_case 1 3 5 6 1 0 0 (directed_input_state []);
   jalr_case 4 3 5 6 (rv32_code_words - 6) (-2048) 1
     (directed_input_state []);
   jalr_case 3 3 5 6 2 2047 0 (directed_input_state []);
   jalr_case 0 3 5 6 3 (-1) 1 (directed_input_state [])];;

(*** The RV32 frontend constructs complete instructions directly from their
 *** encoding fields; it has no Arm-style bit templates or x86-style byte
 *** corpus. For example, an `ADD` case chooses `rd`, `rs1`, and `rs2` and
 *** calls `encode_r` with the ADD function bits. An `ADDI` case chooses
 *** the same register fields plus a signed 12-bit immediate and calls
 *** `encode_i`. The resulting 32-bit word is serialized in little-endian
 *** byte order for the executor.
 ***
 *** The campaign has register-only, memory, and control-flow classes,
 *** following the Arm/x86 frontend split between register coverage and
 *** dedicated harness families. The selected forms are the RV32I
 *** register-register and register-immediate ALU instructions, `LUI`, the
 *** M instructions, the loads and stores, `AUIPC`, the six branches,
 *** `JAL`, and `JALR`.
 ***
 *** Some behavior is not compared because the model claims nothing there:
 *** a halfword or word access, taken branch, or jump whose address is not
 *** aligned, for which the model allows every successor state. Both
 *** executors implement the C extension and continue at a two-byte-aligned
 *** jump target, so there is no common result to compare either. Taken
 *** branches and JALs stay within the code slot, so their offsets have
 *** bit 1 clear and bits 8 and above equal to the sign; the untaken
 *** directed branches still decode other offsets.
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

(*** Control-flow cases leave PC-relative values in registers, such as
 *** `word (pc + 8)` after a JAL, and RISCV_CONV leaves arithmetic on them
 *** unevaluated. After each step, `RV32_PC_VALUES_TAC` rewrites
 *** `word_add (word (pc + a)) (word b)` to `word (pc + c)`, and clears bit 0
 *** of `word (pc + a)` as JALR does, using the alignment of `pc`.
 ***
 *** RISCV_CONV decides whether the new PC is aligned by rewriting with the
 *** assumptions only, without evaluating words. Before a JALR step,
 *** `RV32_STEP_TAC` therefore adds the target of the JALR in the form
 *** above, as two equations, one per spelling of the mask. Before a branch
 *** step, it adds the value of the branch condition, so that an untaken
 *** branch whose offset is not a multiple of four does not leave the
 *** alignment undecided. The facts are removed again after the step.
 ***)

let RV32_PC_OFFSET_SUB = prove
 (`(!pc a b. word_sub (word (pc + a)) (word (pc + b)):int32 =
             word_sub (word a) (word b)) /\
   (!pc a. word_sub (word (pc + a)) (word pc):int32 = word a) /\
   (!pc b. word_sub (word pc) (word (pc + b)):int32 =
           word_sub (word 0) (word b))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* `pctm` is the symbolic code address `pc`; both conversions below leave
   other words alone. *)

let rv32_is_pc_relative pctm tm =
  tm = pctm || is_binary "+" tm && lhand tm = pctm && is_numeral (rand tm);;

let RV32_PC_ADD_CONV pctm =
  let pth = prove
   (`(!pc a b. word_add (word (pc + a)) (word b):int32 =
               word (pc + (a + b))) /\
     (!pc b. word_add (word pc) (word b):int32 = word (pc + b))`,
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]) in
  fun tm ->
    match tm with
    | Comb(Comb(Const("word_add",_),Comb(Const("word",_),x)),
           Comb(Const("word",_),n))
        when rv32_is_pc_relative pctm x && is_numeral n ->
        (GEN_REWRITE_CONV I [pth] THENC
         RAND_CONV (TRY_CONV (RAND_CONV NUM_REDUCE_CONV)) THENC
         TRY_CONV WORD_PC_PLUS_CONV) tm
    | _ -> failwith "RV32_PC_ADD_CONV";;

let RV32_ALIGNED_BIT0 = prove
 (`!x:int32. aligned 4 x ==> ~bit 0 x`,
  REWRITE_TAC[aligned; BIT_VAL; EXP; DIV_1; GSYM NOT_EVEN; divides] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[EVEN_MULT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let RV32_JALR_MASK_ADD = prove
 (`!x y:int32.
     ~bit 0 x
     ==> word_and (word_add x y) (word 4294967294) =
         word_add x (word_and y (word 4294967294))`,
  BITBLAST_TAC);;

let rv32_aligned_pc_th asl =
  let loaded_th =
    find (can (term_match [] `aligned_bytes_loaded s (word pc) l`) o concl)
      (map snd asl) in
  MATCH_MP aligned_bytes_loaded_aligned loaded_th;;

let RV32_PC_MASK_CONV pc_aligned_th =
  let mask_th =
    MATCH_MP (SPEC (rand (concl pc_aligned_th)) RV32_JALR_MASK_ADD)
      (MATCH_MP RV32_ALIGNED_BIT0 pc_aligned_th)
  and pctm = rand (rand (concl pc_aligned_th)) in
  fun tm ->
    match tm with
    | Comb(Comb(Const("word_and",_),Comb(Const("word",_),x)),
           Comb(Const("word",_),m))
        when m = `4294967294` && rv32_is_pc_relative pctm x ->
        (LAND_CONV (TRY_CONV (GEN_REWRITE_CONV I [WORD_ADD])) THENC
         GEN_REWRITE_CONV I [mask_th] THENC
         RAND_CONV WORD_REDUCE_CONV THENC
         GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
         TRY_CONV WORD_PC_PLUS_CONV) tm
    | _ -> failwith "RV32_PC_MASK_CONV";;

let RV32_PC_VALUES_TAC : tactic = fun (asl,w) ->
  let pc_aligned_th = rv32_aligned_pc_th asl in
  let pctm = rand (rand (concl pc_aligned_th)) in
  RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV
    (RV32_PC_ADD_CONV pctm ORELSEC RV32_PC_MASK_CONV pc_aligned_th)))
    (asl,w);;

let rv32_pc_offset tm =
  if tm = `pc:num` then 0 else
  let l,r = dest_binary "+" tm in
  if l = `pc:num` then dest_small_numeral r
  else failwith "rv32_pc_offset";;

let rv32_read component state =
  mk_comb(mk_comb(`read:(riscvstate,int32)component->riscvstate->int32`,
                  component),state);;

let rv32_branch_definitions =
  [riscv_BEQ; riscv_BNE; riscv_BLT; riscv_BGE; riscv_BLTU; riscv_BGEU];;

let rv32_step_facts execth (asl,w) =
  let state = rand w and ths = map snd asl in
  let value_th component =
    let read = rv32_read component state in
    find (fun th -> is_eq (concl th) && lhs (concl th) = read) ths in
  let value component = rhs (concl (value_th component)) in
  match (snd execth).(rv32_pc_offset (rand (value `PC`))) with
  | None -> []
  | Some decode_th ->
      let instruction = rand (rand (snd (strip_forall (concl decode_th)))) in
      match strip_comb instruction with
      | Const("riscv_JALR",_),[_; rs1; immediate] ->
          let base = try value rs1 with Failure _ -> `word 0:int32` in
          if not (can (rv32_pc_offset o rand) base) then [] else
          let masked =
            mk_comb(mk_comb(`word_and:int32->int32->int32`,
              mk_comb(mk_comb(`word_add:int32->int32->int32`,base),
                      immediate)),
              `word 4294967294:int32`) in
          let pc_aligned_th = rv32_aligned_pc_th asl in
          let target =
            (LAND_CONV (RV32_PC_ADD_CONV (rand (rand (concl pc_aligned_th))))
             THENC RV32_PC_MASK_CONV pc_aligned_th) masked in
          [target;
           CONV_RULE (LAND_CONV (RAND_CONV (K (SYM (WORD_REDUCE_CONV
             `word_not (word 1):int32`))))) target]
      | Const(_,_),[rs1; rs2; _]
          when exists (can (fun th -> PART_MATCH lhs th instruction))
                 rv32_branch_definitions ->
          let definition =
            tryfind (fun th -> PART_MATCH lhs th instruction)
              rv32_branch_definitions in
          let body =
            rhs (concl (BETA_CONV (mk_comb (rhs (concl definition),state)))) in
          let is_condition tm =
            is_cond tm &&
            not (can (find_term (fun t -> is_const t &&
                                          name_of t = "aligned"))
                   (lhand (rator tm))) in
          let condition = lhand (rator (find_term is_condition body)) in
          let operand_ths =
            mapfilter value_th (filter (fun r -> r <> `ZERO`) [rs1; rs2]) in
          let condition =
            rhs (concl (PURE_REWRITE_CONV operand_ths condition)) in
          let fact =
            (PURE_REWRITE_CONV[RISCV_ZERO_REGISTER; READ_RVALUE] THENC
             WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC INT_REDUCE_CONV)
            condition in
          if is_const (rhs (concl fact)) then [fact] else []
      | _ -> [];;

let RV32_STEP_TAC execth n : tactic = fun (asl,w) ->
  let facts = rv32_step_facts execth (asl,w) in
  let is_fact th = exists (fun fact -> concl fact = concl th) facts in
  (MAP_EVERY ASSUME_TAC facts THEN
   RISCV_STEPS_TAC execth [n] THEN
   REPEAT (FIRST_X_ASSUM (fun th ->
     if is_fact th then ALL_TAC else NO_TAC)) THEN
   RV32_PC_VALUES_TAC) (asl,w);;

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
  | None -> MAP_EVERY (RV32_STEP_TAC execth) states
  end
and tac_after memop =
  (if memop then MAP_EVERY RV32_MEMORY_SPLIT_TAC (0--4) else ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (if memop then CONV_TAC(ONCE_DEPTH_CONV READ_MEMORY_FULLMERGE_CONV)
   else REWRITE_TAC[RV32_PC_OFFSET_SUB]) THEN
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
   *** for the same bytes; the executed instructions are stepped in HOL,
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
  let execth = RISCV_MK_EXEC_RULE (REFL ibyteterm) in
  (* The theorem array returned by `RISCV_MK_EXEC_RULE` is indexed by byte
     offset. *)
  let decoded =
    match (snd execth).(4 * length test_case.case_setup) with
    | Some th -> (rand o rand o snd o strip_forall o concl) th
    | None -> mk_numeral (num test_case.case_instruction) in
  let attempt goal tactic =
    try
      ignore (prove (goal,tactic));
      true
    with error ->
      Printf.printf "RV32 proof failure: %s\n" (Printexc.to_string error);
      false in
  let execution =
    cosim_execute (Lazy.force rv32_cosim_executor)
      (cosim_hex_of_bytes bytes)
      (map string_of_num test_case.case_input) in
  match execution with
  | Cosim_trap details ->
      Printf.printf "Unexpected RV32 trap: %s\n" (String.concat " " details);
      decoded,false
  | Cosim_ok output_words ->
      let output_state = map num_of_string output_words in
      let goal = subst
        [ibyteterm,`ibytes:byte list`;
         mk_flist (map mk_numeral test_case.case_input),
         `input_state:num list`;
         mk_flist (map mk_numeral output_state),`output_state:num list`]
        template in
      let proof_tactic =
        PURE_REWRITE_TAC [fst execth] THEN
        tac_before (test_case.case_memop_index <> None) THEN
        tac_main test_case.case_memop_index execth (1--test_case.case_steps) THEN
        tac_after (test_case.case_memop_index <> None) in
      decoded,attempt goal proof_tactic;;

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
