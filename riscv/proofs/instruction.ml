(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Partial RV32IM state and instruction semantics.                           *)
(* ========================================================================= *)

(* Instruction behavior follows The RISC-V Instruction Set Manual, Volume I:
   Unprivileged Architecture, specifically RV32I version 2.1 and the M
   extension version 2.0. ABI register names follow section 1.1, "Integer
   Register Convention", of the RISC-V ABIs Specification. Privilege modes,
   CSRs, and trap state are specified separately in The RISC-V Instruction
   Set Manual, Volume II: Privileged Architecture.

   https://docs.riscv.org/reference/isa/unpriv/rv32.html
   https://docs.riscv.org/reference/isa/unpriv/m-st-ext.html
   https://riscv-non-isa.github.io/riscv-elf-psabi-doc/

   The state uses 32-bit PCs, registers, and memory addresses.

   The model covers the instructions used by the mldsa-native RV32 backend. It
   omits privileged state, exceptions, CSRs, and the compressed extension.

   MUL and MULH emit no operand-dependent event. Constant-time theorems using
   this model therefore require data-independent multiply latency on the
   target implementation.

   Misaligned word accesses and instruction targets use `ASSIGNS entirety`,
   which permits any successor state. This conservatively abstracts omitted
   exception and trap handling; it does not claim that the architecture
   defines such cases as undefined behavior. Normal execution proofs establish
   four-byte alignment and do not use this case. *)

(* TODO: This is complete only for the unprivileged RV32IM register state:
   x0--x31 and pc. The M extension adds no architectural registers. A faithful
   RISC-V hart model must also represent the implemented privilege modes and
   CSRs, including trap status, cause, exception PC, trap vector, interrupt,
   and counter state.

   It must also model the execution environment and any enabled extension
   state, for example reservation state for A or floating-point and vector
   registers for F, D, and V. The flat memory below omits address translation,
   access control, memory-mapped I/O, and memory-ordering behavior. `events` is
   ghost state for proofs, not an architectural register. *)

new_type_abbrev
 ("riscv_uarch_event",`:32 address_uarch_event`);;

let riscvstate_INDUCT,riscvstate_RECURSION,riscvstate_COMPONENTS =
  define_auto_record_type
   "riscvstate =
     { PC: int32;                         // program counter
       registers: 5 word -> int32;       // integer registers
       memory: int32 -> byte;             // memory
       events: riscv_uarch_event list     // observable events
     }";;

loadt "common/code_loading.ml";;

(* ------------------------------------------------------------------------- *)
(* Tweak for aligned_bytes_loaded s (word pc) (APPEND program data).         *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_BYTES_LOADED_APPEND_CLAUSE = prove
 (`aligned_bytes_loaded s (word pc) (APPEND prog data) /\
   read PC s = pcin /\
   rest <=>
   aligned_bytes_loaded s (word pc) prog /\
   read PC s = pcin /\
   bytes_loaded s (word(pc + LENGTH prog)) data /\
   rest`,
  REWRITE_TAC[aligned_bytes_loaded_append_alt; GSYM WORD_ADD; CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Integer-register views and ABI aliases.                                   *)
(* ------------------------------------------------------------------------- *)

let XREG = define
 `XREG n = registers :> element (word n)`;;

(* Precompute the concrete register components for component automation. *)

add_component_alias_thms
 (map (fun n -> let tm = mk_comb(`XREG`,mk_small_numeral n) in
                (GEN_REWRITE_CONV I [XREG] THENC NUM_REDUCE_CONV) tm)
      (0--31));;

(* x0 reads as zero and ignores writes. The underlying register-file entry is
   consequently not observable through any decoded instruction. *)

let X0 = define
 `X0:(riscvstate,int32)component = rvalue (word 0)`;;

let X1  = define `X1  = XREG 1`
and X2  = define `X2  = XREG 2`
and X3  = define `X3  = XREG 3`
and X4  = define `X4  = XREG 4`
and X5  = define `X5  = XREG 5`
and X6  = define `X6  = XREG 6`
and X7  = define `X7  = XREG 7`
and X8  = define `X8  = XREG 8`
and X9  = define `X9  = XREG 9`
and X10 = define `X10 = XREG 10`
and X11 = define `X11 = XREG 11`
and X12 = define `X12 = XREG 12`
and X13 = define `X13 = XREG 13`
and X14 = define `X14 = XREG 14`
and X15 = define `X15 = XREG 15`
and X16 = define `X16 = XREG 16`
and X17 = define `X17 = XREG 17`
and X18 = define `X18 = XREG 18`
and X19 = define `X19 = XREG 19`
and X20 = define `X20 = XREG 20`
and X21 = define `X21 = XREG 21`
and X22 = define `X22 = XREG 22`
and X23 = define `X23 = XREG 23`
and X24 = define `X24 = XREG 24`
and X25 = define `X25 = XREG 25`
and X26 = define `X26 = XREG 26`
and X27 = define `X27 = XREG 27`
and X28 = define `X28 = XREG 28`
and X29 = define `X29 = XREG 29`
and X30 = define `X30 = XREG 30`
and X31 = define `X31 = XREG 31`;;

(* Register the Xn views as aliases of concrete register-file elements. This
   lets generic read/write and frame automation treat, for example, X1 and
   XREG 1 as the same component. *)

add_component_alias_thms
 [X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
  X16; X17; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29;
  X30; X31];;

(* These names follow the integer register convention in the RISC-V ABIs
   Specification cited above. *)

let ZERO = define `ZERO = X0`
and RA   = define `RA = X1`
and SP   = define `SP = X2`
and GP   = define `GP = X3`
and TP   = define `TP = X4`
and T0   = define `T0 = X5`
and T1   = define `T1 = X6`
and T2   = define `T2 = X7`
and S0   = define `S0 = X8`
and S1   = define `S1 = X9`
and A0   = define `A0 = X10`
and A1   = define `A1 = X11`
and A2   = define `A2 = X12`
and A3   = define `A3 = X13`
and A4   = define `A4 = X14`
and A5   = define `A5 = X15`
and A6   = define `A6 = X16`
and A7   = define `A7 = X17`
and S2   = define `S2 = X18`
and S3   = define `S3 = X19`
and S4   = define `S4 = X20`
and S5   = define `S5 = X21`
and S6   = define `S6 = X22`
and S7   = define `S7 = X23`
and S8   = define `S8 = X24`
and S9   = define `S9 = X25`
and S10  = define `S10 = X26`
and S11  = define `S11 = X27`
and T3   = define `T3 = X28`
and T4   = define `T4 = X29`
and T5   = define `T5 = X30`
and T6   = define `T6 = X31`;;

(* Register the ABI names as aliases too, so automation treats, for example,
   RA and X1 as the same component. *)

add_component_alias_thms
 [ZERO; RA; SP; GP; TP; T0; T1; T2; S0; S1; A0; A1; A2; A3; A4; A5; A6; A7;
  S2; S3; S4; S5; S6; S7; S8; S9; S10; S11; T3; T4; T5; T6];;

let RISCV_ZERO_REGISTER = prove
 (`ZERO = rvalue (word 0) /\ X0 = rvalue (word 0)`,
  REWRITE_TAC[ZERO; X0]);;

(* Map the five-bit register field in an instruction to its named component.
   Register zero selects the read-only `ZERO` component above. *)

let riscv_gpr = define
 `riscv_gpr (n:5 word) =
    if n = word 0 then ZERO else
    if n = word 1 then RA else
    if n = word 2 then SP else
    if n = word 3 then GP else
    if n = word 4 then TP else
    if n = word 5 then T0 else
    if n = word 6 then T1 else
    if n = word 7 then T2 else
    if n = word 8 then S0 else
    if n = word 9 then S1 else
    if n = word 10 then A0 else
    if n = word 11 then A1 else
    if n = word 12 then A2 else
    if n = word 13 then A3 else
    if n = word 14 then A4 else
    if n = word 15 then A5 else
    if n = word 16 then A6 else
    if n = word 17 then A7 else
    if n = word 18 then S2 else
    if n = word 19 then S3 else
    if n = word 20 then S4 else
    if n = word 21 then S5 else
    if n = word 22 then S6 else
    if n = word 23 then S7 else
    if n = word 24 then S8 else
    if n = word 25 then S9 else
    if n = word 26 then S10 else
    if n = word 27 then S11 else
    if n = word 28 then T3 else
    if n = word 29 then T4 else
    if n = word 30 then T5 else T6`;;

(* Keep register reads and writes explicit in the instruction definitions.
   The selected component may be `ZERO`, whose write is ignored. *)

let read_gpr = new_definition
 `read_gpr (r:(riscvstate,int32)component) s = read r s`;;

let write_gpr = new_definition
 `write_gpr (r:(riscvstate,int32)component) x s = write r x s`;;

(* ------------------------------------------------------------------------- *)
(* Native-width address and control-flow helpers.                            *)
(* ------------------------------------------------------------------------- *)

(* Form the base-plus-immediate value used by LW, SW, and JALR. The decoder
   supplies a sign-extended int32 immediate, and word_add gives RV32
   wraparound arithmetic. *)

let riscv_addr = new_definition
 `riscv_addr (rs1:(riscvstate,int32)component) (imm:int32) s : int32 =
    word_add (read_gpr rs1 s) imm`;;

(* Instruction semantics run after fetch has advanced PC by four bytes. *)

let riscv_instruction_pc = new_definition
 `riscv_instruction_pc s =
    word_sub (read PC s) (word 4)`;;

(* Form a branch target relative to the address of the branch instruction,
   rather than the already advanced PC. *)

let riscv_branch_target = new_definition
 `riscv_branch_target (imm:int32) s : int32 =
    word_add (riscv_instruction_pc s) imm`;;

(* Return the high 32 bits of the signed 32-by-32-bit product used by MULH. *)

let riscv_mulh = new_definition
 `riscv_mulh (x:int32) (y:int32) =
    word_subword
      (word_mul (word_sx x:int64) (word_sx y:int64))
      (32,32):int32`;;

(* Record the architectural address or target observed by constant-time
   proofs. Arithmetic instructions do not add an event. *)

let riscv_event_load = new_definition
 `riscv_event_load (addr:int32) sz s =
    write events (CONS (EventLoad (addr,sz)) (read events s)) s`;;

let riscv_event_store = new_definition
 `riscv_event_store (addr:int32) sz s =
    write events (CONS (EventStore (addr,sz)) (read events s)) s`;;

let riscv_event_jump = new_definition
 `riscv_event_jump (src:int32) (dst:int32) s =
    write events (CONS (EventJump (src,dst)) (read events s)) s`;;

(* ------------------------------------------------------------------------- *)
(* Instruction semantics.                                                    *)
(* ------------------------------------------------------------------------- *)

let riscv_ADD = define
 `riscv_ADD rd rs1 rs2 s s' <=>
    write_gpr rd (word_add (read_gpr rs1 s) (read_gpr rs2 s)) s = s'`;;

let riscv_ADDI = define
 `riscv_ADDI rd rs1 (imm:int32) s s' <=>
    write_gpr rd (word_add (read_gpr rs1 s) imm) s = s'`;;

let riscv_SUB = define
 `riscv_SUB rd rs1 rs2 s s' <=>
    write_gpr rd (word_sub (read_gpr rs1 s) (read_gpr rs2 s)) s = s'`;;

let riscv_SLLI = define
 `riscv_SLLI rd rs1 shamt s s' <=>
    write_gpr rd (word_shl (read_gpr rs1 s) shamt) s = s'`;;

let riscv_SRAI = define
 `riscv_SRAI rd rs1 shamt s s' <=>
    write_gpr rd (word_ishr (read_gpr rs1 s) shamt) s = s'`;;

let riscv_LUI = define
 `riscv_LUI rd (imm:int32) s s' <=>
    write_gpr rd imm s = s'`;;

let riscv_MUL = define
 `riscv_MUL rd rs1 rs2 s s' <=>
    write_gpr rd (word_mul (read_gpr rs1 s) (read_gpr rs2 s)) s = s'`;;

let riscv_MULH = define
 `riscv_MULH rd rs1 rs2 s s' <=>
    write_gpr rd (riscv_mulh (read_gpr rs1 s) (read_gpr rs2 s)) s = s'`;;

let riscv_LW = define
 `riscv_LW rd rs1 imm s s' <=>
    let addr = riscv_addr rs1 imm s in
    if aligned 4 addr then
      riscv_event_load addr 4
        (write_gpr rd (read (memory :> bytes32 addr) s) s) = s'
    else
      ASSIGNS entirety s s'`;;

let riscv_SW = define
 `riscv_SW rs2 rs1 imm s s' <=>
    let addr = riscv_addr rs1 imm s in
    if aligned 4 addr then
      riscv_event_store addr 4
        (write (memory :> bytes32 addr) (read_gpr rs2 s) s) = s'
    else
      ASSIGNS entirety s s'`;;

let riscv_BNE = define
 `riscv_BNE rs1 rs2 imm s s' <=>
    let src = riscv_instruction_pc s in
    let dst =
      if read_gpr rs1 s = read_gpr rs2 s
      then read PC s
      else riscv_branch_target imm s in
    if aligned 4 dst then
      riscv_event_jump src dst (write PC dst s) = s'
    else
      ASSIGNS entirety s s'`;;

let riscv_JALR = define
 `riscv_JALR rd rs1 imm s s' <=>
    let src = riscv_instruction_pc s in
    let link = read PC s in
    let dst =
      word_and (riscv_addr rs1 imm s) (word_not (word 1):int32) in
    if aligned 4 dst then
      riscv_event_jump src dst
        (write PC dst (write_gpr rd link s)) = s'
    else
      ASSIGNS entirety s s'`;;
