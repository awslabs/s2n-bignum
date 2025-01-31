(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Auxiliary instructions are for making sure operand registers don't depend
   on RSP. This is because RSP in the theorem statement is an arbitrary value
   represented by `stackpointer`. However in actual machine run, it is a
   concrete value. If certain register's value depends on RSP value then the
   machine run and the instruction modeling result won't match. *)

let rand_scale_index(rest) =
  let index = if rest = 0 then 0 else Random.int (min rest 8) in
  let log2_int = fun x -> int_of_float (Float.log2 (float_of_int x)) in
  let scale =
    if index = 0 then Random.int 4
    else
      let scale_range = log2_int (rest/index) in
        if scale_range = 0 then 0 else Random.int (min scale_range 4) in
  let rest = rest - index * int_of_float (2.0 ** (float_of_int scale)) in
  [rest, scale, index]

(* Mode: base + scale*index + displacement
   Fixed: use of registers, operand size = 64, displacement size = 8
   Randomized: addressing mode parameters *)
let cosimulate_mem_full_harness(opcode) =
   (* disp8 is sign-extended *)
   let stack_start = Random.int 128 in
   let rest = 248 - stack_start in
   let base = if rest = 0 then 0 else Random.int (min rest 8) in
   let rest = rest - base in
   let base = stack_start + base in
   let [rest, scale, index] = rand_scale_index rest in
   (* disp8 is sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   (* fix use of rbx and rcx *)
   let sib = scale * int_of_float (2.0**6.0) + 0b001011 in
   [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
    [0x48; 0x8d; 0x5c; 0x24; base]; (* LEA rbx, [rsp+base] *)
    [0x48] @ opcode @ [0x44; sib; disp];  (* INST [rbx + scale*rcx + displacement], rax *)
    [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
   ];;

(* Mode: base + displacement
   Fixed: use of registers, operand size = 64, displacement size = 8
   Randomized: addressing mode parameters
   *)
let cosimulate_mem_base_disp_harness(opcode) =
   (* disp8 is sign-extended *)
   let stack_start = Random.int 128 in
   let rest = 248 - stack_start in
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   [[0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
    [0x48; 0x8d; 0x5c; 0x24; stack_start]; (* LEA rbx, [rsp+stack_start] *)
    [0x48] @ opcode @ [0x43; disp];  (* INST [rbx + displacement], rax *)
    [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
   ];;

(* Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters *)
let cosimulate_mem_rsp_harness(opcode) =
   let [rest, scale, index] = rand_scale_index 248 in
   (* disp8 is a sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   (* fix use of rcx and rsp *)
   let sib = scale * int_of_float (2.0**6.0) + 0b001100 in
   [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48] @ opcode @ [0x44; sib; disp];  (* INST [rsp + scale*rcx + displacement], rax *)
   ];;

(* Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters *)
let cosimulate_mul_full_harness() =
   (* disp8 is sign-extended *)
   let stack_start = Random.int 128 in
   let rest = 248 - stack_start in
   let base = if rest = 0 then 0 else Random.int (min rest 8) in
   let rest = rest - base in
   let base = stack_start + base in
   let [rest, scale, index] = rand_scale_index rest in
   (* disp8 is sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   let sib = scale * int_of_float (2.0**6.0) + 0b001011 in
   [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48; 0x89; 0xd8]; (* MOV r8, rbx *)
    [0x48; 0x8d; 0x5c; 0x24; base]; (* LEA rbx, [rsp+base] *)
    [0x48; 0xf7; 0x64; sib; disp];  (* MUL [rbx + scale*rcx + displacement] *)
    [0x4c; 0x89; 0xc3]; (* MOV rbx, r8 *)
   ];;

(* Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters
   Mode: base + displacement *)
let cosimulate_mul_base_disp_harness() =
   (* disp8 is sign-extended *)
   let stack_start = Random.int 128 in
   let rest = 248 - stack_start in
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   [[0x48; 0x89; 0xd8]; (* MOV r8, rbx *)
    [0x48; 0x8d; 0x5c; 0x24; stack_start]; (* LEA rbx, [rsp+stack_start] *)
    [0x48; 0xf7; 0x63; disp];  (* MUL [rbx + displacement] *)
    [0x4c; 0x89; 0xc3]; (* MOV rbx, r8 *)
   ];;

(* Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters *)
let cosimulate_mul_rsp_harness() =
   let [rest, scale, index] = rand_scale_index 248 in
   (* disp8 is a sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   (* fix use of rcx and rsp *)
   let sib = scale * int_of_float (2.0**6.0) + 0b001100 in
   [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48; 0xf7; 0x64; sib; disp];  (* MUL [rsp + scale*rcx + displacement], rax *)
   ];;

(* Fixed: operand size = 64 *)
let cosimulate_push_harness() =
  let reg = Random.int 6 in
  let push_inst = 0x50 + reg in
  [[0x48; 0x8d; 0x64; 0x24; 0x10]; (* lea rsp, [rsp + 16] *)
   [push_inst]; (* push REG *)
   [0x48; 0x8d; 0x64; 0x24; 0xf8] (* lea rsp, [rsp - 8] *)
  ];;

(* Fixed: operand size = 64 *)
let cosimulate_pop_harness() =
   let reg = Random.int 6 in
   let pop_inst = 0x58 + reg in
   [[0x48; 0x8d; 0x64; 0x24; 0x10]; (* lea rsp, [rsp + 16] *)
    [pop_inst]; (* pop REG *)
    [0x48; 0x8d; 0x64; 0x24; 0xE8] (* lea rsp, [rsp - 24] *)
   ];;

let mem_iclasses = [
   (* ADD r/m64, r64 *)
   cosimulate_mem_full_harness([0x01]);
   cosimulate_mem_base_disp_harness([0x01]);
   cosimulate_mem_rsp_harness([0x01]);
   (* ADD r64, r/m64 *)
   cosimulate_mem_full_harness([0x03]);
   cosimulate_mem_base_disp_harness([0x03]);
   cosimulate_mem_rsp_harness([0x03]);
   (* ADC r/m64, r64 *)
   cosimulate_mem_full_harness([0x11]);
   cosimulate_mem_base_disp_harness([0x11]);
   cosimulate_mem_rsp_harness([0x11]);
   (* ADC r64, r/m64 *)
   cosimulate_mem_full_harness([0x13]);
   cosimulate_mem_base_disp_harness([0x13]);
   cosimulate_mem_rsp_harness([0x013]);
   (* OR r/m64, r64 *)
   cosimulate_mem_full_harness([0x09]);
   cosimulate_mem_base_disp_harness([0x09]);
   cosimulate_mem_rsp_harness([0x09]);
   (* OR r64, r/m64 *)
   cosimulate_mem_full_harness([0x0B]);
   cosimulate_mem_base_disp_harness([0x0B]);
   cosimulate_mem_rsp_harness([0x0B]);
   (* SBB r/m64, r64 *)
   cosimulate_mem_full_harness([0x19]);
   cosimulate_mem_base_disp_harness([0x19]);
   cosimulate_mem_rsp_harness([0x19]);
   (* SBB r64, r/m64 *)
   cosimulate_mem_full_harness([0x1B]);
   cosimulate_mem_base_disp_harness([0x1B]);
   cosimulate_mem_rsp_harness([0x1B]);
   (* SUB r/m64, r64 *)
   cosimulate_mem_full_harness([0x29]);
   cosimulate_mem_base_disp_harness([0x29]);
   cosimulate_mem_rsp_harness([0x29]);
   (* SUB r64, r/m64 *)
   cosimulate_mem_full_harness([0x2B]);
   cosimulate_mem_base_disp_harness([0x2B]);
   cosimulate_mem_rsp_harness([0x2B]);
   (* XOR r/m64, r64 *)
   cosimulate_mem_full_harness([0x31]);
   cosimulate_mem_base_disp_harness([0x31]);
   cosimulate_mem_rsp_harness([0x31]);
   (* XOR r64, r/m64 *)
   cosimulate_mem_full_harness([0x33]);
   cosimulate_mem_base_disp_harness([0x33]);
   cosimulate_mem_rsp_harness([0x33]);
   (* MOV r/m64, r64 *)
   cosimulate_mem_full_harness([0x89]);
   cosimulate_mem_base_disp_harness([0x89]);
   cosimulate_mem_rsp_harness([0x89]);
   (* MOV r64, r/m64 *)
   cosimulate_mem_full_harness([0x8B]);
   cosimulate_mem_base_disp_harness([0x8B]);
   cosimulate_mem_rsp_harness([0x8B]);
   (* CMOVA r64, r/m64 *)
   cosimulate_mem_full_harness([0x0F; 0x47]);
   cosimulate_mem_base_disp_harness([0x0F; 0x47]);
   cosimulate_mem_rsp_harness([0x0F; 0x47]);
   (* CMOVB r64, r/m64 *)
   cosimulate_mem_full_harness([0x0F; 0x42]);
   cosimulate_mem_base_disp_harness([0x0F; 0x42]);
   cosimulate_mem_rsp_harness([0x0F; 0x42]);
   (* MUL r/m64 *)
   cosimulate_mul_full_harness();
   cosimulate_mul_base_disp_harness();
   cosimulate_mul_rsp_harness();
   (* PUSH rax *)
   cosimulate_push_harness();
   (* POP rax *)
   cosimulate_pop_harness();
  ];;
