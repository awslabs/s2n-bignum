(* RISC-V instruction bindings for the Sail compiler plugin.

   This file selects the upstream instruction computations to compare with
   s2n-bignum's RV32IM model. Each binding gives an export name, symbolic
   operands in the order of the upstream function's parameters and a call
   into the upstream Sail model.
   Fixed arguments choose the operation or width; the calculations remain
   in the upstream instruction and helper bodies.

   ci/check.py generate builds the plugin and calls run.sh to start Sail
   with the external RISC-V model, configured for 32-bit registers and all 32
   integer registers. After Sail checks that model, the common translator
   infers source-function requests from these checked calls, with operands
   supplied by Sail's declarations and only necessary type arguments fixed.
   Shared functions retain operation selectors; the bindings select individual
   instructions. ci/check.py proofs runs the separate HOL Light agreement
   proofs.

   The upstream model's execute function handles several instruction groups.
   To call register arithmetic directly, the exporter asks Sail's split
   transformation to extract that part as execute_RTYPE(rs2, rs1, rd, op).
   The ADD request below sets op = ADD; other groups are extracted similarly.
   Entry.instantiate asks Sail to check the constructed calls and determine
   their effects.

   cuts lists register, memory and platform functions interpreted by the
   common translator in HOL. Instruction selection and these interpretations
   are trusted: well-typed calls alone do not show that they select the intended
   s2n-bignum instruction. *)
open Libsail
open Ast_util
open Entry

let register name = name, word 5
let registers names = List.map register names
(* The HOL operand is a five-bit field. Regidx constructs the upstream
   register-index wrapper; it does not read the register. *)
let reg name = call "Regidx" [id name]
let execution_result = mk_id_typ (mk_id "ExecutionResult")

(* Keep ExecutionResult as the Sail return type. All bindings export state
   relations. Control bindings additionally retain success/failure tags and
   require Retire_Success and the completion jump event in that relation. *)
let state family name parameters body =
  make ~family ~result:execution_result name parameters body

let retirement name parameters body =
  make ~family:"control" ~retirement:true ~result:execution_result
    name parameters body

let arithmetic =
  List.map (fun operation ->
    state "arithmetic" ("rv_UTYPE_" ^ operation)
      ["imm", word 20; register "rd"]
      (call "execute_UTYPE" [id "imm"; reg "rd"; id operation])
  ) ["LUI"; "AUIPC"]
  @ List.map (fun operation ->
    state "arithmetic" ("rv_ITYPE_" ^ operation)
      ["imm", word 12; register "rs1"; register "rd"]
      (call "execute_ITYPE" [id "imm"; reg "rs1"; reg "rd"; id operation])
  ) ["ADDI"; "SLTI"; "SLTIU"; "XORI"; "ORI"; "ANDI"]
  @ List.map (fun operation ->
    state "arithmetic" ("rv_SHIFTIOP_" ^ operation)
      ["shamt", word 6; register "rs1"; register "rd"]
      (call "execute_SHIFTIOP" [id "shamt"; reg "rs1"; reg "rd"; id operation])
  ) ["SLLI"; "SRLI"; "SRAI"]
  @ List.map (fun operation ->
    state "arithmetic" ("rv_RTYPE_" ^ operation)
      (registers ["rs2"; "rs1"; "rd"])
      (call "execute_RTYPE" [reg "rs2"; reg "rs1"; reg "rd"; id operation])
  ) ["ADD"; "SUB"; "SLL"; "SLT"; "SLTU"; "XOR"; "SRL"; "SRA"; "OR"; "AND"]

(* MUL's operation is Sail's mul_op record: the half of the 64-bit product
   and the signedness of each operand, as in upstream's encdec_mul_op. *)
let multiply =
  List.map (fun (operation, half, signed_rs1, signed_rs2) ->
    state "multiply" ("rv_MUL_" ^ operation)
      (registers ["rs2"; "rs1"; "rd"])
      (call "execute_MUL" [reg "rs2"; reg "rs1"; reg "rd";
         mk_exp (Ast.E_struct (Ast.SN_anon, [
           mk_fexp (mk_id "result_part") (id half);
           mk_fexp (mk_id "signed_rs1") (id signed_rs1);
           mk_fexp (mk_id "signed_rs2") (id signed_rs2)]))])
  ) ["MUL", "Low", "Signed", "Signed";
     "MULH", "High", "Signed", "Signed";
     "MULHSU", "High", "Signed", "Unsigned";
     "MULHU", "High", "Unsigned", "Unsigned"]
  (* DIV and REM select the unsigned forms with is_unsigned = true. *)
  @ List.map (fun (group, operation, is_unsigned) ->
    state "multiply" ("rv_" ^ group ^ "_" ^ operation)
      (registers ["rs2"; "rs1"; "rd"])
      (call ("execute_" ^ group)
         [reg "rs2"; reg "rs1"; reg "rd"; bool is_unsigned])
  ) ["DIV", "DIV", false; "DIV", "DIVU", true;
     "REM", "REM", false; "REM", "REMU", true]

(* Loads select is_unsigned and the width in bytes; at XLEN = 32 LW
   extends nothing. vmem_read/write are cuts: the translator computes their
   address, register rs1 plus the offset, and gives them the explicit
   successful flat-memory interpretation, rather than the full platform's
   translation/fault behavior. FENCE's fields fm, rs1 and rd are ignored
   upstream; its pred and succ sets select only barriers, which change no
   state here. PAUSE, a FENCE encoding, has its own Zihintpause clause. *)
let memory =
  List.map (fun (operation, is_unsigned, width) ->
    state "memory" ("rv_LOAD_" ^ operation)
      ["imm", word 12; register "rs1"; register "rd"]
      (call "execute_LOAD"
         [id "imm"; reg "rs1"; reg "rd"; bool is_unsigned; int width])
  ) ["LB", false, 1; "LH", false, 2; "LW", false, 4;
     "LBU", true, 1; "LHU", true, 2]
  @ List.map (fun (operation, width) ->
    state "memory" ("rv_STORE_" ^ operation)
      ["imm", word 12; register "rs2"; register "rs1"]
      (call "execute_STORE" [id "imm"; reg "rs2"; reg "rs1"; int width])
  ) ["SB", 1; "SH", 2; "SW", 4]
  @ [state "memory" "rv_FENCE"
       ["fm", word 4; "pred", word 4; "succ", word 4;
        register "rs"; register "rd"]
       (call "execute_FENCE"
          [id "fm"; id "pred"; id "succ"; reg "rs"; reg "rd"]);
     state "memory" "rv_FENCE_TSO" [] (call "execute_FENCE_TSO" [unit]);
     state "memory" "rv_PAUSE" [] (call "execute_PAUSE" [unit])]

(* ECALL and EBREAK always trap, so their retirement relations hold for no
   final state. *)
let control =
  List.map (fun operation ->
    retirement ("rv_BTYPE_" ^ operation)
      ["imm", word 13; register "rs2"; register "rs1"]
      (call "execute_BTYPE" [id "imm"; reg "rs2"; reg "rs1"; id operation])
  ) ["BEQ"; "BNE"; "BLT"; "BGE"; "BLTU"; "BGEU"]
  @ [retirement "rv_JAL" ["imm", word 21; register "rd"]
       (call "execute_JAL" [id "imm"; reg "rd"]);
     retirement "rv_JALR"
       ["imm", word 12; register "rs1"; register "rd"]
       (call "execute_JALR" [id "imm"; reg "rs1"; reg "rd"]);
     retirement "rv_ECALL" [] (call "execute_ECALL" [unit]);
     retirement "rv_EBREAK" [] (call "execute_EBREAK" [unit])]

let entries = arithmetic @ multiply @ memory @ control

(* Each cut keeps its upstream signature and receives the existing HOL
   register, successful-access or disabled-feature interpretation; the
   barrier and event hooks change no state, and is_fiom_active reads a
   quantified component. Other reachable helpers retain their actual
   instruction calculations. A true row permits an impure value-producing
   call; false requires a statement path or pure call. Individual
   signature, state and completion checks remain; this permission does not
   select an instruction output type. *)
let contracts = [
  "rX_bits", true; "wX_bits", false;
  "get_arch_pc", true; "get_next_pc", true; "set_next_pc", false;
  "vmem_read", false; "vmem_write", false;
  "currentlyEnabled", true; "trap", true; "exception_context", true;
  "sail_barrier", true; "generate_event", true; "is_fiom_active", true
]
let cuts = List.map fst contracts

(* The extensions that currentlyEnabled answers false for. *)
let disabled_extensions = ["Ext_Zca"; "Ext_Zicfilp"]

(* Source names that sail_plugin_hol_light.ml interprets without a cut,
   after checking their declared types, with the translator case:
     PC                 read as the instruction's entry PC, never written:
                        register, simple_write, computation (E_assign);
     regidx, Regidx     the five-bit register field: hol_type, call;
     ExecutionResult, ExceptionType, ExceptionContext
                        a state computation drops ExecutionResult; a
                        retirement relation keeps the constructor tags and
                        the trap and excinfo fields: hol_type, and when it
                        builds them, call and record_construction_fields;
     Retire_Success     the unit result of a state computation: call; the
                        required result of a retirement relation: export_checked;
     Load, Store, Data  the only access kinds of vmem_read/vmem_write:
                        require_flat_access_literal;
     quot_round_zero, rem_round_zero
                        division rounding toward zero, by a divisor proved
                        nonzero: call. *)
