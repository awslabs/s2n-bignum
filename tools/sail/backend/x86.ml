(* Source-independent part of the x86 instruction bindings.

   Two external Sail models supply x86 execution bodies: shina-lab/sail-x86
   (x86_shina.ml) and rems-project/sail-x86-from-acl2 (x86_rems.ml). Each
   source table selects that model's own bodies and declares how its state
   maps to HOL's x86state. The translator receives exactly one source per
   compiler run; it never combines one model's result with another's flags.

   This module holds what the two tables share: register-form names,
   operand widths and register-field sizes, and the descriptor type the
   translator reads. It does not depend on either source table.

   A form's name records its operation, width and operands, for example
   X86_ADD64_RR. A source's root prefix keeps the two sources' HOL
   constants apart: the same form exported from REMS is X86_REMS_ADD64_RR. *)
open Entry

(* The field is an encoded register number, not an independent HOL lens.
   In a no-REX byte encoding 4..7 denote high bytes of registers 0..3.
   Keeping its field three bits prevents impossible no-REX accesses to
   registers 8..15. The source GPRRef helpers perform that selection.
   At every other width, a four-bit field and REX cover all sixteen GPRs. *)
type scalar_form = {
  width : int;
  register_bits : int;
  rex : bool;
}

let scalar_forms widths =
  List.concat_map (fun width ->
    let regular = {width; register_bits=4; rex=true} in
    if width = 8 then [regular; {width; register_bits=3; rex=false}]
    else [regular]
  ) widths

let scalar_name ?(prefix = "X86_") operation form operands =
  Printf.sprintf "%s%s%d%s_%s" prefix operation form.width
    (if form.rex then "" else "_LEGACY") operands

let scalar_parameters form names =
  List.map (fun name -> name, word form.register_bits) names

(* Typed source state with a fixed HOL interpretation. Each binding names
   a source declaration; the translator checks its declared type, arity,
   width and index bounds before using it. A binding listed by one source
   is unavailable to the other, even if a declaration has the same name:
   the two models' read_gpr functions have different signatures.

   Gpr_bank: shina's GPR register, a vector(16, bits(64)); its checked
   element accesses are registers :> element index (x86_bank_register).
   Flag_bits: shina's one-bit CF/PF/AF/ZF/SF/OF registers; each maps to
   the HOL Boolean flag component of RFLAGS (x86_flag).
   Simd_access: shina's read_simd/write_simd(width, index) cuts (x86_simd).
   Gpr_access: REMS's read_gpr(index)/write_gpr(index, value) cuts with
   range(0, 15) indices and 64-bit values, mapped to registers :> element
   (x86_rems_gpr).
   Uncaught_exceptions: a REMS throw (x86_fault, x86_model_error) ends the
   instruction without a normal final state (computation, E_throw). It is
   not a binding of state, but it is a source-specific trusted
   interpretation like the others.
   The names in parentheses are the cases in sail_plugin_hol_light.ml.

   Other source registers have no fixed interpretation. They become HOL
   component parameters of each exported relation, as for Arm and RV32.
   REMS's rflags and rip are such parameters; an agreement theorem names
   the HOL components it substitutes for them. *)
type state_binding =
  | Gpr_bank of string
  | Flag_bits of string list
  | Simd_access
  | Gpr_access
  | Uncaught_exceptions

type source = {
  model : string;                         (* "shina" or "rems" *)
  stem : string -> string;                (* family -> output file stem *)
  (* Qualify HOL datatypes, constructors and the case eliminator by the
     output stem, so models from both sources load into one kernel. *)
  qualified_names : bool;
  (* Use the translator support added for REMS: more static facts and
     branch selection, matches on Booleans and guarded variables, bounded
     integer recursion, refined unknown integers and short-circuit values
     with one continuation. Each translates the
     same source relation. Arm, RV32 and shina keep the established
     translation so their checked-in exports and proofs stay unchanged;
     enabling it for them would be a separate, re-verified migration. *)
  extended_evaluation : bool;
  entries : Entry.t list;
  family_roots : (string * string list) list;
  assumptions : Entry.t list -> Entry.assumption list;
  (* Cut functions. The flag says whether a state-computation root may
     call the impure declaration as a read contract. *)
  contracts : (string * bool) list;
  bindings : state_binding list;
  (* Checks of the loaded model that the bindings rely on, run before any
     cut removes a body. *)
  validate : Libsail.Interactive.State.istate -> unit;
}

let cuts source = List.map fst source.contracts
