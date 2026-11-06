#!/usr/bin/env python3
"""Test the HOL exporter on small Sail programs held in memory.

The real Sail compiler loads and checks each program before calling our
plugin. Cases check the emitted calculations and retained effects, or refusal
of unsupported programs; they do not provide architecture coverage.
"""

import os
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

import _project
from coverage import without_comments

HERE = Path(__file__).resolve().parent.parent
BUILD = HERE / "_build"
HEADER = "default Order dec\n$include <prelude.sail>\n"
MODEL = HEADER + """
register D : bits(64)
register A : bits(64)
register B : bits(64)

val add_value : (bits(64), bits(64)) -> bits(64)
function add_value(x, y) = x + y

val ADD : unit -> unit
function ADD() = D = add_value(A, B)

val TWO_WRITES : unit -> unit
function TWO_WRITES() = {
    D = A + B;
    B = D
}

val zero_value : unit -> bits(64)
function zero_value() = 0x0000000000000000
val ZERO_VALUE : unit -> unit
function ZERO_VALUE() = D = zero_value()
"""
ENUM_MODEL = HEADER + """
$include <result.sail>
enum singleton = { Only }
enum choice = { First, Second, Third }

val singleton_ident : singleton -> singleton
function singleton_ident(value) = value

val rotate_choice : choice -> choice
function rotate_choice(value) = match value {
    First => Second,
    Second => Third,
    Third => First
}

val result_value : result(bool, unit) -> bool
function result_value(value) = match value {
    Ok(payload) => payload,
    Err(_) => false
}

val literal_bytes : unit -> string
function literal_bytes() = """ + '"' + "".join(
    f"\\{byte:03d}" for byte in range(256)) + '"' + """

val equal_bytes : (string,string) -> bool
function equal_bytes(left,right) = left == right

struct BoolFields = { first : bool, second : bool }
val pack_bools : BoolFields -> BoolFields
function pack_bools(value) =
    struct { second = value.second, first = value.first }
val first_bool : BoolFields -> bool
function first_bool(value) = value.first
val second_bool : BoolFields -> bool
function second_bool(value) = value.second
"""
ENUM_ROOTS = (
    "singleton_ident", "rotate_choice", "result_value",
    "literal_bytes", "equal_bytes", "pack_bools", "first_bool", "second_bool")
FAULT_MODEL = HEADER + """
register D : bits(64)
val AArch64_SPAlignmentFault = impure "fault" : unit -> unit
val fault_helper : bool -> unit
function fault_helper(flag) = {
    if flag then AArch64_SPAlignmentFault();
    D = 0x0000000000000001
}
val FAULT_BRANCH : bits(1) -> unit
function FAULT_BRANCH(flag) = {
    fault_helper(flag == 0b1);
    D = 0x0000000000000002
}
val FAULT_LOOP : bits(1) -> unit
function FAULT_LOOP(flag) = {
    foreach (i from 0 to 1) {
        if flag == 0b1 then AArch64_SPAlignmentFault();
        D = 0x0000000000000001
    };
    D = 0x0000000000000002
}
val FAULT_ALWAYS : unit -> unit
function FAULT_ALWAYS() = {
    foreach (i from 0 to 1) { AArch64_SPAlignmentFault() };
    D = 0x0000000000000002
}
bitfield SCTLRType : bits(64) = { SA : 3, SA0 : 4 }
val SCTLR_read__1 = impure "control_read" : unit -> SCTLRType
val FAULT_CONTROL : unit -> unit
function FAULT_CONTROL() = {
    if SCTLR_read__1()[SA] != 0b0 then AArch64_SPAlignmentFault();
    D = 0x0000000000000002
}
val EndOfInstruction = impure "normal_stop" : unit -> unit
val NORMAL_STOP : bits(1) -> unit
function NORMAL_STOP(flag) = {
    foreach (i from 0 to 1) {
        D = 0x0000000000000001;
        if flag == 0b1 then EndOfInstruction();
        D = 0x0000000000000002
    };
    D = 0x0000000000000003
}
enum Choice = { Choice_First, Choice_Second, Choice_Third }
val eq_any = pure "eq_any" : forall ('a : Type). ('a, 'a) -> bool
val unknown_choice : unit -> Choice
function unknown_choice() = undefined
val UNKNOWN_CHOICE : unit -> unit
function UNKNOWN_CHOICE() = {
    let choice = unknown_choice();
    assert(or_bool(eq_any(choice, Choice_First), eq_any(choice, Choice_Third)));
    if eq_any(choice, Choice_First) then EndOfInstruction();
    D = 0x0000000000000002
}
val UNKNOWN_WORD : unit -> unit
function UNKNOWN_WORD() = {
    let value : bits(64) = undefined;
    D = value
}
val GUARDED : bits(1) -> unit
function GUARDED(flag) = {
    assert(flag == 0b1);
    D = 0x0000000000000002
}
union exception = { Error_Undefined : unit, Error_ExceptionTaken : unit }
val UNDEFINED_FAULT : bits(1) -> unit
function UNDEFINED_FAULT(flag) = {
    if flag == 0b1 then throw(Error_Undefined());
    D = 0x0000000000000002
}
val selected_choice : unit -> Choice
function selected_choice() = { D = 0x0000000000000007; Choice_First }
val JOIN_ENUM : bits(1) -> unit
function JOIN_ENUM(flag) = {
    choice : Choice = Choice_Second;
    if flag == 0b1 then choice = selected_choice()
    else choice = selected_choice();
    D = if eq_any(choice, Choice_First) then 0x0000000000000001
        else 0x0000000000000002
}
val JOIN_STATE : bits(1) -> unit
function JOIN_STATE(flag) = {
    if flag == 0b1 then D = 0x0000000000000001
    else D = 0x0000000000000002;
    D = 0x0000000000000063
}
"""
TESTS = BUILD / "tests"
TESTS.mkdir(parents=True, exist_ok=True)
RUN = Path(tempfile.mkdtemp(prefix="run-", dir=TESTS))


class BackendTests(unittest.TestCase):
    counter = 0

    @classmethod
    def setUpClass(cls):
        cls.environment = os.environ.copy()
        if not shutil.which("ocamlfind"):
            raise AssertionError("Run inside the matching OCaml switch")
        directory = os.environ.get("SAIL_HOL_BUILD_DIR")
        if not directory:
            directory = Path(os.environ["SAIL_HOL_PLUGIN"]).parent
        build = Path(directory)
        modules = [build / (name + ".cmx") for name in
                   ("entry", "arm", "rv32", "x86", "x86_shina", "x86_rems",
                    "sail_plugin_hol_light")]
        if not all(path.is_file() for path in modules):
            raise AssertionError("Set SAIL_HOL_BUILD_DIR to the matching CMX directory")
        temporary = RUN / "unit-frontend"
        temporary.mkdir()
        object_file = temporary / "unit_frontend.cmx"
        cls.frontend = temporary / "unit_frontend"
        includes = ["-I", str(build)]
        site_modules = []
        if os.environ.get("SAIL_BUILD_DIR"):
            sail_build = Path(os.environ["SAIL_BUILD_DIR"])
            for kind in ("byte", "native"):
                includes += ["-I", str(sail_build / "src/lib/.libsail.objs" / kind)]
            site_data = (sail_build / "src/bin/.sail.eobjs/native/"
                         "dune_site__Dune_site_data.cmx")
            if site_data.is_file():
                site_modules = [str(site_data)]
        if not site_modules:
            raise AssertionError("Set SAIL_BUILD_DIR to the matching Sail Dune build")
        libraries = subprocess.check_output(
            ["ocamlfind", "query", "-recursive", "-predicates", "native",
             "-format", "%d|%a", "libsail"], env=cls.environment, text=True)
        archives = []
        for library in libraries.splitlines():
            directory, names = library.split("|", 1)
            archives.extend(str(Path(directory) / name) for name in names.split())
        commands = [
            ["ocamlfind", "ocamlopt", "-g", "-package", "libsail", *includes,
             "-c", str(HERE / "tests/unit_frontend.ml"), "-o", str(object_file)],
            # Dune's generated site data must precede dune_site.cmxa.
            # Findlib normally puts all package archives before user modules.
            ["ocamlfind", "ocamlopt", "-g", "-linkall",
             "-package", "libsail", *includes, *site_modules, *archives, *map(str, modules),
             str(object_file), "-o", str(cls.frontend)],
        ]
        for command in commands:
            result = subprocess.run(command, env=cls.environment, capture_output=True,
                                    text=True, timeout=60)
            with (temporary / "build.log").open("a") as log:
                log.write(result.stdout + result.stderr)
            if result.returncode:
                raise AssertionError("Unit frontend build failed:\n" +
                                     (result.stdout + result.stderr)[-4000:])
        # Each test checks the prelude again, and each z3 question starts two
        # processes. Record Sail's answers for a prelude-only program once;
        # every test loads them and asks z3 only its own new questions.
        cls.environment.pop("SAIL_HOL_UNIT_SMT_CACHE", None)
        answers = temporary / "prelude-smt-cache"
        result = subprocess.run(
            [str(cls.frontend), "--unit-save-smt", str(answers)], input=HEADER,
            env=cls.environment, capture_output=True, text=True, timeout=60)
        if result.returncode or not answers.is_file():
            raise AssertionError("Prelude check failed:\n" +
                                 (result.stdout + result.stderr)[-4000:])
        cls.environment["SAIL_HOL_UNIT_SMT_CACHE"] = str(answers)

    def test_term_printer_bytes_and_deep_bindings(self):
        result = subprocess.run(
            [str(self.frontend), "--check-term-printer"],
            env=self.environment, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("HOL term printer checks passed", result.stdout)

    def test_binary_union_retains_both_payloads(self):
        source = """
union Operand = { Reg : bits(64), Mem : bits(32) }
register D : bits(64)
val ADD : Operand -> unit
function ADD(operand) = match operand {
    Reg(value) => D = value,
    Mem(value) => D = sail_zero_extend(value, 64)
}
"""
        text, _ = self.run_sail(source)
        self.assertIn("64 word+32 word", text)
        self.assertIn("sail_hl_result_case", text)
        self.assertIn("word_zx", text)
        self.assertEqual(text.count("write reg_D"), 2)

    def test_match_binder_cannot_rebind_a_mutable_local(self):
        source = """
register D : bits(8)
register E : bits(8)
val get : bits(8) -> option(bits(8))
function get(v) = if v == 0x00 then None() else Some(v)
val ROOT : bits(8) -> unit
function ROOT(v) = {
    var x : bits(8) = 0x05;
    match get(v) { Some(x) => D = x, None() => D = 0x02 };
    E = x
}
"""
        self.run_computation(source, error="cannot bind the name of a mutable local")
        text, _ = self.run_computation(
            source.replace("Some(x) => D = x", "Some(y) => D = y"))
        self.assertIn("write reg_E ((word 5):8 word)", text)

    def test_match_cannot_observe_undefined_bits_of_a_returned_word(self):
        source = """
register D : bits(8)
val f : unit -> bits(4)
function f() = {
    var x : bits(4) = undefined;
    x[1..0] = 0b01;
    return x
}
val ROOT : unit -> unit
function ROOT() = match f() { 0b0001 => D = 0x01, _ => D = 0x02 }
"""
        self.run_computation(source, error="observable value contains uninitialized bits")

    def test_match_patterns_cannot_bind_type_variables(self):
        # With 'n the pattern's type variable shares the name of H's 'n = 5.
        source = """
register D : bits(8)
val get : bits(8) -> option(int)
function get(v) = if v == 0x00 then None() else Some(unsigned(v))
val H : forall 'n. (int('n), bits(8)) -> unit
function H(n, v) = match get(v) {
    Some(y as int('n)) => { assert(y > 3, "big"); D = 0x01 },
    None() => D = 0x02
}
val ROOT : bits(8) -> unit
function ROOT(v) = H(5, v)
"""
        for name in ("'n", "'m"):
            with self.subTest(name=name):
                self.run_computation(
                    source.replace("int('n))", "int(" + name + "))"),
                    error="type-variable patterns in match clauses are unsupported")

    def test_primitive_word_widths_are_checked_at_generation(self):
        # HOL would test bit 0, truncate or reshape instead.
        cases = [
            ("val bit_to_bool = pure \"bit_to_bool\" : bits(2) -> bool",
             "if bit_to_bool(x[1 .. 0]) then x else x",
             "bit_to_bool requires a one-bit word"),
            ("val shift_bits_left = pure \"shift_bits_left\" : "
             "(bits(64), bits(4)) -> bits(32)",
             "sail_zero_extend(shift_bits_left(x, x[3 .. 0]), 64)",
             "bitvector shifts require a result of the input width"),
        ]
        for declaration, expression, error in cases:
            with self.subTest(error=error):
                self.run_computation(
                    self.computation_fixture(declaration + "\n", expression),
                    error=error)
        # The prelude's declaration requires m >= n; a model's own need not.
        narrowing = """default Order dec
val sail_zero_extend = pure "zero_extend" :
  (bitvector(64), int(32)) -> bitvector(32)
val sail_zero_extend64 = pure "zero_extend" :
  (bitvector(32), int(64)) -> bitvector(64)
register D : bitvector(64)
val ADD : bitvector(64) -> unit
function ADD(x) = D = sail_zero_extend64(sail_zero_extend(x, 32), 64)
"""
        self.run_sail(narrowing,
                      error="extension requires a result no narrower")

    def test_globals_are_reported_and_quoted(self):
        source = """
let Mask : bits(64) = 0x00000000ffffffff
register D : bits(64)
val ADD : bits(64) -> unit
function ADD(x) = D = and_vec(x, Mask)
"""
        text, deps = self.run_sail(source,
                                   with_sources=True)
        self.assertIn("inlined-global Mask", deps)
        self.assertIn('Sail source "Mask global"', text)

    def test_known_binary_union_selects_actual_register_arm(self):
        source = """
union Operand = { Reg : bits(64), Mem : bits(64) }
register A : bits(64)
register D : bits(64)
val unsupported_memory = impure "unsupported_memory" : bits(64) -> bits(64)
val operand_value : Operand -> bits(64)
function operand_value(operand) = match operand {
    Reg(value) => value,
    Mem(address) => unsupported_memory(address)
}
val ADD : unit -> unit
function ADD() = {
    let operand = Reg(A);
    A = 0x0000000000000000;
    D = operand_value(operand)
}
"""
        text, deps = self.run_sail(source)
        self.assertIn("INL", text)
        self.assertIn("OUTL", text)
        self.assertIn("write reg_A", text)
        self.assertIn("write reg_D", text)
        self.assertNotIn("primitive-contract unsupported_memory", deps)
        self.run_sail(source.replace("Reg(A)", "Mem(A)"), error="unsupported_memory")

    def test_x86_flags_use_existing_boolean_components(self):
        source = """
register CF : bit
register PF : bit
register AF : bit
register ZF : bit
register SF : bit
register OF : bit
val ADD : unit -> unit
function ADD() = {
    let saved = CF;
    CF = 0b0; PF = saved; AF = saved;
    ZF = saved; SF = saved; OF = saved
}
"""
        text, deps = self.run_sail(source, architecture="x86")
        self.assertIn("x86state", text)
        self.assertIn("read CF", text)
        for flag in ("CF", "PF", "AF", "ZF", "SF", "OF"):
            self.assertIn("write " + flag, text)
            self.assertNotIn("reg_" + flag, text)
        self.assertIn("x86-six-Boolean-flags", deps)
        self.run_sail("""
register CF : bits(2)
val ADD : unit -> unit
function ADD() = CF = 0b00
""",
                      architecture="x86",
                      error="declared one-bit register")

    def test_x86_gpr_boundary_checks_width_and_index(self):
        source = """
val read_gpr = pure "read_gpr" : (int, int) -> bits(64)
val write_gpr = impure "write_gpr" : (int, int, bits(64)) -> unit
val ADD : (bits(4), bits(4)) -> unit
function ADD(d, m) =
    write_gpr(64, unsigned(d), read_gpr(64, unsigned(m)))
"""
        text, deps = self.run_sail(source, architecture="x86")
        self.assertIn("read (registers :> (element", text)
        self.assertIn("write (registers :> (element", text)
        self.assertIn("4 word", text)
        self.assertIn("primitive-contract read_gpr", deps)
        self.assertIn("primitive-contract write_gpr", deps)
        self.run_sail(source.replace("read_gpr(64", "read_gpr(32"),
                      architecture="x86",
                      error="only full-width 64-bit accesses")
        self.run_sail(source.replace("write_gpr(64", "write_gpr(32"),
                      architecture="x86",
                      error="only full-width 64-bit accesses")
        self.run_sail(source.replace("read_gpr(64, unsigned(m))",
                                     "read_gpr(64, 16)"),
                      architecture="x86",
                      error="register index is not proved in 0..15")

    def test_x86_simd_boundary_checks_component_width_and_index(self):
        for width in (128, 256):
            source = f"""
val read_simd = pure "read_simd" : (int, int) -> bits({width})
val write_simd = impure "write_simd" : (int, int, bits({width})) -> unit
val ADD : (bits(5), bits(5)) -> unit
function ADD(d, m) =
    write_simd({width}, unsigned(d), read_simd({width}, unsigned(m)))
"""
            options = dict(architecture="x86")
            text, deps = self.run_sail(source, **options)
            self.assertIn(f"SIMD{width} (Simdreg", text)
            self.assertIn(f"Lower_{width}", text)
            self.assertIn("primitive-contract read_simd", deps)
            self.assertIn("primitive-contract write_simd", deps)
            for changed in (
                source.replace(f"read_simd({width}", "read_simd(512"),
                source.replace(f"write_simd({width}", "write_simd(512"),
                source.replace(f"read_simd({width}",
                               f"read_simd({384 - width}"),
                source.replace(f"write_simd({width}",
                               f"write_simd({384 - width}"),
            ):
                with self.subTest(width=width, source=changed):
                    self.run_sail(changed, **options,
                        error="requires a checked 128/256-bit access")
            self.run_sail(source.replace(f"read_simd({width}, unsigned(m))",
                                        f"read_simd({width}, 32)"),
                          **options, error="SIMD register index is not proved in 0..31")
            self.run_sail(source.replace(f"write_simd({width}, unsigned(d)",
                                        f"write_simd({width}, 32"),
                          **options, error="SIMD register index is not proved in 0..31")

    # REMS's register helpers: one-argument read and two-argument write
    # over sixteen individual registers, with optional write logging.
    REMS_REGISTERS = (
        "register log_register_writes : bool\n" +
        "".join(f"register {name} : bits(64)\n" for name in (
            "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
            "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15")) + """
val log_gpr_write : range(0, 15) -> unit
function log_gpr_write(idx) = ()
val read_gpr : range(0, 15) -> bits(64)
function read_gpr(idx) = match idx {
  0 => rax, 1 => rcx, 2 => rdx, 3 => rbx, 4 => rsp, 5 => rbp, 6 => rsi,
  7 => rdi, 8 => r8, 9 => r9, 10 => r10, 11 => r11, 12 => r12, 13 => r13,
  14 => r14, 15 => r15
}
val write_gpr : (range(0, 15), bits(64)) -> unit
function write_gpr(idx, value) = {
  match idx {
    0 => rax = value, 1 => rcx = value, 2 => rdx = value, 3 => rbx = value,
    4 => rsp = value, 5 => rbp = value, 6 => rsi = value, 7 => rdi = value,
    8 => r8 = value, 9 => r9 = value, 10 => r10 = value, 11 => r11 = value,
    12 => r12 = value, 13 => r13 = value, 14 => r14 = value, 15 => r15 = value
  };
  if log_register_writes then log_gpr_write(idx)
}
""")

    def run_rems(self, body, **options):
        return self.run_sail(self.REMS_REGISTERS + body, architecture="x86",
                             x86_source="rems", **options)

    def test_rems_registers_are_reached_only_through_the_gpr_cuts(self):
        # A direct access would bypass registers :> element i and become a
        # second, separate component for the same register.
        for body in ("""
val ADD : bits(4) -> unit
function ADD(d) = write_gpr(unsigned(d), rax)
""", """
val ADD : bits(4) -> unit
function ADD(d) = rcx = read_gpr(unsigned(d))
"""):
            with self.subTest(body=body):
                self.run_rems(body, error="is accessed only through read_gpr/write_gpr")

    def test_rems_gpr_cuts_keep_numbering_and_index_bounds(self):
        body = """
val ADD : (bits(4), bits(4)) -> unit
function ADD(d, m) = write_gpr(unsigned(d), read_gpr(unsigned(m)))
"""
        text, deps = self.run_rems(body)
        self.assertIn("read (registers :> (element", text)
        self.assertIn("write (registers :> (element", text)
        self.assertNotIn("reg_rax", text)
        self.assertIn("primitive-contract x86-REMS-GPR-access", deps)
        # The fixed interpretation applies only to the x86 numbering.
        swapped = self.REMS_REGISTERS.replace("0 => rax, 1 => rcx", "0 => rcx, 1 => rax")
        self.run_sail(swapped + body, architecture="x86", x86_source="rems",
                      error="read_gpr case 0 does not access rax")
        extra = self.REMS_REGISTERS.replace(
            "if log_register_writes then log_gpr_write(idx)", "rax = value")
        self.run_sail(extra + body, architecture="x86", x86_source="rems",
                      error="write_gpr has an effect other than its update and logging")
        # Under shina's bindings the REMS helpers are not cuts: their bodies
        # are translated and the symbolic register match is refused.
        self.run_sail(self.REMS_REGISTERS + body, architecture="x86",
                      error="integer matches require a statically known selector")

    def test_rems_throw_has_no_normal_outcome_only_for_rems(self):
        body = """
union exception = { Emsg : string }
val fault : forall ('a : Type). string -> 'a
function fault(msg) = throw(Emsg(concat_str("Fault: ", msg)))
val ADD : bits(4) -> unit
function ADD(d) = {
  if d == 0x0 then fault("zero");
  write_gpr(unsigned(d), 0x0000000000000001)
}
"""
        text, deps = self.run_rems(body)
        self.assertIn("primitive-contract x86-uncaught-exception-no-normal-state", deps)
        self.assertIn("F", text)
        self.run_sail("""
union exception = { Emsg : string }
register D : bits(8)
val ADD : bits(8) -> unit
function ADD(x) = { if x == 0x00 then throw(Emsg("zero")); D = x }
""", architecture="x86", error="unsupported")

    def test_refined_unknown_integer_retains_its_refinement(self):
        body = """
val undef_nat : unit -> nat
function undef_nat() = undefined
register D : bits(1)
val ADD : unit -> unit
function ADD() = D = get_slice_int(1, undef_nat(), 0)
"""
        text, deps = self.run_rems(body)
        self.assertIn("primitive-contract Sail-undefined-refined-integer", deps)
        self.assertRegex(text, r"\?\(v\d+:int\)")
        self.assertRegex(text, r"(?s)\(if \(\(\(& 0\) <= \(v\d+:int\)\):bool\) then .* else F\)")

    def test_boolean_and_guarded_variable_matches(self):
        body = """
val bit_number : (bits(4), int) -> bool
function bit_number(x, y) = unsigned(x) == y
overload operator == = {bit_number}
register D : bits(64)
register B : bool
val ADD : bits(4) -> unit
function ADD(x) = {
  D = match B { true => 0x0000000000000001, false => 0x0000000000000002 };
  D = match x { 1 => 0x0000000000000003, 2 => 0x0000000000000004,
                _ => 0x0000000000000005 }
}
"""
        text, deps = self.run_rems(body)
        self.assertGreaterEqual(text.count("(if "), 3)
        for value in ("1", "2", "3", "4", "5"):
            self.assertIn(f"(word {value})", text)

    def test_truncate_and_subrange_update_have_static_positions(self):
        body = """
register D : bits(64)
val ADD : (bits(64), bits(4)) -> unit
function ADD(x, y) = D = sail_zero_extend([truncate(x, 8) with 7 .. 4 = y], 64)
"""
        text, deps = self.run_rems(body)
        self.assertIn("word_zx", text)
        self.assertIn("word_insert", text)
        self.assertIn("primitive-contract truncate", deps)
        self.assertIn("primitive-contract update_subrange_bits", deps)

    def test_bounded_integer_recursion_unfolds_and_shares_calls(self):
        body = """
val count : int -> int
function count(x) =
  if x == 0 then 0 else
  if get_slice_int(1, x, 0) == 0b0 then count(shr_int(x, 1))
  else count(shr_int(x, 1)) + 1
register D : bits(8)
val ADD : bits(4) -> unit
function ADD(x) = D = get_slice_int(8, count(unsigned(x)), 0)
"""
        text, _ = self.run_rems(body)
        # Each unfolded level evaluates its recursive call once.
        self.assertLess(text.count("div"), 40)
        self.run_rems(body.replace("unsigned(x)", "signed(x)"),
                      error="recursive call lacks a decreasing static instance")

    def test_x86_integer_count_shift_names_keep_types_and_nonnegative_count(self):
        for name, operation in (
                ("shiftl", "word_shl"), ("shiftr", "word_ushr"),
                ("arith_shiftr", "word_ishr")):
            with self.subTest(name=name):
                source = f"""
val {name} = pure "{name}" :
    forall 'n, 'n >= 0. (bits(64), int('n)) -> bits(64)
val ROOT : bits(64) -> bits(64)
function ROOT(x) = {name}(x, 1)
"""
                text, _ = self.run_sail(source, roots=("ROOT",), architecture="x86")
                self.assertIn(operation, text)
                self.run_sail(
                    source.replace("'n >= 0", "true").replace("(x, 1)", "(x, -1)"),
                    roots=("ROOT",), architecture="x86",
                    error="proved nonnegative amount")
                self.run_sail(
                    source.replace("-> bits(64)\nval ROOT", "-> bits(32)\nval ROOT")
                          .replace("val ROOT : bits(64) -> bits(64)",
                                   "val ROOT : bits(64) -> bits(32)"),
                    roots=("ROOT",), architecture="x86",
                    error="matching word result")

    def test_literal_string_arguments_keep_the_evaluated_binding(self):
        source = """
$include <string.sail>
register D : bits(64)
register A : bits(64)
val selected : (string, bits(64)) -> bits(64)
function selected(label, x) = if label == "yes" then x + x else x
val ADD : unit -> unit
function ADD() = D = selected("%s", A)
""" % ("q" * 1024)
        text, _ = self.run_sail(source)
        self.assertLessEqual(text.count("(ASCII F T T T F F F T)"), 2048)
        self.assertIn("write reg_D", text)

    def test_static_string_lookup_does_not_print_unused_case_literals(self):
        cases = "\n".join(
            'else if label == "%s" then x + x' % ("q" * 128 + str(index))
            for index in range(100))
        source = """
$include <string.sail>
register D : bits(64)
register A : bits(64)
val selected : (string, bits(64)) -> bits(64)
function selected(label, x) =
    if label == "first" then x + x
    %s
    else if label == "absent" then x
    else { assert(false); x }
val ADD : unit -> unit
function ADD() = D = selected("absent", A)
""" % cases
        text, _ = self.run_sail(source)
        self.assertLess(len(text), 10000)
        self.assertNotIn("(ASCII F T T T F F F T)", text)
        self.assertIn("write reg_D", text)

    def test_string_register_argument_is_captured_before_later_state_write(self):
        source = """
$include <string.sail>
register S : string
register D : bool
val replace : unit -> string
function replace() = { D = false; "before" }
val ADD : unit -> unit
function ADD() = D = (S == replace())
"""
        text, _ = self.run_sail(source)
        body = text.split("let sail_hl_ADD =", 1)[1]
        # The exporter refuses string register writes, so replace() cannot
        # change S. Require the read to use the entry state s instead, and
        # the final write the state that replace() returns.
        read = re.search(r"let (v\d+) = \(\(read reg_S s\):string\)", body)
        self.assertIsNotNone(read, body)
        self.assertRegex(body, r"\(\(" + read[1] + r":string\) = ")
        pair = re.search(r"let \((v\d+),(v\d+)\) =", body)
        self.assertIsNotNone(pair, body)
        self.assertRegex(body, r"write reg_D v\d+ " + pair[2] + r"\)")
        self.assertIn("char list", text)
        failed, failed_deps = self.run_sail(
            source.replace('D = false; "before"',
                           'D = false; assert(false); "before"'))
        self.assert_failed_relation(failed, failed_deps)
        failed_body = failed.split("let sail_hl_ADD =", 1)[1]
        self.assertLess(failed_body.index("read reg_S"),
                        failed_body.index("write reg_D"))

    def run_sail(self, source, roots=("ADD",), error=None, normal_retirement=False,
                 architecture=None, output_dir=False,
                 with_sources=False, quote_sources=False, features=(), initial_bits=(),
                 initial_enums=(), initial_bools=(), input_lift=None, input_lifts=(),
                 fixed_arguments=(), expected_inputs=None, input_spans=None,
                 through=None, acquired=None, x86_source=None,
                 evaluate_arguments=False, jobs=None):
        BackendTests.counter += 1
        case = RUN / str(BackendTests.counter)
        case.mkdir(parents=True, exist_ok=True)
        prefix = case / "output"
        output = prefix.with_suffix(".ml")
        # Fresh filenames per invocation make refusal checks independent of
        # outputs from an earlier successful run.
        command = [
            str(self.frontend), "--hol-light", "-o", str(prefix),
        ]
        for root in roots:
            command += ["--hol-light-root", root]
        if architecture:
            command += ["--hol-light-architecture", architecture]
        # x86 fixtures default to shina's state bindings; REMS fixtures
        # select its bindings explicitly.
        if architecture == "x86":
            command += ["--hol-light-x86-source", x86_source or "shina"]
        for feature in features:
            command += ["--hol-light-assume-feature", feature]
        for bit in initial_bits:
            command += ["--hol-light-assume-bit", bit]
        for enum in initial_enums:
            command += ["--hol-light-assume-enum", enum]
        for boolean in initial_bools:
            command += ["--hol-light-assume-bool", boolean]
        if input_lift:
            command += ["--unit-lift", *input_lift]
        for lift in input_lifts:
            command += ["--unit-lift", *lift]
        for argument in fixed_arguments:
            command += ["--unit-fixed-argument", argument]
        if expected_inputs is not None:
            command += ["--unit-input-count", str(expected_inputs)]
        if input_spans is not None:
            command += ["--unit-input-spans", input_spans]
        if through is not None:
            command += ["--unit-through", through]
        if evaluate_arguments:
            command += ["--unit-evaluate-arguments"]
        if acquired is not None:
            callee, binding, value = acquired
            command += ["--unit-acquired", callee, f"{binding}={value}"]
        batch = case / "batch"
        if output_dir:
            command += ["--hol-light-output-dir", str(batch)]
        if jobs is not None:
            command += ["--hol-light-jobs", str(jobs)]
        if normal_retirement:
            command += ["--hol-light-normal-retirement"]
        if quote_sources:
            command += ["--hol-light-quote-sources"]
        if (not source.lstrip().startswith("default Order") and
                "$include <prelude.sail>" not in source):
            source = HEADER + source
        result = subprocess.run(command, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, timeout=60,
                                env=self.environment, input=source)
        self.assertFalse(list(case.rglob("*.sail")), "fixture created a Sail input file")
        self.assertFalse(list(case.rglob("*.holslice")), "fixture created a descriptor")
        (case / "frontend.log").write_text(result.stdout)
        if error is not None:
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(error, result.stdout)
            self.assertFalse(output.exists(), "failed export left a model")
            if output_dir:
                self.assertFalse(list(batch.glob("*.ml")),
                                 "failed batch published a partial model")
            return result.stdout
        self.assertEqual(result.returncode, 0, result.stdout)
        if output_dir:
            stem = architecture if architecture != "x86" else \
                "x86-" + (x86_source or "shina")
            inventory = batch / (stem + "-inventory.json")
            self.assertTrue(inventory.exists(), "batch did not produce inventory")
            return ({path.name: path.read_text() for path in batch.glob("*.ml")},
                    json.loads(inventory.read_text()))
        self.assertTrue(output.exists(), "target did not produce a model")
        text = output.read_text()
        code = "\n".join(line for line in without_comments(text).splitlines()
                         if line.strip())
        return (text if with_sources else code,
                prefix.with_suffix(".dependencies").read_text())

    def run_local_selection(self, body, declarations="", error=None):
        source = """
register A : bits(8)
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
""" + declarations + """
val ROOT : (bits(8),bits(8)) -> unit
function ROOT(opcode,x) = {
""" + body + """
}
"""
        return self.run_sail(source, roots=("HOL_INPUT_ROOT__acquire__opcode_133",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("opcode=133",), error=error)

    def test_closed_local_byte_and_alias_keep_original_writes(self):
        text, deps = self.run_local_selection("""
    A=x;
    let op : range(0,255)=unsigned(opcode);
    let alias : int=op;
    match alias {
      133=>{let y=acquire(1); D=x+y},
      _=>{D=acquire(2); D=acquire(3)}
    };
    A=D
""")
        self.assertIn("word_add", text)
        self.assertEqual(text.count("write reg_A"), 2)
        self.assertIn("<- acquire(1)", deps)
        self.assertNotIn("acquire(2)", deps)

    def test_closed_local_selection_respects_lexical_shadowing(self):
        text, _ = self.run_local_selection("""
    let op : int=unsigned(opcode);
    {let op : int=unsigned(x); if op==133 then A=x else A=0x00};
    match op {133=>D=acquire(1), _=>{D=acquire(2); D=acquire(3)}}
""")
        self.assertIn("(if ", text)
        self.assertIn("write reg_A", text)

    def test_closed_local_if_precedes_numeric_match(self):
        text, deps = self.run_local_selection("""
    let op : int=unsigned(opcode);
    if op<=63 & tmod_int(op,8)<=5 then {D=acquire(2); D=acquire(3)}
    else match op {133=>D=acquire(1), _=>D=0x00}
""")
        self.assertIn("write reg_D", text)
        self.assertIn("<- acquire(1)", deps)

    def test_closed_local_selection_refuses_unknown_or_effectful_facts(self):
        variants = (
            ("classify(opcode)", """
val classify = pure {interpreter:"uint"} : bits(8) -> int
function classify(value)=134
"""),
            ("classify(opcode)", """
val classify = impure {interpreter:"uint"} : bits(8) -> int
"""),
            ("classify(opcode)", """
val classify = pure {interpreter:"undefined_int"} : bits(8) -> int
"""),
            ("G", "let G : int=133\n"),
            ("unsigned({A=x; opcode})", ""),
            ("tmod_int(133,0)", ""),
        )
        for rhs, declarations in variants:
            with self.subTest(rhs=rhs, declarations=declarations):
                self.run_local_selection("""
    let op : int=""" + rhs + """;
    match op {133=>D=acquire(1), _=>{D=acquire(2); D=acquire(3)}}
""", declarations, error="requires exactly one direct input call")

    def run_acquired(self, body, declarations="", value=133, fixed=(),
                     through="helper", error=None, spans=None, scalar=False,
                     scan_argument_type="unit"):
        result = "bits(8)" if scalar else "(bits(8),bits(8))"
        source = """
register A : bits(8)
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val scan = impure "unsupported_scan" : """ + scan_argument_type + " -> " + result + """
val helper : bits(8) -> unit
function helper(pfx)={let y=acquire(1); D=pfx+y}
""" + declarations + """
val ROOT : bits(8) -> unit
function ROOT(x)={
""" + body + """
}
"""
        suffix = "".join(f"__{name}_{number}"
                         for name, number in sorted(fixed))
        child = "" if through is None else "__through_" + through
        root = "HOL_INPUT_ROOT__acquire" + suffix + child + \
               "__acquired_scan__opcode_" + str(value).replace("-", "m")
        return self.run_sail(source, roots=(root,), input_lift=("ROOT", "acquire"),
            acquired=("scan", "opcode", value),
            fixed_arguments=tuple(f"{name}={number}" for name, number in fixed),
            through=through, input_spans=spans,
            with_sources=True, error=error)

    def test_acquired_tuple_retains_typed_prefix_and_child(self):
        text, deps = self.run_acquired("""
    A=x;
    let(pfx,opcode)=scan();
    let op : range(0,255)=unsigned(opcode);
    if op<=63 & op%8<=5 then {D=acquire(2); D=acquire(3)}
    else match op {133=>helper(pfx), _=>D=0x00};
    A=D
""", declarations="""
val rem_positive_round_zero = pure {interpreter:"rem_round_zero"}
  : forall 'n 'm, 'n >= 0 & 'm > 0.
    (int('n),int('m)) -> int(mod('n,'m))
overload operator % = {rem_positive_round_zero}
""")
        self.assertIn("word_add", text)
        self.assertEqual(text.count("write reg_A"), 2)
        self.assertIn("fix opcode (result.1) : bitvector(8) = 0b10000101", deps)
        self.assertIn("input 0, parameter __hol_input0 (result.0) : bitvector(8)", deps)
        self.assertIn("[input 1, parameter __hol_input1] <- acquire(1)", deps)
        self.assertIn("-> HOL_INPUT_helper__acquire, input 0", deps)
        self.assertNotIn("unsupported_scan", text)
        self.assertNotIn("acquire(2)", deps)

    def test_acquired_scalar_zero_slot_and_fixed_formal(self):
        text, deps = self.run_acquired("""
    A=x;
    if unsigned(x)==56 then {
      let opcode=scan(); let op=unsigned(opcode);
      if op==246 then helper(A) else D=0x00
    } else {let other=scan(); D=other}
""", scalar=True, value=246, fixed=(("x", 56),))
        self.assertIn("word_add", text)
        self.assertIn("fix opcode (result) : bitvector(8) = 0b11110110", deps)
        self.assertIn("[input 0, parameter __hol_input0] <- acquire(1)", deps)
        self.assertIn("supplied fields: none", text)

    def test_acquired_keeps_other_calls_until_checked_selection(self):
        text, deps = self.run_acquired("""
    let opcode=scan(); let op=unsigned(opcode);
    if op==133 then helper(x) else {let other=scan(); D=other}
""", scalar=True)
        self.assertIn("word_add", text)
        self.assertEqual(deps.count("<- scan()"), 1)
        self.run_acquired("let opcode=scan(); let other=scan(); helper(x)",
            scalar=True, error="unsupported primitive scan")

    def test_acquired_preserves_shadowing_and_input_freshness(self):
        text, deps = self.run_acquired("""
    let __hol_input0=x;
    let(pfx,opcode)=scan();
    {let opcode=x; if unsigned(opcode)==133 then A=x else A=0x00};
    if unsigned(opcode)==133 then helper(pfx + __hol_input0) else D=0x00
""")
        self.assertIn("(if ", text)
        self.assertIn("parameter __hol_input1 (result.0)", deps)
        self.assertIn("[input 1, parameter __hol_input2]", deps)
        self.assertIn("retained caller: helper", deps)
        self.assertIn("word_add", text)

    def test_acquired_direct_inputs_follow_tuple_slots(self):
        text, deps = self.run_acquired("""
    let(pfx,opcode)=scan();
    if unsigned(opcode)==133 then {let y=acquire(1); D=pfx+y+x}
    else D=0x00
""", through=None)
        self.assertIn("word_add", text)
        self.assertIn("[input 1, parameter __hol_input1]", deps)

    def test_acquired_refuses_missing_duplicate_or_loop_call(self):
        for body, error in (
            ("helper(x)", "requires exactly one immutable acquired-input let"),
            ("let(pfx,opcode)=scan(); let(q,opcode)=scan(); helper(pfx)",
             "requires exactly one immutable acquired-input let"),
            ("foreach(i from 0 to 1){let(pfx,opcode)=scan(); helper(pfx)}",
             "acquired calls under loops are unsupported"),
            ("let(pfx,other)=scan(); helper(pfx)",
             "unknown acquired fixed binding: opcode"),
        ):
            with self.subTest(body=body):
                self.run_acquired(body, error=error)

    def test_acquired_refuses_invalid_value_and_source_origin(self):
        for value in (-1, 256):
            with self.subTest(value=value):
                self.run_acquired("let(pfx,opcode)=scan(); helper(pfx)", value=value,
                    error="fixed bit argument is outside its source width")
        self.run_acquired("let(pfx,opcode)=scan(); helper(pfx)", spans="missing",
            error="selected input has no original source span")
        self.run_acquired("""
    if unsigned(x)==56 then {let opcode=scan(); helper(x)}
    else {let other=scan(); D=other}
""", scalar=True, fixed=(("x", 56),), spans="duplicate",
            error="selected input has no unique original source call")

    def test_acquired_keeps_effectful_selector_unknown(self):
        self.run_acquired("""
    let(pfx,opcode)=scan();
    let op=unsigned({A=x; opcode});
    if op==133 then helper(pfx) else helper(x)
""", error="requires exactly one direct helper call")

    def test_acquired_refuses_impossible_primitive_return_facts(self):
        for condition, declarations in (
            ("classify(opcode)==133", """
val classify = pure {interpreter:"uint"} : bits(8) -> int(0)
"""),
            ("classify(unsigned(opcode),133)", """
val classify = pure {interpreter:"eq_int"} : (int,int) -> bool(false)
"""),
        ):
            with self.subTest(condition=condition):
                self.run_acquired("""
    let(pfx,opcode)=scan();
    if """ + condition + """ then helper(pfx) else helper(x)
""", declarations=declarations, error="requires exactly one direct helper call")
        # Analysis may select a consistent result, but it never supplies
        # a HOL interpretation for the retained primitive calculation.
        self.run_acquired("""
    let(pfx,opcode)=scan();
    if classify(unsigned(opcode),133) then helper(pfx) else helper(x)
""", declarations="""
val classify = pure {interpreter:"eq_int"} : (int,int) -> bool(true)
""", error="unsupported primitive classify")

    def test_acquired_refuses_effectful_arguments(self):
        self.run_acquired("let opcode=scan({A=x;x}); helper(x)", scalar=True,
            scan_argument_type="bits(8)", error="acquired call arguments must be literals")

    def run_gpr_bank(self, body, declarations="", parameters="bits(64)",
                     arguments="x", shape="vector(16,bits(64))", error=None):
        return self.run_sail("""
register GPR : """ + shape + "\n" + declarations + """
val ADD : """ + parameters + """ -> unit
function ADD(""" + arguments + """)={
""" + body + """
}
""", architecture="x86", error=error)

    def test_x86_raw_gpr_access_uses_existing_bank(self):
        text, deps = self.run_gpr_bank("GPR[1]=GPR[unsigned(d)]",
            parameters="bits(4)", arguments="d")
        self.assertIn("read (registers :>", text)
        self.assertIn("write (registers :>", text)
        self.assertNotIn("reg_GPR", text)
        self.assertIn("x86-raw-GPR-bank", deps)

    def test_x86_raw_gpr_partial_writes_preserve_other_bits(self):
        for high, low in ((7, 0), (15, 8), (15, 0)):
            with self.subTest(high=high, low=low):
                width = high - low + 1
                text, _ = self.run_gpr_bank(f"GPR[0][{high}..{low}]=x",
                    parameters=f"bits({width})")
                self.assertIn("word_insert", text)
                self.assertIn(f"({low},{width})", text)
                self.assertIn("read (registers :>", text)
                self.assertNotIn("reg_GPR", text)

    def test_x86_raw_gpr_read_samples_bank_before_effectful_index(self):
        text, _ = self.run_gpr_bank("GPR[1]=GPR[index_change(x)]", """
val index_change : bits(64) -> int(0)
function index_change(x)={GPR[0]=x; 0}
""")
        root = text.split("let sail_hl_ADD =", 1)[1]
        self.assertIn("index_5fchange", root)
        self.assertRegex(root, r"read \(registers :>.*?\) s\)")
        pair = re.search(r"let \((v\d+),(v\d+)\) =", root)
        self.assertIsNotNone(pair, root)
        self.assertRegex(root, r"write \(registers :>.*? " + pair[2] + r"\)")

    def test_x86_raw_gpr_partial_write_merges_after_rhs_effect(self):
        text, _ = self.run_gpr_bank("GPR[0][15..8]=replacement(x)", """
val replacement : bits(64) -> bits(8)
function replacement(x)={GPR[0]=x; 0xbb}
""")
        root = text.split("let sail_hl_ADD =", 1)[1]
        pair = re.search(r"let \((v\d+),(v\d+)\) =", root)
        self.assertIsNotNone(pair, root)
        insert = root.split("word_insert", 1)[1]
        self.assertRegex(insert, r"read \(registers :>.*? " + pair[2] + r"\)")
        self.assertNotRegex(insert, r"read \(registers :>.*? s\)")

    def test_x86_raw_gpr_wrong_bank_shape_refuses(self):
        for shape, width in (("vector(8,bits(64))", 64),
                             ("vector(16,bits(32))", 32)):
            with self.subTest(shape=shape):
                self.run_gpr_bank("GPR[0]=x", shape=shape,
                    parameters=f"bits({width})", error="declared vector(16,bits(64))")

    def test_x86_raw_gpr_unbounded_index_refuses(self):
        # Sail rejects this bound before export, not the HOL range check.
        self.run_gpr_bank("GPR[x]=GPR[0]", parameters="int",
            error="Failed to prove constraint")

    def test_x86_raw_gpr_aggregate_alias_and_write_refuse(self):
        for body in ("let bank=GPR; GPR[0]=bank[1]", "GPR=GPR"):
            with self.subTest(body=body):
                self.run_gpr_bank(body, error="unsupported type")

    @staticmethod
    def input_lift_fixture(body, result="bits(8)"):
        return """
register A : bits(8)
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> """ + result + """
val ROOT : bits(8) -> unit
function ROOT(__hol_input0) = {
""" + body + """
}
"""

    def test_input_lift_retains_original_writes_and_calculations(self):
        source = self.input_lift_fixture("""
    A = __hol_input0;
    let __hol_input1 : bits(8) = __hol_input0;
    let supplied = acquire(1);
    D = __hol_input1 + supplied
""")
        options = dict(roots=("HOL_INPUT_ROOT__acquire",),
                       input_lift=("ROOT", "acquire"))
        text, deps = self.run_sail(source, **options)
        self.assertIn("write reg_A", text)
        self.assertIn("write reg_D", text)
        self.assertIn("word_add", text)
        self.assertNotIn("unsupported_acquire", text)
        self.assertLess(text.index("write reg_A"), text.index("write reg_D"))
        # The new parameter must not capture either original source binder.
        self.assertIn("(v0:8 word)", text)
        self.assertIn("(v1:8 word)", text)
        self.assertIn("source-input-boundary HOL_INPUT_ROOT__acquire", deps)
        self.assertIn("acquire(1)", deps)
        self.assertIn("unit-input.sail:", deps)
        self.assertIn("bitvector(8)", deps)
        changed, _ = self.run_sail(source.replace(
            "__hol_input1 + supplied", "xor_vec(__hol_input1,supplied)"), **options)
        self.assertIn("word_xor", changed)
        self.assertNotIn("word_add", changed)
        original, _ = self.run_sail(source, with_sources=True, quote_sources=True,
                                    **options)
        self.assertIn("let supplied = acquire(1)", original)
        self.assertIn("unit-input.sail:", original)
        self.assertIn("Source input boundary:", original)
        _, architecture_deps = self.run_sail(source, architecture="x86", **options)
        self.assertIn("source-input-boundary HOL_INPUT_ROOT__acquire", architecture_deps)

    def test_input_boundary_reports_its_root_but_not_unreached_function(self):
        source = """
enum Choice = { First, Second }
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val ROOT : Choice -> unit
function ROOT(op) = {
    let x = acquire(1);
    D = match op { First => x, Second => not_vec(x) }
}
val unrelated : unit -> bits(8)
function unrelated() = 0x11
"""
        text, deps = self.run_sail(source, roots=("HOL_INPUT_ROOT__acquire",),
            input_lift=("ROOT", "acquire"))
        self.assertIn("source-input-boundary HOL_INPUT_ROOT__acquire", deps)
        self.assertNotIn("unsupported_acquire", text)
        _, deps = self.run_sail(source, roots=("unrelated",),
            input_lift=("ROOT", "acquire"))
        self.assertNotIn("source-input-boundary", deps)

    def test_input_lift_infers_the_original_call_result_type(self):
        source = self.input_lift_fixture(
            "let supplied = acquire(1); D = supplied[7 .. 0]", "bits(32)")
        text, _ = self.run_sail(
            source, roots=("HOL_INPUT_ROOT__acquire",),
            input_lift=("ROOT", "acquire"))
        self.assertIn("(v1:32 word)", text)
        self.assertIn("word_subword", text)

    def test_input_lift_refuses_zero_multiple_and_repeated_execution(self):
        for body, error in (
            ("D = __hol_input0", "exactly one direct input call"),
            ("A = acquire(1); D = acquire(1)", "exactly one direct input call"),
            ("foreach (i from 0 to 1) { D = acquire(1) }",
             "input calls under loops are unsupported"),
            ("while (__hol_input0 == 0x00) { D = acquire(1) }",
             "input calls under loops are unsupported"),
        ):
            with self.subTest(body=body):
                self.run_sail(self.input_lift_fixture(body),
                    roots=("HOL_INPUT_ROOT__acquire",), input_lift=("ROOT", "acquire"),
                    error=error)

    def test_input_lift_refuses_colliding_derived_names(self):
        source = """
val c = impure "c" : int -> bits(8)
val b__c = impure "b__c" : int -> bits(8)
val a__b : unit -> bits(8)
function a__b() = c(1)
val a : unit -> bits(8)
function a() = b__c(1)
"""
        self.run_sail(source, roots=("HOL_INPUT_a__b__c",),
            input_lifts=(("a__b", "c"), ("a", "b__c")),
            error="derived names collide")

    def test_multiple_inputs_have_distinct_types_slots_and_fresh_names(self):
        source = """
register A : bits(8)
register D : bits(32)
val acquire = impure "unsupported_acquire" : forall 'n, 'n in {1,4}.
    int('n) -> bits(8 * 'n)
val ROOT : bits(8) -> unit
function ROOT(__hol_input0) = {
    let __hol_input1 = __hol_input0;
    A = __hol_input0;
    let first = acquire(1);
    A = __hol_input1 + first;
    let second = acquire(4);
    D = xor_vec(second, sail_zero_extend(A, 32))
}
"""
        text, deps = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__inputs_2",),
            input_lift=("ROOT", "acquire"), expected_inputs=2)
        self.assertIn("(v0:8 word)", text)
        self.assertIn("(v1:8 word)", text)
        self.assertIn("(v2:32 word)", text)
        self.assertIn("[input 0, parameter __hol_input2] <- acquire(1)", deps)
        self.assertIn("[input 1, parameter __hol_input3] <- acquire(4)", deps)
        self.assertEqual(text.count("write reg_A"), 2)
        self.assertLess(text.rindex("write reg_A"), text.index("write reg_D"))
        self.assertIn("word_add", text)
        self.assertIn("word_xor", text)
        self.assertNotIn("unsupported_acquire", text)

    def test_helper_inputs_keep_effectful_arguments_and_both_source_spans(self):
        source = """
register A : bits(8)
register B : bits(8)
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val left_arg : unit -> bits(8)
function left_arg() = { B = B + 0x01; A }
val right_arg : bits(8) -> bits(8)
function right_arg(x) = { B = B + 0x02; x }
val child : (bits(8),bits(8)) -> (bits(8),bits(8))
function child(__hol_input0,__hol_input1) = {
    let __hol_input2 = __hol_input0;
    A = __hol_input2;
    let first = acquire(1);
    let second = acquire(2);
    (first + __hol_input1, second)
}
val ROOT : (range(0,255),bits(8)) -> unit
function ROOT(op,__hol_input0) = match op {
    23 => {
        let __hol_input1 = __hol_input0;
        A = 0x11;
        let (a,b) = child(left_arg(),right_arg(__hol_input1));
        D = sub_bits(a,b);
        A = D
    },
    _ => D = __hol_input0
}
"""
        options = dict(roots=("HOL_INPUT_ROOT__acquire__op_23__inputs_2__through_child",),
                       input_lift=("ROOT", "acquire"), through="child",
                       fixed_arguments=("op=23",), expected_inputs=2)
        text, deps = self.run_sail(source, **options)
        self.assertEqual(text.count("write reg_B"), 2)
        self.assertEqual(text.count("write reg_A"), 3)
        self.assertEqual(text.count("write reg_D"), 1)
        # Shared definitions precede the root in the file; their textual
        # order is not execution order. Check the root's retained calls.
        root = text[text.index("let sail_hl_HOL_5fINPUT_5fROOT"):]
        stages = [root.index("write reg_A"),
                  root.index("(sail_hl_shared_output_left_5farg"),
                  root.index("(sail_hl_shared_output_right_5farg"),
                  root.index("(sail_hl_shared_output_HOL_5fINPUT_5fchild"),
                  root.index("write reg_D"), root.rindex("write reg_A")]
        self.assertEqual(stages, sorted(stages))
        self.assertIn("word_sub", text)
        self.assertNotIn("unsupported_acquire", text)
        self.assertRegex(deps, r"\[input 0, parameter __hol_input[2-9]\] <- acquire\(1\)")
        self.assertRegex(deps, r"\[input 1, parameter __hol_input[2-9]\] <- acquire\(2\)")
        self.assertEqual(deps.count("retained caller:"), 2)
        self.assertIn("child(left_arg(), right_arg(__hol_input1))", deps)
        self.assertIn("-> HOL_INPUT_child__acquire__inputs_2", deps)
        self.assertEqual(len(re.findall(
            r"at unit-input\.sail:\d+:\d+-\d+:\d+", deps)), 6)
        self.assertIn("source-input-boundary HOL_INPUT_child__acquire__inputs_2", deps)
        swapped, _ = self.run_sail(source.replace(
            "(first + __hol_input1, second)",
            "(second + __hol_input1, first)"), **options)
        self.assertNotEqual(text, swapped)

    @staticmethod
    def helper_input_fixture(body, child_body="x + acquire(1)"):
        return """
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val child : bits(8) -> bits(8)
val ROOT : bits(8) -> unit
function child(x) = """ + child_body + """
function ROOT(x) = { """ + body + """ }
"""

    def test_helper_inputs_refuse_missing_repeated_looped_and_recursive_calls(self):
        for body, child, error in (
                ("D = x", "x + acquire(1)", "exactly one direct helper call"),
                ("D = child(x) + child(x)", "x + acquire(1)",
                 "exactly one direct helper call"),
                ("foreach (i from 0 to 1) { D = child(x) }",
                 "x + acquire(1)", "helper calls under loops"),
                ("ROOT(x); D = child(x)", "x + acquire(1)", "recursive caller"),
                ("D = child(x)", "child(x) + acquire(1)", "recursive helper path"),
                ("D = child(x)", "{ ROOT(x); x + acquire(1) }",
                 "recursive helper path")):
            with self.subTest(body=body, child=child):
                self.run_sail(self.helper_input_fixture(body, child),
                    roots=("unused",), input_lift=("ROOT", "acquire"),
                    through="child", error=error)

    def test_helper_inputs_retain_unit_call_guard_and_early_return(self):
        source = """
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val child : unit -> bits(8)
function child() = acquire(1)
val ROOT : bits(8) -> unit
function ROOT(x) = { if x == 0x00 then return(); D = child() }
"""
        text, deps = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__through_child",),
            input_lift=("ROOT", "acquire"), through="child")
        self.assertIn("if", text)
        self.assertEqual(text.count("write reg_D"), 1)
        self.assertIn("retained caller: child()", deps)

    def test_helper_inputs_report_original_and_selected_caller(self):
        source = """
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val child : (int,bits(8)) -> bits(8)
function child(op,x) = {
    let supplied = acquire(1);
    if op == 23 then x + supplied else supplied
}
val ROOT : (range(0,255),bits(8)) -> unit
function ROOT(op,x) = match op { 23 => D = child(op,x), _ => D = x }
"""
        _, deps = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23__through_child",),
            input_lift=("ROOT", "acquire"), through="child",
            fixed_arguments=("op=23",))
        self.assertIn("retained caller: child(op, x) "
                      "(selected call: child(23, x))", deps)
        self.assertIn("<- acquire(1) at unit-input.sail:", deps)

    def test_helper_inputs_refuse_child_type_witnesses(self):
        source = """
val acquire = impure "unsupported_acquire" :
    forall 'n, 'n > 0. unit -> bits('n)
val child : forall 'n, 'n > 0. bits('n) -> bits('n)
function child(x) = xor_vec(x,acquire())
val ROOT : forall 'n, 'n > 0. bits('n) -> bits('n)
function ROOT(x) = child(x)
"""
        self.run_sail(source, roots=("unused",),
            input_lift=("ROOT", "acquire"), through="child",
            error="helper input type must be closed")

    def test_helper_inputs_refuse_unlocated_leaf_acquisition(self):
        self.run_sail(self.helper_input_fixture("D = child(x)"),
            roots=("unused",), input_lift=("ROOT", "acquire"),
            through="child", input_spans="missing",
            error="helper input requires a real source span")

    def test_helper_clone_root_records_its_boundary_without_unused_caller(self):
        text, deps = self.run_sail(self.helper_input_fixture("D = child(x)"),
            roots=("HOL_INPUT_child__acquire",),
            input_lift=("ROOT", "acquire"), through="child",
            with_sources=True)
        self.assertIn("Source input boundary: HOL_INPUT_child__acquire", text)
        self.assertIn("source-input-boundary HOL_INPUT_child__acquire", deps)
        self.assertNotIn("source-input-boundary HOL_INPUT_ROOT", deps)
        self.assertNotIn("retained caller:", deps)

    def test_multiple_numeric_inputs_keep_same_line_slots_and_calculations(self):
        # Equal result types must not conceal swapped inputs. Numeric
        # selection changes a call's argument, not its source position.
        source = self.numeric_input_fixture(
            "match op { 23 => { let first = acquire(op); "
            "let second = acquire(99); A = first + x; "
            "D = xor_vec(second, A) }, _ => D = x }")
        text, deps = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23__inputs_2",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",),
            expected_inputs=2)
        self.assertIn("(v0:8 word)", text)
        self.assertIn("(v1:8 word)", text)
        self.assertIn("(v2:8 word)", text)
        self.assertIn("[input 0, parameter __hol_input0] <- acquire(op) "
                      "(specialized call: acquire(23))", deps)
        self.assertIn("[input 1, parameter __hol_input1] <- acquire(99)", deps)
        spans = re.findall(
            r"at unit-input\.sail:(\d+):(\d+)-(\d+):(\d+) : bitvector\(8\)",
            deps)
        self.assertEqual(len(spans), 2, deps)
        first, second = [tuple(map(int, span)) for span in spans]
        self.assertEqual(first[0], second[0])
        self.assertEqual(first[0], first[2])
        self.assertEqual(second[0], second[2])
        self.assertLess(first[1], first[3])
        self.assertLess(first[3], second[1])
        self.assertLess(second[1], second[3])
        def calculation_inputs(model):
            # Resolve the printer's retained local bindings, without
            # assuming its internal variable numbers or removing effects.
            aliases = dict(re.findall(
                r"\(let \(?(v\d+)(?::8 word)?\)? = \((v\d+):8 word\) in",
                model))

            def original(identifier):
                visited = set()
                while identifier in aliases:
                    self.assertNotIn(identifier, visited)
                    visited.add(identifier)
                    identifier = aliases[identifier]
                return identifier

            add = re.search(
                r"word_add \((v\d+):8 word\) \((v\d+):8 word\)", model)
            xor = re.search(r"word_xor \((v\d+):8 word\)", model)
            self.assertIsNotNone(add, model)
            self.assertIsNotNone(xor, model)
            return (tuple(original(argument) for argument in add.groups()),
                    original(xor.group(1)))

        self.assertEqual(calculation_inputs(text), (("v1", "v0"), "v2"))
        swapped, _ = self.run_sail(source.replace(
            "A = first + x; D = xor_vec(second, A)",
            "A = second + x; D = xor_vec(first, A)"),
            roots=("HOL_INPUT_ROOT__acquire__op_23__inputs_2",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",),
            expected_inputs=2)
        self.assertEqual(calculation_inputs(swapped), (("v2", "v0"), "v1"))
        self.assertNotEqual(text, swapped)

    def test_multiple_inputs_count_static_calls_in_exclusive_branches(self):
        source = self.input_lift_fixture(
            "if __hol_input0 == 0x00 then D = acquire(1) "
            "else A = acquire(2)")
        text, deps = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__inputs_2",),
            input_lift=("ROOT", "acquire"), expected_inputs=2)
        self.assertIn("if", text)
        for slot, register in ((1, "D"), (2, "A")):
            self.assertRegex(text,
                rf"\(let (?P<bound>v\d+) = \(v{slot}:8 word\) in\s+"
                rf"\(let v\d+ = \(write reg_{register} (?P=bound) s\)")
        self.assertIn("[input 0,", deps)
        self.assertIn("[input 1,", deps)
        self.assertIn("<- acquire(1)", deps)
        self.assertIn("<- acquire(2)", deps)

    def test_multiple_inputs_reject_wrong_counts_and_invalid_requests(self):
        for body in ("D = __hol_input0", "D = acquire(1)",
                     "A = acquire(1); A = acquire(1); D = acquire(1)"):
            with self.subTest(body=body):
                self.run_sail(self.input_lift_fixture(body),
                    roots=("HOL_INPUT_ROOT__acquire__inputs_2",),
                    input_lift=("ROOT", "acquire"), expected_inputs=2,
                    error="requires exactly 2 direct input calls")
        for count in (0, -1):
            with self.subTest(count=count):
                self.run_sail(self.input_lift_fixture("D = acquire(1)"),
                    roots=("unused",), input_lift=("ROOT", "acquire"),
                    expected_inputs=count, error="input count must be positive")

    def test_multiple_inputs_reject_missing_or_duplicate_locations(self):
        source = self.input_lift_fixture("A = acquire(1); D = acquire(1)")
        for mutation, error in (
                ("missing", "multiple inputs require real source spans"),
                ("duplicate", "multiple inputs have duplicate source spans")):
            with self.subTest(mutation=mutation):
                self.run_sail(source,
                    roots=("HOL_INPUT_ROOT__acquire__inputs_2",),
                    input_lift=("ROOT", "acquire"), expected_inputs=2,
                    input_spans=mutation, error=error)

    def test_multiple_inputs_preserve_guards_and_early_return(self):
        source = self.input_lift_fixture("""
    if __hol_input0 == 0x00 then return ();
    A = acquire(1);
    D = acquire(1)
""")
        text, deps = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__inputs_2",),
            input_lift=("ROOT", "acquire"), expected_inputs=2)
        self.assertIn("if", text)
        self.assertIn("write reg_A", text)
        self.assertIn("write reg_D", text)
        self.assertIn("[input 0,", deps)
        self.assertIn("[input 1,", deps)

    def test_multiple_inputs_keep_literal_argument_and_loop_checks(self):
        for body, error in (
                ("A = acquire(1); D = acquire(unsigned(__hol_input0))",
                 "input call arguments must be literals"),
                ("A = acquire(1); foreach (i from 0 to 1) { D = acquire(1) }",
                 "input calls under loops are unsupported")):
            with self.subTest(body=body):
                self.run_sail(self.input_lift_fixture(body),
                    roots=("HOL_INPUT_ROOT__acquire__inputs_2",),
                    input_lift=("ROOT", "acquire"), expected_inputs=2, error=error)

    def test_input_lift_refuses_argument_reads_or_effects(self):
        source = self.input_lift_fixture("D = acquire(unsigned(__hol_input0))")
        self.run_sail(source, roots=("HOL_INPUT_ROOT__acquire",),
            input_lift=("ROOT", "acquire"),
            error="input call arguments must be literals")
        source = source.replace("val ROOT :", """
val next : unit -> int
function next() = { A = 0x01; 1 }
val ROOT :""").replace("unsigned(__hol_input0)", "next()")
        self.run_sail(source, roots=("HOL_INPUT_ROOT__acquire",),
            input_lift=("ROOT", "acquire"),
            error="input call arguments must be literals")

    @staticmethod
    def numeric_input_fixture(body):
        return """
register A : bits(8)
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val ROOT : (range(0, 255), bits(8)) -> unit
function ROOT(op, x) = {
""" + body + """
}
"""

    def test_numeric_input_selection_retains_body_and_records_selection(self):
        source = self.numeric_input_fixture("""
    A = x;
    match op {
      23 => { let supplied = acquire(1); D = x + supplied },
      24 => { A = acquire(1); D = acquire(1) },
      _ => D = 0x77
    }
""")
        options = dict(roots=("HOL_INPUT_ROOT__acquire__op_23",),
                       input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        text, deps = self.run_sail(source, **options)
        self.assertIn("(v0:8 word)", text)
        self.assertIn("(v1:8 word)", text)
        self.assertNotIn("(v0:int)", text)
        self.assertIn("word_add", text)
        self.assertLess(text.index("write reg_A"), text.index("write reg_D"))
        self.assertNotIn("word 119", text)
        self.assertIn("fix op=23 in ROOT", deps)
        self.assertIn("acquire(1)", deps)
        self.assertIn("unit-input.sail:", deps)
        changed, _ = self.run_sail(source.replace(
            "x + supplied", "xor_vec(x,supplied)"), **options)
        self.assertIn("word_xor", changed)
        self.assertNotIn("word_add", changed)
        original, _ = self.run_sail(source, with_sources=True, quote_sources=True,
                                    **options)
        self.assertIn("Fixed source arguments: op=23 in ROOT", original)
        self.assertIn("match op", original)
        self.assertIn("let supplied = acquire(1)", original)

    def test_numeric_input_selection_checks_arguments_and_removes_all_fixed(self):
        source = """
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val ROOT : range(0, 255) -> unit
function ROOT(op) = match op { 23 => D = acquire(1), _ => D = 0x00 }
"""
        text, _ = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        self.assertIn("(v0:8 word)", text)
        # Only the root's parameters matter here. Retained source lets may
        # introduce their own v1 after the definition's signature.
        self.assertNotIn("(v1:", text.split(" =\n", 1)[0])
        for arguments, error in (
                (("other=23",), "unknown fixed argument"),
                (("op=23", "op=24"), "duplicate fixed argument"),
                (("op=256",), "fixed argument does not satisfy its source type")):
            with self.subTest(arguments=arguments):
                self.run_sail(source, roots=("unused",),
                    input_lift=("ROOT", "acquire"), fixed_arguments=arguments, error=error)

    def test_numeric_input_selection_preserves_case_order_and_guards(self):
        source = self.numeric_input_fixture("""
    match op {
      _ => { let supplied = acquire(1); D = x + supplied },
      23 => { A = acquire(1); D = acquire(1) }
    }
""")
        options = dict(roots=("HOL_INPUT_ROOT__acquire__op_23",),
                       input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        text, _ = self.run_sail(source, **options)
        self.assertIn("word_add", text)
        self.assertNotIn("write reg_A", text)
        guarded = self.numeric_input_fixture("""
    match op {
      23 if x == 0x00 => { A = acquire(1); D = x },
      23 => D = acquire(1),
      _ => D = 0x00
    }
""")
        self.run_sail(guarded, error="exactly one direct input call", **options)

    def test_numeric_input_selection_retains_immutable_shadowing(self):
        source = self.numeric_input_fixture("""
    let op : int = unsigned(x);
    let supplied = acquire(1);
    D = if op == 23 then x + supplied else supplied
""")
        text, _ = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        self.assertIn("(if ", text)
        self.assertIn("val", text)
        self.assertIn("word_add", text)

    def test_numeric_input_selection_tries_closed_guards_in_order(self):
        source = self.numeric_input_fixture("""
    match op {
      tag if tag == 26 | tag == 90 => { A = acquire(1); D = acquire(1) },
      tag if 80 <= tag & tag <= 83 => { A = acquire(1); D = acquire(1) },
      tag if tag == 23 => {
        let tag : int = unsigned(x);
        let supplied = acquire(1);
        D = if tag == 0 then x + supplied else supplied
      },
      23 => { A = acquire(1); D = acquire(1) },
      _ => D = 0x00
    }
""")
        text, _ = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        self.assertIn("word_add", text)
        self.assertIn("(if ", text)
        self.assertNotIn("write reg_A", text)
        # A nonmatching literal arm's guard is never evaluated.
        source = self.numeric_input_fixture("""
    match op {
      24 if touched(x) => { A = acquire(1); D = acquire(1) },
      23 => D = acquire(1),
      _ => D = 0x00
    }
""").replace("val ROOT :", """
val touched : bits(8) -> bool
function touched(x) = { A = x; true }
val ROOT :""")
        text, _ = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        self.assertNotIn("write reg_A", text)

    def test_numeric_input_selection_keeps_undecidable_guards(self):
        guards = (
            ("tag == unsigned(x)", ""),
            ("helper(tag)", """
val helper : int -> bool
function helper(tag) = tag == 23
"""),
            ("and_bool(touched(x),false)", """
val touched : bits(8) -> bool
function touched(x) = { A = x; true }
"""),
            ("or_bool(touched(x),true)", """
val touched : bits(8) -> bool
function touched(x) = { A = x; false }
"""),
            ("chosen(tag)", """
val chosen = pure "undefined_bool" : int -> bool
"""),
        )
        for guard, declaration in guards:
            with self.subTest(guard=guard):
                source = self.numeric_input_fixture(
                    "match op { tag if " + guard +
                    " => D = acquire(1), _ => D = acquire(1) }")
                source = source.replace("val ROOT :", declaration + "\nval ROOT :")
                self.run_sail(source,
                    roots=("HOL_INPUT_ROOT__acquire__op_23",),
                    input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",),
                    error="exactly one direct input call")

    def test_numeric_case_binding_preserves_outer_scope_loop_bounds(self):
        # The loop's upper bound denotes case-bound k=1, not the unrelated
        # remaining formal k. Retaining an immutable case binding prevents
        # substitution from leaving this same-name loop unresolved.
        source = """
register A : bits(8)
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val ROOT : (range(0,255), bits(8)) -> unit
function ROOT(op,k) = match op {
  k if k == 1 => {
    foreach (k from 0 to k) { A = A + 0x01 };
    D = acquire(1)
  },
  _ => D = acquire(1)
}
"""
        text, _ = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_1",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=1",))
        self.assertEqual(text.count("write reg_A"), 2)
        self.assertIn("write reg_D", text)

    def test_numeric_input_boundary_preserves_original_call_and_full_span(self):
        # Both calls are on the same line; only their full spans identify
        # the source occurrence reached by op=23.
        source = self.numeric_input_fixture(
            "match op { 23 => D = acquire(op), 24 => D = acquire(99), _ => D = x }")
        options = dict(roots=("HOL_INPUT_ROOT__acquire__op_23",),
                       input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        _, deps = self.run_sail(source, **options)
        self.assertIn("<- acquire(op) (specialized call: acquire(23))", deps)
        self.assertNotIn("acquire(99)", deps)
        _, unchanged = self.run_sail(source.replace("acquire(op)", "acquire(1)"),
                                     **options)
        self.assertIn("<- acquire(1) at unit-input.sail:", unchanged)
        self.assertNotIn("specialized call:", unchanged)

    def test_numeric_selection_canonicalizes_multiple_closed_parameters(self):
        source = """
register D : bits(8)
val acquire = impure "unsupported_acquire" : int -> bits(8)
val ROOT : (range(0,255), range(0,3), bits(8)) -> unit
function ROOT(op,mode,x) = match op {
  23 => match mode { 3 => D = x + acquire(1), _ => D = acquire(2) },
  _ => D = acquire(3)
}
"""
        options = dict(roots=("HOL_INPUT_ROOT__acquire__mode_3__op_23",),
                       input_lift=("ROOT", "acquire"))
        text, deps = self.run_sail(source, fixed_arguments=("op=23", "mode=3"),
                                  **options)
        reordered, reordered_deps = self.run_sail(
            source, fixed_arguments=("mode=3", "op=23"), **options)
        self.assertEqual(text, reordered)
        self.assertEqual(deps, reordered_deps)
        self.assertIn("fix mode=3,op=23 in ROOT", deps)
        self.assertNotIn("(v0:int)", text)
        self.assertIn("word_add", text)
        dependent = self.numeric_input_fixture("D = acquire(1)").replace(
            "(range(0, 255), bits(8))", "forall 'n, 0 <= 'n <= 255. (int('n), bits(8))")
        self.run_sail(dependent, roots=("unused",), input_lift=("ROOT", "acquire"),
            fixed_arguments=("op=23",),
            error="fixed argument requires a closed numeric type")

    @staticmethod
    def fixed_bit_input_fixture(width):
        return f"""
register D : bits({width})
val acquire = impure "unsupported_acquire" : int(1) -> bits({width})
val ROOT : (bits({width}), bits({width})) -> unit
function ROOT(op,x) = {{
  let supplied = acquire(1);
  D = (supplied + op) + x
}}
"""

    def test_fixed_bit_arguments_preserve_width_and_source_calculation(self):
        for width, value in ((1, 1), (8, 56), (16, 65535), (64, 56)):
            with self.subTest(width=width, value=value):
                text, deps = self.run_sail(self.fixed_bit_input_fixture(width),
                    roots=(f"HOL_INPUT_ROOT__acquire__op_{value}",),
                    input_lift=("ROOT", "acquire"),
                    fixed_arguments=(f"op={value}",))
                self.assertIn(f"word {value}", text)
                self.assertIn("word_add", text)
                self.assertIn(f"fix op={value} in ROOT", deps)
                self.assertIn(f"__hol_input0] <- acquire(1)", deps)
                self.assertIn(f":{width} word", text)

    def test_fixed_bit_arguments_reject_negative_and_oversized_values(self):
        for width, value in ((1, -1), (1, 2), (8, 256), (16, 65536)):
            with self.subTest(width=width, value=value):
                self.run_sail(self.fixed_bit_input_fixture(width),
                    roots=("unused",), input_lift=("ROOT", "acquire"),
                    fixed_arguments=(f"op={value}",),
                    error="fixed bit argument is outside its source width")

    def test_fixed_bit_arguments_preserve_host_integer_boundary(self):
        # Read the compiler's machine word size, not Python's integer size.
        word_size = int(subprocess.check_output(
            ["ocamlc", "-config-var", "word_size"], text=True).strip())
        max_int = (1 << (word_size - 2)) - 1
        for width in (word_size - 2, word_size - 1, word_size, 2048):
            with self.subTest(width=width):
                text, _ = self.run_sail(self.fixed_bit_input_fixture(width),
                    roots=(f"HOL_INPUT_ROOT__acquire__op_{max_int}",),
                    input_lift=("ROOT", "acquire"),
                    fixed_arguments=(f"op={max_int}",))
                self.assertIn(f"word {max_int}", text)
                self.assertIn(f":{width} word", text)
        self.run_sail(self.fixed_bit_input_fixture(word_size - 3),
            roots=("unused",), input_lift=("ROOT", "acquire"),
            fixed_arguments=(f"op={max_int}",),
            error="fixed bit argument is outside its source width")

    def test_fixed_bit_arguments_reject_dependent_widths(self):
        source = self.numeric_input_fixture("D = acquire(1)").replace(
            "(range(0, 255), bits(8))",
            "forall 'n, 1 <= 'n & 'n <= 64. (bits('n), bits(8))")
        self.run_sail(source, roots=("unused",), input_lift=("ROOT", "acquire"),
            fixed_arguments=("op=23",),
            error="fixed argument requires a closed numeric type or bitvector width")

    def test_fixed_bit_arguments_accept_closed_width_synonyms(self):
        source = self.fixed_bit_input_fixture(8).replace(
            "val ROOT : (bits(8), bits(8))",
            "type opcode = bits(8)\nval ROOT : (opcode, bits(8))")
        text, _ = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        self.assertIn("word 23", text)
        self.assertIn("word_add", text)

    def test_fixed_bit_arguments_reject_empty_and_excessive_widths(self):
        for width in (0, 2049):
            with self.subTest(width=width):
                source = self.numeric_input_fixture("D = acquire(1)").replace(
                    "(range(0, 255), bits(8))", f"(bits({width}), bits(8))")
                self.run_sail(source, roots=("unused",),
                    input_lift=("ROOT", "acquire"), fixed_arguments=("op=0",),
                    error="fixed bit argument requires width 1 through 2048")

    def test_fixed_bit_argument_selection_changes_the_checked_literal(self):
        options = dict(input_lift=("ROOT", "acquire"))
        first, _ = self.run_sail(self.fixed_bit_input_fixture(8),
            roots=("HOL_INPUT_ROOT__acquire__op_56",),
            fixed_arguments=("op=56",), **options)
        second, _ = self.run_sail(self.fixed_bit_input_fixture(8),
            roots=("HOL_INPUT_ROOT__acquire__op_57",),
            fixed_arguments=("op=57",), **options)
        self.assertIn("word 56", first)
        self.assertIn("word 57", second)
        self.assertNotEqual(first, second)

    def test_numeric_input_selection_refuses_mutable_and_loop_shadows(self):
        for body, error in (
                ("var op : int = unsigned(x); D = acquire(1)",
                 "Cannot modify immutable let-bound constant"),
                ("foreach (op from 0 to 1) { D = acquire(1) }",
                 "fixed argument has a loop shadow")):
            with self.subTest(body=body):
                self.run_sail(self.numeric_input_fixture(body),
                    roots=("HOL_INPUT_ROOT__acquire__op_23",),
                    input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",),
                    error=error)

    def test_numeric_input_selection_retains_effectful_boolean_arguments(self):
        source = self.numeric_input_fixture("""
    match op {
      23 => {
        let ignored = and_bool(touched(x), false);
        let ignored_again = or_bool(touched(x + 1), true);
        let supplied = acquire(1);
        D = x + supplied
      },
      _ => D = 0x00
    }
""").replace("val ROOT :", """
val touched : bits(8) -> bool
function touched(x) = { A = x; x == 0x00 }
val ROOT :""")
        text, _ = self.run_sail(source,
            roots=("HOL_INPUT_ROOT__acquire__op_23",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        # The helper is defined once. Its second call appears in both
        # branches of the first Boolean result; each path threads the
        # first call's state into the second call, then into D's write.
        helper, root = text.split(
            "let sail_hl_HOL_5fINPUT_5fROOT_5f_5facquire_5f_5fop_5f23 =", 1)
        self.assertEqual(helper.count("write reg_A"), 1)
        calls = re.findall(
            r"\(let \((v\d+),(v\d+)\) = \(let v\d+ = .*? in\n\s*"
            r"\(sail_hl_shared_output_touched_5f0 reg_A v\d+ s (s|v\d+)\)\)",
            root, re.S)
        self.assertEqual(len(calls), 3)
        self.assertEqual(calls[0][2], "s")
        self.assertTrue(all(call[2] == calls[0][1] for call in calls[1:]))
        final_states = re.findall(r"\(write reg_D v\d+ (v\d+)\)", root)
        self.assertEqual(set(final_states), {call[1] for call in calls[1:]})
        self.assertIn("word_add", text)

    def test_numeric_input_selection_retains_assertions_before_and_after_input(self):
        for body in (
                "assert(x == 0x00); let supplied = acquire(1); D = supplied",
                "let supplied = acquire(1); assert(x == 0x00); D = supplied"):
            with self.subTest(body=body):
                text, _ = self.run_sail(self.numeric_input_fixture(
                    "match op { 23 => { " + body + " }, _ => D = 0x00 }"),
                    roots=("HOL_INPUT_ROOT__acquire__op_23",),
                    input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
                self.assertIn("write reg_D", text)
                self.assertIn("F", text)
                self.assertIn("(if ", text)

    def test_numeric_input_selection_rejects_multiple_calls_and_omits_unused_boundary(self):
        source = self.numeric_input_fixture(
            "match op { 23 => { A = acquire(1); D = acquire(1) }, _ => D = x }")
        self.run_sail(source, roots=("HOL_INPUT_ROOT__acquire__op_23",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",),
            error="exactly one direct input call")
        source = self.numeric_input_fixture(
            "match op { 23 => D = acquire(1), _ => D = x }") + """
val unrelated : unit -> bits(8)
function unrelated() = 0x11
"""
        _, deps = self.run_sail(source, roots=("unrelated",),
            input_lift=("ROOT", "acquire"), fixed_arguments=("op=23",))
        self.assertNotIn("source-input-boundary", deps)

    def test_initial_enum_is_checked_and_rejects_invalidating_writes(self):
        source = """
enum Mode = { LongMode, OtherMode }
register cur_mode : Mode
register D : bits(8)
val ROOT : bits(8) -> unit
function ROOT(x) = {
    match cur_mode {
        LongMode => D = x,
        OtherMode => D = not_vec(x)
    }
}
"""
        options = dict(roots=("ROOT",), architecture="x86",
                       initial_enums=("cur_mode=LongMode",))
        text, deps = self.run_sail(source, **options)
        self.assertIn("write reg_D", text)
        self.assertNotIn("word_not", text)
        self.assertIn("initial-enum cur_mode=LongMode", deps)
        self.run_sail(source, roots=("ROOT",), architecture="x86",
            initial_enums=("cur_mode=UnknownMode",),
            error="assumed constructor is not in the source register's enum")
        self.run_sail(source.replace("match cur_mode",
                                    "cur_mode = OtherMode; match cur_mode"),
            **options, error="write may invalidate source assumption")
        self.run_sail(source,
            roots=("ROOT",), architecture="x86",
            initial_enums=("cur_mode=LongMode", "cur_mode=LongMode"),
            error="duplicate assumption")

    def test_initial_boolean_is_checked_and_retains_other_effects(self):
        source = """
register available : bool
register D : bits(8)
val next : unit -> bits(8)
function next() = { D = D + 1; D }
val ROOT : unit -> unit
function ROOT() = {
    let x = next();
    D = if available then x else not_vec(x)
}
"""
        for value in ("true", "false"):
            text, deps = self.run_computation(source, architecture="x86",
                initial_bools=(f"available={value}",))
            self.assertIn("word_add", text)
            self.assertIn("write reg_D", text)
            self.assertEqual("word_not" in text, value == "false")
            self.assertIn(f"initial-bool available={value}", deps)
        self.run_computation(source, architecture="x86",
            initial_bools=("available=true", "available=false"),
            error="duplicate assumption")
        self.run_computation(source.replace("register available : bool",
                                           "register available : bits(1)")
                            .replace("if available", "if available == 0b1"),
            architecture="x86", initial_bools=("available=true",),
            error="assumed Boolean requires bool")
        self.run_computation(source.replace("register available : bool",
                                           "let available : bool = true"),
            architecture="x86", initial_bools=("available=true",),
            error="assumed Boolean requires a source register")

    def test_initial_boolean_rejects_helper_and_pre_read_writes(self):
        source = """
register available : bool
register D : bits(8)
val change : unit -> unit
function change() = available = false
val ROOT : unit -> unit
function ROOT() = { change(); D = if available then 0x01 else 0x02 }
"""
        options = dict(architecture="x86", initial_bools=("available=true",),
                       error="write may invalidate source assumption")
        self.run_computation(source, **options)
        self.run_computation(source.replace("change();", "available = false;"),
                             **options)
        self.run_computation(source.replace("change(); D =", "D =")
                             .replace("else 0x02", "else 0x02; change()"),
                             **options)

    def test_initial_boolean_does_not_fix_unrelated_parameters(self):
        source = """
register available : bool
register D : bits(8)
val ROOT : bits(1) -> unit
function ROOT(x) = {
    let enabled : bool = x == 0b1;
    D = if enabled then 0x01 else 0x02
}
"""
        text, deps = self.run_computation(source, architecture="x86",
            initial_bools=("available=true",))
        self.assertIn("(if ", text)
        self.assertIn("(word 1)", text)
        self.assertIn("(word 2)", text)
        self.assertNotIn("used-assumption initial-bool", deps)
        self.run_computation(source, initial_bools=("available=true",),
            error="source assumptions require an Arm or x86 architecture")

    def test_initial_boolean_rejects_refined_and_existential_registers(self):
        for declared in ("bool(true)", "{('p : Bool), 'p. bool('p)}"):
            source = f"""
register available : {declared} = true
register D : bits(8)
val ROOT : unit -> unit
function ROOT() = D = if available then 0x01 else 0x02
"""
            self.run_computation(source, architecture="x86",
                initial_bools=("available=false",),
                error="assumed Boolean requires bool")

    def test_generic_equality_uses_checked_types_and_retains_arguments(self):
        for name in ("eq_anything", "neq_anything"):
            source = f"""
enum Mode = {{ LongMode, OtherMode }}
val {name} = pure "{name}" : forall ('a : Type). ('a, 'a) -> bool
register cur_mode : Mode
register A : bits(8)
register D : bool
val next : unit -> Mode
function next() = {{ A = A + 1; LongMode }}
val ROOT : unit -> unit
function ROOT() = D = {name}(cur_mode, next())
"""
            text, deps = self.run_computation(source, architecture="x86",
                initial_enums=("cur_mode=LongMode",))
            self.assertIn(f"primitive-contract {name}", deps)
            self.assertIn("write reg_A", text)
            self.assertIn("write reg_D", text)
            self.run_computation(source.replace(f'pure "{name}"', f'impure "{name}"'),
                architecture="x86", initial_enums=("cur_mode=LongMode",),
                error="stateless operations require a pure external declaration")
            self.run_sail(f"""
val {name} = pure "{name}" : (bits(16), bits(8)) -> bool
val ROOT : (bits(16), bits(8)) -> bool
function ROOT(x,y) = {name}(x,y)
""", roots=("ROOT",), error="generic equality requires matching operand types")

    def test_slice_bounds_select_constant_prefix_but_not_wrapping_slice(self):
        source = """
register D : bits(8)
val unsupported = impure "unsupported" : unit -> bits(8)
val ROOT : bits(6) -> unit
function ROOT(x) = {
    let joined : bits(8) = 0b11 @ x;
    D = if unsigned(joined[7 .. 6]) == 3 then joined else unsupported()
}
"""
        text, _ = self.run_computation(source)
        self.assertIn("word_join", text)
        self.assertIn("word_subword", text)
        self.assertNotIn("unsupported", text)
        self.run_computation(source.replace("joined[7 .. 6]", "joined[1 .. 0]"),
            error="unsupported primitive unsupported")

    def test_enum_match_evaluates_effectful_scrutinee_once(self):
        source = """
enum Choice = { First, Second }
register A : bits(8)
register D : bits(8)
val choose : unit -> Choice
function choose() = { A = A + 1; First }
val ROOT : unit -> unit
function ROOT() = match choose() {
    First => D = A,
    Second => D = A + 2
}
"""
        text, _ = self.run_computation(source)
        body = text.split("let sail_hl_ROOT =", 1)[1].split("`;;", 1)[0]
        self.assertEqual(text.count("write reg_A"), 1)
        self.assertEqual(body.count(self.shared_name(text, "choose")), 1)
        self.assertLess(body.index(self.shared_name(text, "choose")),
                        body.index("write reg_D"))

    def test_record_update_preserves_base_and_field_evaluation_order(self):
        source = """
struct Pair = { first : bits(8), second : bits(8) }
register A : bits(8)
register D : bits(8)
val original : unit -> Pair
function original() = { A = 0x01; struct { first = 0x11, second = A } }
val changed : unit -> bits(8)
function changed() = { A = 0x02; A }
val ROOT : unit -> unit
function ROOT() = {
    let pair = { original() with first = changed() };
    D = pair.second;
    A = pair.first
}
"""
        text, _ = self.run_computation(source)
        body = text.split("let sail_hl_ROOT =", 1)[1].split("`;;", 1)[0]
        self.assertEqual(text.count("write reg_A"), 3)
        self.assertLess(body.index(self.shared_name(text, "original")),
                        body.index(self.shared_name(text, "changed")))
        self.assertLess(body.index(self.shared_name(text, "changed")),
                        body.index("write reg_D"))
        self.assertIn("FST", body)
        self.assertIn("SND", body)
        pure_source = """
struct Pair = { first : bits(8), second : bits(8) }
val ROOT : bits(8) -> bits(8)
function ROOT(x) = {
    let pair = { struct Pair { first = x, second = 0x22 } with first = x + x };
    pair.first
}
"""
        pure_text, _ = self.run_sail(pure_source, roots=("ROOT",))
        self.assertIn("word_add", pure_text)
        self.assertNotIn("write", pure_text)

    def test_record_helper_static_field_fixes_dependent_result_width(self):
        source = """
struct Configuration = { wide : bool, unused : bits(8) }
register D : bits(128)
val configured : unit -> Configuration
function configured() = struct { wide = false, unused = 0x11 }
val width : Configuration -> {128,256}
function width(settings) = if settings.wide then 256 else 128
val read_simd = pure "read_simd" : forall 'n, 'n in {128,256}.
    (int('n), int) -> bits('n)
val ROOT : unit -> unit
function ROOT() = {
    let settings = { configured() with unused = 0x22 };
    let length = width(settings);
    if length == 128 then D = read_simd(length,0)[127..0] else assert(false)
}
"""
        text, _ = self.run_computation(source, architecture="x86")
        self.assertIn("write reg_D", text)
        self.assertNotIn("Sail-assertion-abort", text)
        # Flipping the original field must change the reachable branch.
        changed, deps = self.run_computation(
            source.replace("wide = false", "wide = true"), architecture="x86")
        self.assertIn("guarded-assertion false", deps)
        self.assertIn("\\(s:x86state) (t:x86state).", changed)
        self.assertRegex(changed, r"\belse F\b|\bin\s+F\b|\.\s*\(?F\b")
        self.assertNotIn("fault-any-final-state", deps)

    def test_record_helper_facts_respect_shadowed_and_dynamic_fields(self):
        source = """
struct Configuration = { wide : bool, unused : bits(8) }
register D : bool
val configured : bool -> Configuration
function configured(wide) = {
    let saved = wide;
    let wide = true;
    struct { wide = saved, unused = 0x11 }
}
val ROOT : bits(1) -> unit
function ROOT(flag) = {
    let settings = { configured(flag == 0b1) with unused = 0x22 };
    D = settings.wide
}
"""
        for literal, value in (("false", "F"), ("true", "T")):
            with self.subTest(literal=literal):
                text, _ = self.run_computation(
                    source.replace("configured(flag == 0b1)",
                                   "configured(" + literal + ")"))
                self.assertRegex(text, r"write reg_D \(" + value + r":bool\)")
        text, _ = self.run_computation(source)
        body = text.split("let sail_hl_ROOT =", 1)[1]
        self.assertNotRegex(body, r"write reg_D \([FT]:bool\)")
        self.assertIn("FST", body)

    def test_record_helper_enum_result_selects_actual_branch(self):
        source = """
enum Prefix = { Prefix_None, Prefix_66, Prefix_F2, Prefix_F3 }
struct Settings = { repne : bool, rep : bool, opsize : bool, tag : range(0,15) }
register D : bool
val eq_any = pure "eq_any" : forall ('a : Type). ('a, 'a) -> bool
val configured : unit -> Settings
function configured() =
    struct { repne = false, rep = false, opsize = false, tag = 0 }
val mandatory : Settings -> Prefix
function mandatory(settings) =
    if settings.repne then Prefix_F2
    else if settings.rep then Prefix_F3
    else if settings.opsize then Prefix_66
    else Prefix_None
val opaque = pure "opaque" : unit -> bool
val ROOT : unit -> unit
function ROOT() = {
    let settings = { configured() with opsize = true };
    let selected = mandatory(settings);
    if or_bool(not_bool(eq_any(selected, Prefix_66)),
               not_bool(eq_int(settings.tag, 0))) then D = opaque()
    else D = true
}
"""
        text, _ = self.run_computation(source, architecture="x86")
        self.assertIn("write reg_D (T:bool)", text)
        self.assertNotIn("opaque", text)
        # Each actual source check remains observable after specialization.
        for changed in (
                source.replace("opsize = true", "opsize = false"),
                source.replace("repne = false", "repne = true"),
                source.replace("rep = false", "rep = true"),
                source.replace("tag = 0", "tag = 1"),
                source.replace("opsize = true", "opsize = D")):
            with self.subTest(changed=changed):
                self.run_computation(changed, architecture="x86",
                                     error="unsupported primitive opaque")
        # The result can refer to an earlier binding whose name is shadowed.
        scoped = source.replace(
            "function mandatory(settings) =\n",
            "function mandatory(settings) = {\n    let saved =\n").replace(
            "else Prefix_None\nval opaque",
            "else Prefix_None;\n"
            "    let saved_again = saved;\n"
            "    let saved = Prefix_F2;\n"
            "    saved_again\n}\nval opaque")
        scoped_text, _ = self.run_computation(scoped, architecture="x86")
        self.assertIn("write reg_D (T:bool)", scoped_text)
        # Recovering a fact must not skip the argument helper's state effect.
        effectful = source.replace(
            "function configured() =\n    struct",
            "function configured() = { D = false;\n    struct").replace(
            "opsize = false, tag = 0 }\nval mandatory",
            "opsize = false, tag = 0 } }\nval mandatory")
        effect_text, _ = self.run_computation(effectful, architecture="x86")
        self.assertEqual(effect_text.count("write reg_D"), 2)
        self.assertLess(effect_text.index("write reg_D (F:bool)"),
                        effect_text.index("write reg_D (T:bool)"))

    def test_implicit_numeric_witness_respects_lexical_shadowing(self):
        source = """
register D : bits(128)
val choose : bool -> {128,256}
function choose(wide) = if wide then 256 else 128
val read_simd = pure "read_simd" : forall 'n, 'n in {128,256}.
    (int('n), int) -> bits('n)
val ROOT : unit -> unit
function ROOT() = {
    let length = choose(false);
    {
        let length = choose(true);
        D = read_simd(length,0)[127..0]
    };
    D = read_simd(length,1)[127..0]
}
"""
        text, _ = self.run_computation(source, architecture="x86")
        self.assertIn("SIMD256", text)
        self.assertIn("SIMD128", text)
        self.assertEqual(text.count("write reg_D"), 2)
        self.run_computation(
            source.replace("val ROOT : unit -> unit", "val ROOT : bits(1) -> unit")
                  .replace("function ROOT()", "function ROOT(flag)")
                  .replace("let length = choose(false)",
                           "let length = choose(flag == 0b1)"),
            architecture="x86", error="internal dynamic bitvectors: read_simd")

    def test_source_annotations_preserve_original_sail_and_locations(self):
        body = "function identity(x) = x"
        source = HEADER + "val identity : bits(32) -> bits(32)\n" + body + "\n"
        text, _ = self.run_sail(source, roots=("identity",), with_sources=True,
                                quote_sources=True)
        self.assertIn(body, text)
        self.assertIn("unit-input.sail", text)
        self.assertRegex(text, r'unit-input\.sail.*:4')
        self.assertNotIn(body, without_comments(text))
        # By default the model gives only the name and path:line.
        reference, _ = self.run_sail(source, roots=("identity",), with_sources=True)
        self.assertNotIn(body, reference)
        self.assertNotIn("sail_source|", reference)
        self.assertRegex(reference, r'\(\* Sail source "identity", "[^"]*unit-input\.sail:4" \*\)')

    def test_source_annotations_protect_comment_and_quote_delimiters(self):
        payload = '*) " (* |sail_source}'
        source = HEADER + (
            'val text : unit -> string\n'
            'function text() = "*) \\" (* |sail_source}"\n')
        text, _ = self.run_sail(source, roots=("text",), with_sources=True,
                                quote_sources=True)
        self.assertIn('function text()', text)
        self.assertIn("{sail_sourcex|", text)
        code = without_comments(text)
        self.assertNotIn(payload, code)
        self.assertIn("new_definition", code)

    def test_generated_bitfield_helpers_trace_the_original_declaration(self):
        declaration = "bitfield Flags : bits(8) = { low : 3 .. 0, high : 7 .. 4 }"
        source = HEADER + declaration + """
val FIELD : bits(8) -> bits(4)
function FIELD(x) = {
    let fields = Mk_Flags(x);
    _get_Flags_low(fields)
}
"""
        text, dependencies = self.run_sail(
            source, roots=("FIELD",), with_sources=True, quote_sources=True)
        self.assertIn(declaration, text)
        self.assertIn("Mk_Flags generated from type Flags", text)
        self.assertIn("_get_Flags_low generated from type Flags", text)
        self.assertRegex(text, r'unit-input\.sail.*:3')
        self.assertNotIn("EMPTY:", text)
        self.assertIn("inlined Mk_Flags", dependencies)
        self.assertIn("inlined _get_Flags_low", dependencies)

    def run_computation(self, source, **options):
        """Export ROOT as a state computation, with the usual refusal checks."""
        return self.run_sail(source, roots=("ROOT",),
                             **options)

    def assert_restricted_relation(self, text, dependencies, marker):
        """Check a failure outcome, not just that the exporter accepted it.

        A failed assertion is not an architectural fault: it has no normal
        final state. Inline failures print F directly; shared-helper failures
        propagate through the result case and print F in its rejected branch.
        """
        self.assertIn(marker, dependencies)
        self.assertIn("\\(s:armstate) (t:armstate).", text)
        self.assertRegex(text, r"\belse F\b|\bin\s+F\b|\.\s*\(?F\b")
        self.assertNotIn("fault-any-final-state", dependencies)

    def assert_guarded_relation(self, text, dependencies, condition=None):
        self.assert_restricted_relation(text, dependencies, "guarded-assertion")
        if condition is not None:
            self.assertTrue(any(
                line.startswith("guarded-assertion ") and condition in line
                for line in dependencies.splitlines()), dependencies)

    def assert_failed_relation(self, text, dependencies):
        # Sail rewrites literal assert(false) to exit(unit). This boundary
        # rejects normal outcomes; it must not become a fault admitting all.
        self.assert_restricted_relation(
            text, dependencies, "primitive-contract Sail-exit-no-normal-state")

    def assert_existential_choice(self, text, dependencies, hol_type):
        self.assertIn("primitive-contract Sail-undefined-existential", dependencies)
        self.assertRegex(text, r"\(\?\(v\d+:" + re.escape(hol_type) + r"\)")

    def test_sail_exit_keeps_argument_effects_and_skips_later_writes(self):
        source = """
register D : bits(64)
val ROOT : unit -> unit
function ROOT() = {
    exit({ D = 0x0000000000000001; () });
    D = 0x0000000000000002
}
"""
        text, deps = self.run_computation(source)
        self.assert_failed_relation(text, deps)
        self.assertEqual(text.count("write reg_D"), 1)
        self.assertIn("word 1", text)
        self.assertNotIn("word 2", text)

    def test_sp_control_read_retains_original_bitfield_type(self):
        source = """
bitfield SCTLRType : bits(64) = { SA : 3, SA0 : 4 }
val SCTLR_read__1 = impure "control_read" : unit -> SCTLRType
val AArch64_SPAlignmentFault = impure "fault" : unit -> unit
register D : bits(64)
val ROOT : unit -> unit
function ROOT() = {
    if SCTLR_read__1()[SA] != 0b0 then AArch64_SPAlignmentFault();
    D = 0x0000000000000002
}
"""
        text, deps = self.run_computation(source, architecture="aarch64")
        self.assertIn("reg_SCTLR_5fread_5f_5f1", text)
        self.assertIn("word_subword", text)
        self.assertIn("primitive-contract SCTLR_read__1", deps)
        self.assertIn("primitive-contract Arm-fault-any-final-state", deps)
        # Neither a bare word nor a different bitfield is this declaration.
        for changed in (
                source.replace("unit -> SCTLRType", "unit -> bits(64)")
                      .replace("SCTLR_read__1()[SA]", "SCTLR_read__1()[3]"),
                source.replace("SCTLRType", "OtherControl"),
                source.replace("bits(64) = { SA", "bits(32) = { SA")):
            with self.subTest(source=changed):
                self.run_computation(changed, architecture="aarch64",
                                     error="SCTLR_read__1 requires")

    def test_fault_relation_branch_exits_helper_and_instruction(self):
        text, deps = self.run_sail(
            FAULT_MODEL, roots=("FAULT_BRANCH",), architecture="aarch64",
            with_sources=True)
        code = without_comments(text)
        self.assertIn("\\(s:armstate) (t:armstate).", code)
        self.assertIn("INL", code)
        self.assertIn("sail_hl_result_case", code)
        self.assertIn(". T)", code)
        self.assertIn("word 2", code)
        self.assertNotIn("sail_hl_shared_output_fault", code)
        self.assertIn("primitive-contract Arm-fault-any-final-state", deps)
        self.assertIn("state-computation-root FAULT_BRANCH", deps)
        self.assertIn("state-preservation guarantees", text)

    def test_fault_relation_loop_join_propagates_nonlocal_exit(self):
        text, deps = self.run_sail(
            FAULT_MODEL, roots=("FAULT_LOOP",), architecture="aarch64")
        self.assertIn("INL", text)
        self.assertIn("INR", text)
        self.assertIn("sail_hl_result_case", text)
        self.assertIn("unrolled-static-loop", deps)

    def test_fault_loop_without_normal_exit_is_refused(self):
        self.run_sail(FAULT_MODEL, roots=("FAULT_ALWAYS",), architecture="aarch64",
                      error="a control-flow join requires a normal exit")

    def test_fault_relation_does_not_turn_source_refusals_into_faults(self):
        self.run_sail(
            FAULT_MODEL.replace("D = 0x0000000000000002",
                                "opaque(); D = 0x0000000000000002") +
            '\nval opaque = impure "opaque" : unit -> unit\n',
            roots=("FAULT_BRANCH",), architecture="aarch64", error="opaque")

    def test_fault_relation_does_not_reclassify_normal_termination_throw(self):
        source = """
union exception = { Error_ExceptionTaken : unit }
register D : bits(64)
val EndOfInstruction : unit -> unit
function EndOfInstruction() = throw(Error_ExceptionTaken(()))
val ROOT : unit -> unit
function ROOT() = { D = 0x0000000000000001; EndOfInstruction() }
"""
        text, deps = self.run_sail(
            source, roots=("ROOT",), architecture="aarch64")
        self.assertIn("= t", text)
        self.assertIn("Arm-normal-instruction-termination", deps)
        self.assertNotIn("Arm-fault-any-final-state", deps)

    def test_normal_termination_inside_loop_preserves_reached_state(self):
        text, deps = self.run_sail(
            FAULT_MODEL, roots=("NORMAL_STOP",), architecture="aarch64")
        self.assertIn("sail_hl_result_case", text)
        self.assertIn("= t", text)
        self.assertIn("Arm-normal-instruction-termination", deps)
        self.assertNotIn("Arm-fault-any-final-state", deps)

    def test_undefined_choice_is_existential_and_assertion_restricts_outcomes(self):
        text, deps = self.run_sail(
            FAULT_MODEL, roots=("UNKNOWN_CHOICE",), architecture="aarch64")
        self.assertRegex(text, r"\(\?\(v[0-9]+:sail_hl_type_Choice\)")
        self.assertIn("Sail-undefined-existential", deps)
        self.assertIn("guarded-assertion", deps)
        self.assertNotIn("sail_hl_shared_output_unknown", text)

    def test_dynamic_assertion_failure_admits_no_normal_state(self):
        text, deps = self.run_sail(
            FAULT_MODEL, roots=("GUARDED",), architecture="aarch64")
        self.assertRegex(text, r"(?s)if .* then .* else F")
        self.assertIn("guarded-assertion", deps)
        self.assertNotIn("Arm-fault-any-final-state", deps)

    def test_architectural_undefined_throw_is_not_generic_exception_mapping(self):
        text, deps = self.run_sail(
            FAULT_MODEL, roots=("UNDEFINED_FAULT",), architecture="aarch64")
        self.assertIn("Arm-undefined-fault-any-final-state", deps)
        self.assertIn("INL", text)
        self.assertIn("sail_hl_result_case", text)
        self.assertIn(". T)", text)
        self.run_sail(
            FAULT_MODEL.replace("throw(Error_Undefined())",
                                "throw(Error_ExceptionTaken())"),
            roots=("UNDEFINED_FAULT",), architecture="aarch64", error="throw")

    def test_fault_relation_keeps_normal_state_graph_without_faults(self):
        text, deps = self.run_sail(
            MODEL, roots=("ADD",))
        self.assertIn("\\(s:armstate) (t:armstate).", text)
        self.assertIn("= t", text)
        self.assertNotIn("Arm-fault-any-final-state", deps)

    def test_fault_relation_boundary_checks_original_signature(self):
        self.run_sail(
            """
register D : bits(64)
val AArch64_SPAlignmentFault = impure "fault" : unit -> bits(64)
val ROOT : unit -> unit
function ROOT() = { let ignored = AArch64_SPAlignmentFault(); D = ignored }
""", roots=("ROOT",), architecture="aarch64", error="requires unit -> unit")

    def test_real_plugin_and_helper_closure(self):
        text, deps = self.run_sail(MODEL)
        self.assertIn("word_add", text)
        self.assertIn("inlined add_value", deps)
        self.assertNotIn("primitive-contract add_value", deps)

    def test_rv32_frozen_pc_write_is_rejected(self):
        source = HEADER + """
register PC : bits(32)
register Result : bits(32)
val ROOT : unit -> unit
function ROOT() = {
    PC = 0x00000004;
    Result = PC
}
"""
        self.run_sail(source, roots=("ROOT",), architecture="rv32",
                      error="source current PC is read-only")

    def test_native_rv32_regidx_keeps_five_bit_register_arguments(self):
        source = HEADER + """
newtype regidx = Regidx : bits(5)
val rX_bits = impure "rX_bits" : regidx -> bits(32)
val wX_bits = impure "wX_bits" : (regidx, bits(32)) -> unit
val ROOT : (bits(5), bits(5)) -> unit
function ROOT(rd, rs) = wX_bits(Regidx(rd), rX_bits(Regidx(rs)))
"""
        text, deps = self.run_computation(source, architecture='rv32')
        self.assertIn("riscv_gpr", text)
        self.assertIn("5 word", text)
        self.assertNotIn("sail_hl_type_regidx", text)
        self.assertIn("primitive-contract rX_bits", deps)

    def test_native_rv32_regidx_wrong_payload_is_rejected(self):
        source = HEADER + """
newtype regidx = Regidx : bits(4)
val rX_bits = impure "rX_bits" : regidx -> bits(32)
register Result : bits(32)
val ROOT : bits(4) -> unit
function ROOT(rs) = Result = rX_bits(Regidx(rs))
"""
        self.run_computation(
            source,
            architecture='rv32',
            error='upstream RV32 regidx requires Regidx(bits(5))')

    def native_pstate_fixture(self, statement, flag_type="bits(1)"):
        return HEADER + """
struct ProcState = {
    N : """ + flag_type + """,
    Z : bits(1), C : bits(1), V : bits(1),
    D : bits(1), EL : bits(2), BTYPE : bits(2), nRW : bits(1),
    GE : bits(4)
}
register PSTATE : ProcState
register Result : bits(1)
val ROOT : unit -> unit
function ROOT() = {
""" + statement + "\n}\n"

    def test_native_pstate_flags_do_not_materialize_unobserved_fields(self):
        text, deps = self.run_computation(
            self.native_pstate_fixture('PSTATE.N = 0b1; Result = PSTATE.N'),
            architecture='aarch64')
        self.assertIn("write NF", text)
        self.assertIn("read NF", text)
        self.assertNotIn("reg_PSTATE", text)
        self.assertIn("primitive-contract PSTATE-NZCV-projection", deps)

    def test_native_pstate_unmapped_field_read_is_rejected(self):
        self.run_computation(
            self.native_pstate_fixture('Result = PSTATE.D'),
            architecture='aarch64',
            error='unsupported upstream PSTATE field D')

    def test_native_pstate_flag_type_change_is_rejected(self):
        self.run_computation(
            self.native_pstate_fixture('Result = PSTATE.N[0]', 'bits(2)'),
            architecture='aarch64',
            error='upstream PSTATE field has an incompatible type')

    def test_native_pstate_whole_record_read_is_rejected(self):
        self.run_computation(
            self.native_pstate_fixture('let snapshot = PSTATE; ()'),
            architecture='aarch64',
            error='whole upstream PSTATE reads are unsupported')

    def assumption_fixture(self, statement, extra=""):
        return HEADER + """
enum Feature = { FEAT_GCS, FEAT_AA64EL0, FEAT_PMULL, FEAT_AFP, FEAT_SME, Other }
val IsFeatureImplemented = pure "IsFeatureImplemented" : Feature -> bool
register FeatureImpl : bits(6)
struct ProcState = {
    N : bits(1), Z : bits(1), C : bits(1), V : bits(1),
    EL : bits(2), BTYPE : bits(2), nRW : bits(1), SM : bits(1)
}
register PSTATE : ProcState
register Result : bool
register Side : bits(1)
""" + extra + """
val ROOT : unit -> unit
function ROOT() = {
""" + statement + "\n}\n"

    def test_assumed_feature_selects_true_and_false_source_branches(self):
        source = self.assumption_fixture(
            "if IsFeatureImplemented(FEAT_PMULL) then Result = true else Result = false")
        for value, literal in (("true", "T"), ("false", "F")):
            with self.subTest(value=value):
                text, deps = self.run_computation(
                    source, architecture="aarch64",
                    features=("FEAT_PMULL=" + value,), with_sources=True)
                code = without_comments(text)
                self.assertIn("write reg_Result (" + literal + ":bool)", code)
                self.assertNotIn("if ", code)
                self.assertIn("Source assumptions: feature FEAT_PMULL=" + value, text)
                self.assertIn("used-assumption feature FEAT_PMULL=" + value, deps)

    def test_assumed_mode_preserves_flags_and_other_controls(self):
        source = self.assumption_fixture(
            "PSTATE.N = 0b1; assert(PSTATE.nRW == 0b0); "
            "assert(PSTATE.SM == 0b0); Result = PSTATE.N == 0b1")
        text, deps = self.run_computation(
            source, architecture="aarch64",
            initial_bits=("PSTATE.nRW=0", "PSTATE.SM=0"), with_sources=True)
        self.assertIn("write NF", without_comments(text))
        self.assertIn("read NF", without_comments(text))
        self.assertNotIn("reg_PSTATE", without_comments(text))
        self.assertIn("initial-bit PSTATE.SM=0b0", text)
        self.assertIn("statically-proved-assertion", deps)

    def test_initial_mode_only_skips_unreachable_feature_controls(self):
        source = self.assumption_fixture(
            "if IsFeatureImplemented(FEAT_SME) & PSTATE.SM == 0b1 & opaque() "
            "then Result = true else Result = Control",
            'register Control : bool\nval opaque = impure "opaque" : unit -> bool\n')
        text, deps = self.run_computation(
            source, architecture="aarch64", features=("FEAT_SME=true",),
            initial_bits=("PSTATE.SM=0",))
        self.assertIn("read reg_Control", text)
        self.assertNotIn("primitive-contract opaque", deps)
        self.run_computation(
            source, architecture="aarch64", features=("FEAT_SME=true",),
            initial_bits=("PSTATE.SM=1",), error="unsupported primitive opaque")

    def test_assumption_values_do_not_swallow_argument_effects(self):
        source = self.assumption_fixture(
            "Result = IsFeatureImplemented(selected())",
            "val selected : unit -> Feature\n"
            "function selected() = { Side = 0b1; FEAT_PMULL }\n")
        text, deps = self.run_computation(
            source, architecture="aarch64", features=("FEAT_PMULL=true",))
        self.assertIn("write reg_Side", text)
        self.assertIn("inlined selected", deps)
        self.assertIn("used-assumption feature FEAT_PMULL=true", deps)
        failed, failed_deps = self.run_computation(
            source.replace("Side = 0b1", "assert(false); Side = 0b1"),
            architecture="aarch64", features=("FEAT_PMULL=true",))
        self.assert_failed_relation(failed, failed_deps)
        self.assertNotIn("write reg_Result", failed)
        self.assertNotIn("used-assumption feature", failed_deps)

    def test_assumptions_do_not_replace_ordinary_helper_bodies(self):
        source = self.assumption_fixture(
            "Result = availability()",
            "val availability : unit -> bool\n"
            "function availability() = false\n")
        text, deps = self.run_computation(
            source, architecture="aarch64", features=("FEAT_PMULL=true",))
        self.assertNotIn("used-assumption", deps)
        self.assertIn("inlined availability", deps)
        self.assertIn("F", text)

    def test_unused_assumptions_are_recorded_but_do_not_restrict_definitions(self):
        text, deps = self.run_computation(
            self.assumption_fixture("Result = true"), architecture="aarch64",
            features=("FEAT_PMULL=true",), initial_bits=("PSTATE.SM=0",),
            with_sources=True)
        self.assertNotIn("Source assumptions:", text)
        self.assertNotIn("used-assumption", deps)
        self.assertIn("configured-assumption feature FEAT_PMULL=true", deps)
        self.assertIn("configured-assumption initial-bit PSTATE.SM=0b0", deps)

    def test_assumption_names_and_types_are_checked_even_when_unused(self):
        source = self.assumption_fixture("Result = true")
        for options, diagnostic in (
            ({"features": ("MISSING=true",)}, "not in Sail's Feature enum"),
            ({"initial_bits": ("MISSING.SM=0",)}, "requires a source register"),
            ({"initial_bits": ("PSTATE.MISSING=0",)}, "requires bits(1)"),
            ({"initial_bits": ("PSTATE.EL=0",)}, "requires bits(1)"),
            ({"features": ("FEAT_GCS=true",)}, "conflicts with the disabled GCS"),
        ):
            with self.subTest(options=options):
                self.run_computation(source, architecture="aarch64",
                                     error=diagnostic, **options)
        self.run_computation(
            source.replace('Feature -> bool', 'bits(6) -> bool'),
            architecture="aarch64", features=("FEAT_PMULL=true",),
            error="feature assumptions require Feature -> bool")
        self.run_computation(
            source.replace('Feature -> bool', 'Feature -> bool(true)'),
            architecture="aarch64", features=("FEAT_PMULL=false",),
            error="feature assumptions require Feature -> bool")
        self.run_computation(
            source.replace("SM : bits(1)", "SM : bool"),
            architecture="aarch64", initial_bits=("PSTATE.SM=0",),
            error="requires bits(1)")

    def test_duplicate_and_conflicting_assumptions_are_rejected(self):
        source = self.assumption_fixture("Result = true")
        for options in (
            {"features": ("FEAT_PMULL=true", "FEAT_PMULL=true")},
            {"features": ("FEAT_PMULL=true", "FEAT_PMULL=false")},
            {"initial_bits": ("PSTATE.SM=0", "PSTATE.SM=1")},
        ):
            with self.subTest(options=options):
                self.run_computation(source, architecture="aarch64",
                                     error="duplicate assumption", **options)
        self.run_computation(source, features=("FEAT_PMULL=true",),
                             error="require an Arm or x86 architecture")
        self.run_computation(source, architecture="rv32",
                             initial_bits=("PSTATE.SM=0",),
                             error="require an Arm or x86 architecture")

    def test_assumed_field_writes_are_rejected_before_or_after_reads(self):
        for statement in (
            "PSTATE.SM = 0b1; Result = PSTATE.SM == 0b1",
            "Result = PSTATE.SM == 0b0; PSTATE.SM = 0b1",
            "(PSTATE.SM, Side) = (0b1, 0b0)",
            "PSTATE = PSTATE",
        ):
            with self.subTest(statement=statement):
                self.run_computation(
                    self.assumption_fixture(statement), architecture="aarch64",
                    initial_bits=("PSTATE.SM=0",),
                    error="write may invalidate source assumption")
        source = self.assumption_fixture(
            "change(); Result = PSTATE.SM == 0b0",
            "val change : unit -> unit\nfunction change() = PSTATE.SM = 0b1\n")
        self.run_computation(source, architecture="aarch64",
                             initial_bits=("PSTATE.SM=0",),
                             error="write may invalidate source assumption")
        self.run_sail(
            self.assumption_fixture("PSTATE.SM = 0b1"),
            architecture="aarch64", initial_bits=("PSTATE.SM=0",),
            roots=("ROOT",), error="write may invalidate source assumption")

    def test_feature_storage_writes_and_skipped_field_writes(self):
        self.run_computation(
            self.assumption_fixture("FeatureImpl = 0b000000"),
            architecture="aarch64", features=("FEAT_PMULL=true",),
            error="write may invalidate source assumption")
        text, deps = self.run_computation(
            self.assumption_fixture(
                "if PSTATE.SM == 0b1 then PSTATE.SM = 0b1; Result = true"),
            architecture="aarch64", initial_bits=("PSTATE.SM=0",))
        self.assertNotIn("reg_PSTATE", text)
        self.assertIn("used-assumption initial-bit PSTATE.SM=0b0", deps)

    def test_shared_assumption_scope_survives_reused_helpers(self):
        source = self.assumption_fixture("Result = mode() | mode()", """
val mode : unit -> bool
function mode() = PSTATE.SM == 0b0
""")
        outputs = []
        for value in ("0", "1"):
            text, deps = self.run_computation(
                source, architecture="aarch64", initial_bits=("PSTATE.SM=" + value,),
                with_sources=True)
            self.assertIn("Source assumptions: initial-bit PSTATE.SM=0b" + value, text)
            self.assertIn("PSTATE.SM=0b" + value, deps)
            outputs.append(without_comments(text))
        self.assertNotEqual(outputs[0], outputs[1])

    def test_assumed_register_field_does_not_capture_another_record(self):
        source = self.assumption_fixture(
            "let local : ConfigType = struct { mode = 0b1, spare = 0b0 }; "
            "Result = local.mode == 0b1",
            "struct ConfigType = { mode : bits(1), spare : bits(1) }\n"
            "register Config : ConfigType\n")
        text, deps = self.run_computation(
            source, architecture="aarch64", initial_bits=("Config.mode=0",),
            with_sources=True)
        self.assertNotIn("Source assumptions:", text)
        self.assertNotIn("used-assumption", deps)
        self.assertIn("word 1", without_comments(text))
        self.run_computation(
            source.replace("let local :", "let Config :").replace("local.mode", "Config.mode"),
            architecture="aarch64", initial_bits=("Config.mode=0",),
            error="Cannot shadow register in pattern Config")

    def test_assumption_metadata_is_restored_for_cached_helper_in_next_root(self):
        source = self.assumption_fixture("Result = mode()", """
val mode : unit -> bool
function mode() = PSTATE.SM == 0b0
val SECOND : unit -> unit
function SECOND() = Result = mode()
""")
        text, _ = self.run_sail(
            source, roots=("ROOT", "SECOND"),
            architecture="aarch64", initial_bits=("PSTATE.SM=0",),
            with_sources=True)
        self.assertEqual(text.count("(* Source assumptions:"), 3)
        self.assertEqual(len(re.findall(
            r"let sail_hl_shared_\w+ = new_definition", text)), 1)

    def test_feature_assumptions_reject_backing_storage_bit_write(self):
        self.run_computation(
            self.assumption_fixture("FeatureImpl[0] = 0b0"),
            architecture="aarch64", features=("FEAT_PMULL=true",),
            error="write may invalidate source assumption")

    def test_native_rv32_rich_retirement_keeps_success_and_trap_distinct(self):
        source = HEADER + """
union ExceptionType = { E_Fetch_Addr_Align : unit, UnobservedCause : bits(8) }
struct ExceptionContext = {
    trap : ExceptionType, excinfo : bits(32), unobserved : bits(16)
}
union ExecutionResult = {
    Retire_Success : unit, Trap : (ExceptionContext, bits(32)),
    UnobservedResult : bits(256)
}
val exception_context = pure "exception_context" :
    (ExceptionType, bits(32)) -> ExceptionContext
val trap = pure "trap" : ExceptionContext -> ExecutionResult
val set_next_pc = impure "set_next_pc" : bits(32) -> unit
val ROOT : bits(32) -> ExecutionResult
function ROOT(target) = {
    if target[1] == 0b1 then
        return trap(exception_context(E_Fetch_Addr_Align(), target));
    set_next_pc(target);
    Retire_Success()
}
"""
        text, _ = self.run_sail(source, roots=("ROOT",), architecture="rv32",
                                normal_retirement=True)
        self.assertIn("sail_hl_ctor_Retire_5fSuccess", text)
        self.assertIn("sail_hl_ctor_Trap", text)
        self.assertIn("EventJump", text)
        self.assertIn("write PC", text)
        self.assertNotIn("256 word", text)
        self.assertNotIn("16 word", text)

    def flat_memory_source(self, operation="Load"):
        if operation == "Load":
            primitive = "vmem_read"
            arguments = "regidx, bits(32), int('width)"
            value_type = "bits(8 * 'width)"
            call = "Regidx(rs), offset, 4, Load(Data), false, false, false"
            body = "{ wX_bits(Regidx(rd), data); Retire_Success() }"
        else:
            primitive = "vmem_write"
            arguments = "regidx, bits(32), int('width), bits(8 * 'width)"
            value_type = "bool"
            call = "Regidx(rs), offset, 4, offset, Store(Data), false, false, false"
            body = "Retire_Success()"
        return HEADER + f"""
$include <result.sail>
newtype regidx = Regidx : bits(5)
enum mem_payload = {{ Data, OtherData }}
union MemoryAccessType('a : Type) = {{ Load : 'a, Store : 'a }}
union ExecutionResult = {{ Retire_Success : unit, Trap : bits(32) }}
val wX_bits = impure "wX_bits" : (regidx, bits(32)) -> unit
val {primitive} = impure "{primitive}" : forall 'width, 0 < 'width <= 8.
    ({arguments}, MemoryAccessType(mem_payload), bool, bool, bool)
    -> result({value_type}, ExecutionResult)
val ROOT : (bits(5), bits(5), bits(32)) -> ExecutionResult
function ROOT(rd, rs, offset) =
    match {primitive}({call}) {{
        Ok(data) => {body},
        Err(failure) => failure
    }}
"""

    def test_native_rv32_memory_retains_result_flow_and_load_event(self):
        source = self.flat_memory_source()
        text, deps = self.run_computation(source, architecture='rv32')
        self.assertIn("bytes32", text)
        self.assertIn("EventLoad", text)
        self.assertIn("sail_hl_result_case", text)
        self.assertIn("primitive-contract vmem_read", deps)
        self.assertIn("primitive-contract wX_bits", deps)
        self.assertNotIn("sail_hl_type_ExecutionResult", text)

    def test_flat_memory_uses_genuine_access_literals(self):
        for operation in ("Load", "Store"):
            with self.subTest(operation=operation):
                text, _ = self.run_computation(
                    self.flat_memory_source(operation), architecture="rv32")
                self.assertIn("Event" + operation, text)

    def test_flat_memory_accesses_one_two_or_four_bytes(self):
        for operation in ("Load", "Store"):
            for size in (1, 2):
                with self.subTest(operation=operation, size=size):
                    source = self.flat_memory_source(operation).replace(
                        "rd), data)", "rd), sail_zero_extend(data, 32))").replace(
                        "offset, 4, offset,", f"offset, {size}, offset[{8 * size - 1} .. 0],"
                    ).replace("offset, 4,", f"offset, {size},")
                    text, _ = self.run_computation(source, architecture="rv32")
                    self.assertIn(f"bytes{8 * size}", text)
                    self.assertRegex(text, rf"Event{operation} \(\w+,{size}\)")
        self.run_computation(self.flat_memory_source().replace(
            "rd), data)", "rd), data[31 .. 0])").replace("offset, 4,", "offset, 8,"),
            architecture="rv32", error="only 1-, 2- and 4-byte flat accesses are supported")

    def assert_flat_memory_refusal(self, change):
        for operation in ("Load", "Store"):
            with self.subTest(operation=operation):
                source = change(self.flat_memory_source(operation), operation)
                self.run_computation(source, architecture="rv32",
                                     error="flat access requires the genuine")

    def test_flat_memory_cannot_skip_an_effectful_access_helper(self):
        def change(source, operation):
            source = source.replace(operation + " : 'a", "Other" + operation + " : unit")
            helper = f"""
register Dummy : bool
val {operation} : mem_payload -> MemoryAccessType(mem_payload)
function {operation}(kind) = {{ Dummy = false; Other{operation}() }}
"""
            return source.replace("val wX_bits", helper + "\nval wX_bits")
        self.assert_flat_memory_refusal(change)

    def test_flat_memory_cannot_replace_a_data_register_by_an_enum(self):
        self.assert_flat_memory_refusal(lambda source, operation: source.replace(
            "val ROOT :", "register Data : mem_payload\nval ROOT :"))

    def test_flat_memory_requires_the_mem_payload_enum(self):
        self.assert_flat_memory_refusal(lambda source, operation: source.replace(
            "enum mem_payload = { Data, OtherData }",
            "enum mem_payload = { OtherData }\nenum other_payload = { Data }"
        ).replace("MemoryAccessType(mem_payload)", "MemoryAccessType(other_payload)"))

    def test_flat_memory_requires_the_memory_access_union(self):
        self.assert_flat_memory_refusal(lambda source, operation: source.replace(
            "MemoryAccessType", "OtherAccessType"))

    def test_native_rv32_state_export_cannot_drop_a_failure_result(self):
        source = HEADER + """
union ExecutionResult = { Retire_Success : unit, Trap : bits(32) }
register Result : bool
val ROOT : unit -> ExecutionResult
function ROOT() = { Result = true; Trap(0x00000004) }
"""
        self.run_computation(
            source,
            architecture='rv32',
            error='unsupported primitive Trap')

    def test_native_rv32_payload_equality_is_rejected(self):
        source = HEADER + """
union ExecutionResult = { Retire_Success : unit, Trap : bits(32) }
val eq_any = pure "eq_any" : forall ('a : Type). ('a, 'a) -> bool
register Result : bool
val ROOT : unit -> ExecutionResult
function ROOT() = {
    Result = eq_any(Retire_Success(), Retire_Success());
    Retire_Success()
}
"""
        self.run_sail(source, roots=("ROOT",), architecture="rv32",
                      normal_retirement=True,
                      error="equality cannot observe omitted upstream payloads")

    def test_native_rv32_wrapper_record_payload_equality_is_rejected(self):
        source = HEADER + """
union ExecutionResult = { Retire_Success : unit, Trap : bits(32) }
struct wrapper = { result : ExecutionResult, marker : bits(8) }
val eq_any = pure "eq_any" : forall ('a : Type). ('a, 'a) -> bool
register Result : bool
val ROOT : (wrapper, wrapper) -> ExecutionResult
function ROOT(left, right) = {
    Result = eq_any(left, right);
    Retire_Success()
}
"""
        self.run_sail(source, roots=("ROOT",), architecture="rv32",
                      normal_retirement=True,
                      error="equality cannot observe omitted upstream payloads")

    def test_native_rv32_trap_contexts_keep_cause_and_field_effects(self):
        # As ECALL and EBREAK build them: a retirement relation keeps the
        # cause's constructor and evaluates every field, also the dropped
        # ones; a state computation cannot build either value.
        source = HEADER + """
enum breakpoint_cause = { Brk_Software, Brk_Hardware }
enum Privilege = { User, Machine }
union ExceptionType = {
    E_Breakpoint : breakpoint_cause, E_U_EnvCall : unit, E_M_EnvCall : unit
}
struct ExceptionContext = {
    trap : ExceptionType, excinfo : bits(32), unobserved : bits(16)
}
union ExecutionResult = { Retire_Success : unit, Trap : ExceptionContext }
val exception_context = pure "exception_context" :
    (ExceptionType, bits(32)) -> ExceptionContext
val trap = pure "trap" : ExceptionContext -> ExecutionResult
register PC : bits(32)
register cur_privilege : Privilege
register Result : bool
val unobserved : unit -> bits(16)
function unobserved() = { Result = true; 0x0000 }
val EBREAK : unit -> ExecutionResult
function EBREAK() = trap(exception_context(E_Breakpoint(Brk_Software), PC))
val ECALL : unit -> ExecutionResult
function ECALL() = {
    let cause : ExceptionType = match cur_privilege {
        User => E_U_EnvCall(), Machine => E_M_EnvCall()
    };
    trap(struct {trap = cause, excinfo = 0x00000000, unobserved = unobserved()})
}
val BUILD : unit -> ExecutionResult
function BUILD() = {
    let c : ExceptionContext = struct {
        trap = E_U_EnvCall(), excinfo = 0x00000000, unobserved = 0x0000
    };
    Retire_Success()
}
val CAUSE : unit -> ExecutionResult
function CAUSE() = {
    let cause : ExceptionType = E_Breakpoint(Brk_Software);
    Retire_Success()
}
"""
        text, _ = self.run_sail(source, roots=("EBREAK", "ECALL"),
                                architecture="rv32", normal_retirement=True)
        self.assertIn("sail_hl_ctor_E_5fBreakpoint", text)
        self.assertIn("(reg_cur_5fprivilege:(riscvstate,sail_hl_type_Privilege)component)",
                      text)
        self.assertIn("write reg_Result", text)
        self.run_sail(source, roots=("BUILD",), architecture="rv32",
                      error="projected upstream records require an explicit construction contract")
        self.run_sail(source, roots=("CAUSE",), architecture="rv32",
                      error="unit variant constructor requires the singleton unit payload")

    def test_native_rv32_fence_hooks_change_no_state(self):
        source = HEADER + """
enum barrier_kind = { Barrier_RISCV_rw_rw, Barrier_RISCV_r_r }
enum Event = { EV_FENCE }
union ExecutionResult = { Retire_Success : unit, Trap : bits(32) }
val sail_barrier = impure "barrier" : barrier_kind -> unit
val generate_event = impure "event" : Event -> unit
val is_fiom_active = impure "fiom" : unit -> bool
val ROOT : (bits(2), bits(2)) -> ExecutionResult
function ROOT(pred, succ) = {
    let pred = if is_fiom_active() then pred | succ else pred;
    match (pred, succ) {
        (0b11, 0b11) => sail_barrier(Barrier_RISCV_rw_rw),
        (0b10, _) => sail_barrier(Barrier_RISCV_r_r),
        (_, 0b00) => (),
        (_, _) => ()
    };
    generate_event(EV_FENCE);
    Retire_Success()
}
"""
        text, deps = self.run_computation(source, architecture="rv32")
        self.assertIn("(reg_is_5ffiom_5factive:(riscvstate,bool)component)", text)
        self.assertRegex(text, r"= \(\(word 3\):2 word\)\) /\\ \(\(\w+:2 word\) = "
                         r"\(\(word 3\):2 word\)\)")
        self.assertNotIn("(write ", text)
        for name in ("sail_barrier", "generate_event", "is_fiom_active"):
            self.assertIn("primitive-contract " + name, deps)
        self.run_computation(source.replace("        (_, _) => ()\n", "").replace(
            "(_, 0b00) => (),", "(_, 0b00) => ()"), architecture="rv32",
            error="tuple bit match must cover every possible value")
        self.run_computation(source.replace("Event -> unit", "bits(2) -> unit").replace(
            "EV_FENCE)", "0b00)"), architecture="rv32",
            error="generate_event requires Event -> unit")

    def test_native_rv32_division_rounds_toward_zero(self):
        # HOL's div and rem are Euclidean. Negating a negative dividend and
        # the result rounds toward zero for either sign of the divisor; a
        # zero divisor must be excluded, as DIV and REM do.
        source = HEADER + """
val quot_round_zero = pure "tdiv_int" : forall 'm, 'm != 0. (int, int('m)) -> int
val rem_round_zero = pure "tmod_int" : forall 'm, 'm != 0. (int, int('m)) -> int
register Q : bits(32)
register R : bits(32)
val ROOT : (bits(32), bits(32)) -> unit
function ROOT(x, y) = {
    let a = signed(x);
    let b = signed(y);
    Q = get_slice_int(32, if b == 0 then -1 else quot_round_zero(a, b), 0);
    R = get_slice_int(32, if b == 0 then a else rem_round_zero(a, b), 0)
}
"""
        text, deps = self.run_computation(source, architecture="rv32")
        for operation in ("div", "rem"):
            self.assertRegex(text, r"\(if \(\((\w+):int\) < \(& 0\)\) then "
                             r"\(-- \(\(-- \(\1:int\)\) " + operation +
                             r" \((\w+):int\)\)\) else \(\(\1:int\) " + operation +
                             r" \(\2:int\)\)\)")
        self.assertIn("(iword (((-- (& 1)):int):int))", text)
        self.assertIn("primitive-contract quot_round_zero", deps)
        self.run_computation(source.replace("forall 'm, 'm != 0. (int, int('m))", "(int, int)")
                             .replace("if b == 0 then -1 else ", ""), architecture="rv32",
                             error="division toward zero requires a proved nonzero divisor")

    def native_batch_fixture(self, control_statement="()"):
        # Deliberately small synthetic callees test catalog checking and
        # publishing. These are not copies of architecture instruction bodies.
        return HEADER + """
newtype regidx = Regidx : bits(5)
enum rop = { ADD, SUB }
enum bop = { BNE, BEQ }
union ExecutionResult = { Retire_Success : unit, Trap : bits(32) }
register Dummy : bool
val opaque = impure "opaque" : unit -> unit
val execute_RTYPE : (regidx, regidx, regidx, rop) -> ExecutionResult
function execute_RTYPE(rs2, rs1, rd, op) = { Dummy = true; Retire_Success() }
val execute_BTYPE : (bits(13), regidx, regidx, bop) -> ExecutionResult
function execute_BTYPE(imm, rs2, rs1, op) = {
    Dummy = true;
""" + control_statement + """;
    Retire_Success()
}
"""

    def test_native_batch_keeps_canonical_filenames_and_independent_types(self):
        models, inventory = self.run_sail(
            self.native_batch_fixture(), roots=("rv_RTYPE_ADD", "rv_BTYPE_BNE"),
            architecture="rv32", output_dir=True)
        self.assertEqual(set(models), {"rv32.ml", "rv32-control.ml"})
        self.assertEqual(inventory["schema"], 1)
        self.assertEqual(inventory["architecture"], "rv32")
        core = inventory["outputs"]["rv32.ml"]
        control = inventory["outputs"]["rv32-control.ml"]
        self.assertEqual(core["roots"], ["rv_RTYPE_ADD"])
        self.assertEqual(core["modes"], {"rv_RTYPE_ADD": "state-computation"})
        self.assertEqual(control["modes"], {"rv_BTYPE_BNE": "normal-retirement"})
        self.assertFalse(set(core["types"]) & set(control["types"]))
        self.assertIn("sail_hl_rv_5fRTYPE_5fADD", models["rv32.ml"])
        self.assertIn("sail_hl_rv_5fBTYPE_5fBNE", models["rv32-control.ml"])
        self.assertIn("successful-root-jump-event", control["contracts"])

    def test_native_rv32_entry_without_effects_is_a_relation(self):
        source = self.native_batch_fixture() + """
val execute_PAUSE : unit -> ExecutionResult
function execute_PAUSE() = Retire_Success()
"""
        models, inventory = self.run_sail(source, roots=("rv_PAUSE",),
                                          architecture="rv32", output_dir=True)
        self.assertEqual(inventory["outputs"]["rv32.ml"]["modes"],
                         {"rv_PAUSE": "state-computation"})
        self.assertRegex(models["rv32.ml"], r"`sail_hl_rv_5fPAUSE  =\n +"
                         r"\\\(s:riscvstate\) \(t:riscvstate\)\.")

    def test_native_batch_failure_does_not_publish_an_earlier_family(self):
        self.run_sail(
            self.native_batch_fixture("opaque()"),
            roots=("rv_RTYPE_ADD", "rv_BTYPE_BNE"),
            architecture="rv32", output_dir=True,
            error="unsupported primitive opaque")

    def test_forked_batch_workers_publish_the_sequential_files(self):
        # Workers translate families from the same prepared compiler state;
        # the parent publishes their artifacts, so the files are unchanged.
        roots = ("rv_RTYPE_ADD", "rv_BTYPE_BNE")
        sequential = self.run_sail(self.native_batch_fixture(), roots=roots,
                                   architecture="rv32", output_dir=True)
        for jobs in (1, 2, 3):
            with self.subTest(jobs=jobs):
                self.assertEqual(
                    self.run_sail(self.native_batch_fixture(), roots=roots,
                                  architecture="rv32", output_dir=True, jobs=jobs),
                    sequential)

    def test_forked_batch_failure_publishes_no_family(self):
        # The control family fails in its worker; the core family's worker
        # succeeds, but nothing is published and the worker's error is shown.
        self.run_sail(
            self.native_batch_fixture("opaque()"),
            roots=("rv_RTYPE_ADD", "rv_BTYPE_BNE"),
            architecture="rv32", output_dir=True, jobs=2,
            error="unsupported primitive opaque")

    def test_job_count_must_be_positive(self):
        self.run_sail(self.native_batch_fixture(), roots=("rv_RTYPE_ADD",),
                      architecture="rv32", output_dir=True, jobs=0,
                      error="expected a positive job count")

    def test_helper_does_not_inherit_unrelated_later_platform_constraints(self):
        source = HEADER + """
val checked : forall 'N, 'N >= 0. bits('N) -> bits('N)
function checked(value) = { assert(constraint('N > 0)); value }
type unrelated_width : Int = config unused.width
constraint 0 < unrelated_width < 64
register Result : bits(32)
val ROOT : bits(32) -> unit
function ROOT(value) = Result = checked(value)
"""
        text, deps = self.run_computation(source, architecture='rv32')
        self.assertIn("32 word", text)
        self.assertIn("inlined checked", deps)
        self.assertNotIn("unrelated_width", text)

    def computation_fixture(self, helper, expression):
        return HEADER + """
val X_set = impure "flat_X_set" : forall 'r,
  0 <= 'r & 'r <= 31. (int('r), int(64), bits(64)) -> unit
""" + helper + """
val ROOT : (bits(5), bits(64)) -> unit
function ROOT(d, x) = {
    let 'r = unsigned(d);
    X_set(r, 64, """ + expression + ")\n}\n"

    @staticmethod
    def setter_fixture(setter, width, helpers, arguments, after=""):
        return HEADER + f"""
register Selector : bits(5)
register Side : bits(1)
val {setter} = impure "flat_{setter}" : forall 'r,
    0 <= 'r & 'r <= 31. (int('r), int({width}), bits({width})) -> unit
{helpers}
val ROOT : bits({width}) -> unit
function ROOT(x) = {{ {setter}({arguments}); {after} }}
"""

    def test_register_setter_captures_index_before_value_changes_state(self):
        for setter, width in (("X_set", 64), ("V_set", 128)):
            with self.subTest(setter=setter):
                source = self.setter_fixture(setter, width, f"""
val changed : bits({width}) -> bits({width})
function changed(x) = {{ Selector = 0b00001; x }}
""", "unsigned(Selector), " + str(width) + ", changed(x)")
                text, deps = self.run_computation(source)
                root = text.split("let sail_hl_ROOT = new_definition", 1)[1]
                self.assertIn("read reg_Selector s", root)
                read = root.index("read reg_Selector s")
                call = root.index(self.shared_name(text, "changed"))
                self.assertLess(read, call)
                self.assertEqual(root.count("read reg_Selector"), 1)
                self.assertIn("write reg_Selector", text)
                self.assertIn("primitive-contract " + setter, deps)

    def test_register_setter_keeps_width_effects_in_argument_order(self):
        for setter, width in (("X_set", 64), ("V_set", 128)):
            with self.subTest(setter=setter):
                source = self.setter_fixture(setter, width, f"""
val width : unit -> int({width})
function width() = {{ Side = 0b1; {width} }}
val changed : bits({width}) -> bits({width})
function changed(x) = {{ Selector = 0b00001; x }}
""", "unsigned(Selector), width(), changed(x)")
                text, deps = self.run_computation(source)
                root = text.split("let sail_hl_ROOT = new_definition", 1)[1]
                read = root.index("read reg_Selector s")
                width_call = root.index(self.shared_name(text, "width"))
                value_call = root.index(self.shared_name(text, "changed"))
                self.assertLess(read, width_call)
                self.assertLess(width_call, value_call)
                self.assertIn("write reg_Side", text)
                self.assertIn("inlined width", deps)

    def test_register_setter_does_not_skip_typed_width_assertions_or_calls(self):
        for setter, width in (("X_set", 64), ("V_set", 128)):
            with self.subTest(setter=setter):
                source = self.setter_fixture(
                    setter, width,
                    f"val width : unit -> int({width})\n"
                    f"function width() = {{ assert(false); {width} }}",
                    "0, width(), x")
                text, deps = self.run_computation(source)
                self.assert_failed_relation(text, deps)
                self.assertNotIn("primitive-contract " + setter, deps)
                self.assertNotIn("write (XREG", text)
                self.assertNotIn("write (QREG", text)
                source = self.setter_fixture(
                    setter, width,
                    f'val width = impure "opaque" : unit -> int({width})',
                    "0, width(), x")
                self.run_computation(source, error="unsupported primitive width")

    def test_register_setter_argument_returns_skip_the_setter_and_later_code(self):
        for setter, width in (("X_set", 64), ("V_set", 128)):
            arguments = ["0", str(width), "x"]
            for position in range(3):
                with self.subTest(setter=setter, argument=position):
                    actual = arguments.copy()
                    actual[position] = (
                        "{ Side = 0b1; return(()); " + actual[position] + " }")
                    source = self.setter_fixture(
                        setter, width, "", ", ".join(actual), "Side = 0b0")
                    text, deps = self.run_computation(source)
                    self.assertEqual(text.count("write reg_Side"), 1)
                    self.assertIn("word 1", text)
                    self.assertNotIn("primitive-contract " + setter, deps)
                    self.assertNotIn("write (XREG", text)
                    self.assertNotIn("write (QREG", text)

    def test_register_setter_width_helper_return_resumes_its_caller(self):
        for setter, width in (("X_set", 64), ("V_set", 128)):
            with self.subTest(setter=setter):
                source = self.setter_fixture(setter, width, f"""
val width : unit -> int({width})
function width() = {{ Side = 0b1; return({width}); Side = 0b0; {width} }}
""", "0, width(), x")
                text, deps = self.run_computation(source)
                self.assertEqual(text.count("write reg_Side"), 1)
                self.assertIn("primitive-contract " + setter, deps)
                self.assertIn("write (" + ("XREG" if setter == "X_set" else "QREG"),
                              text)

    def test_specialized_pure_assertion_block_is_checked(self):
        source = self.computation_fixture("""
val checked : forall 'N, 'N >= 0. bits('N) -> bits('N)
function checked(x) = { assert(constraint('N > 0)); x }
""", "x + checked(x)")
        text, deps = self.run_computation(source)
        self.assertIn("word_add", text)
        self.assertIn("statically-proved-assertion", deps)
        self.assertIn("inlined checked", deps)

    def test_proved_assertion_does_not_discard_unknown_condition(self):
        source = self.computation_fixture("""
val opaque = impure "opaque" : unit -> bool(true)
val checked : bits(64) -> bits(64)
function checked(x) = { assert(opaque()); x }
""", "checked(x)")
        self.run_computation(source, error='unsupported primitive opaque')

    def test_proved_assertion_retains_condition_helper_write(self):
        source = self.computation_fixture("""
val touched : bits(64) -> bool(true)
function touched(x) = { X_set(0,64,x); true }
val checked : bits(64) -> bits(64)
function checked(x) = { assert(touched(x)); x }
""", "checked(x)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined touched", deps)

    def test_plain_boolean_assertion_keeps_effects_and_guards_unknown_truth(self):
        source = self.computation_fixture("""
val touched : bits(64) -> bool
function touched(x) = { X_set(0,64,x); true }
val checked : bits(64) -> bits(64)
function checked(x) = { assert(touched(x)); x }
""", "checked(x)")
        for condition in ("true", "false", "unsigned(x) == 0"):
            with self.subTest(condition=condition):
                text, deps = self.run_computation(
                    source.replace('X_set(0,64,x); true',
                                   'X_set(0,64,x); ' + condition))
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertIn("inlined touched", deps)
                if condition == "true":
                    self.assertIn("statically-proved-assertion", deps)
                else:
                    self.assert_guarded_relation(text, deps, "touched(x)")
                    self.assertNotIn("statically-proved-assertion", deps)
                    self.assertIn("F" if condition == "false" else "val", text)

    def test_plain_boolean_true_pure_helper_retains_its_body(self):
        source = self.computation_fixture("""
val checked : bits(64) -> bool
function checked(x) = { let unused = x + x; true }
val retained : bits(64) -> bits(64)
function retained(x) = { assert(checked(x)); x }
""", "retained(x)")
        text, deps = self.run_computation(source)
        self.assertIn("word_add", text)
        self.assertIn("inlined checked", deps)

    def test_plain_assertion_does_not_skip_unknown_condition(self):
        source = self.computation_fixture("""
val opaque = impure "opaque" : bits(64) -> bool
val checked : bits(64) -> bits(64)
function checked(x) = { assert(opaque(x)); x }
""", "checked(x)")
        self.run_computation(source, error='unsupported primitive opaque')

    def test_partial_boolean_truth_skips_short_circuited_argument_effects(self):
        source = self.computation_fixture("""
val touched : bits(64) -> bool
function touched(x) = { X_set(0,64,x); unsigned(x) == 0 }
val checked : bits(64) -> bits(64)
function checked(x) = {
    if false & touched(x) then { assert(false); () };
    if true | touched(x) then return(x) else { assert(false); return(x) }
}
""", "checked(x)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 1)
        self.assertNotIn("inlined touched", deps)

    def test_partial_boolean_truth_skips_short_circuited_unknown_argument(self):
        source = self.computation_fixture("""
val opaque = impure "opaque" : bits(64) -> bool
val checked : bits(64) -> bits(64)
function checked(x) = { if false & opaque(x) then return(x); return(x) }
""", "checked(x)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 1)
        self.assertNotIn("primitive-contract opaque", deps)

    def boolean_computation_fixture(self, expression, helper="", after=""):
        """Keep Boolean effects inside a value helper and its return scope."""
        return self.computation_fixture(helper + """
val checked : bits(64) -> bits(64)
function checked(x) = {
    let ignored = """ + expression + ";\n" + after + """
    x
}
""", "checked(x)")

    def constant_register_write_positions(self, text, index):
        """Find a literal register index without depending on type wrappers."""
        return [match.start() for match in re.finditer(
            r"write \(XREG \(num_of_int \(+& " + str(index) + r"\b", text)]

    def shared_name(self, text, source):
        """Find the one source worker used by a sequencing fixture."""
        encoded = source.replace("_", "_5f")
        names = re.findall(
            rf"let (sail_hl_shared_\w+_{encoded}_5f\d+) = new_definition", text)
        self.assertEqual(len(names), 1, text)
        return names[0]

    def shared_call_positions(self, text, source):
        name = self.shared_name(text, source)
        # Parenthesized applications exclude the definition's left-hand side
        # and REWRITE_RULE's theorem list. Count calls, not just worker bodies.
        return [match.start() for match in re.finditer(
            r"\(" + re.escape(name) + r"\s", text)]

    def shared_result(self, text, source):
        """Return the value/state names and arguments at a captured call."""
        name = self.shared_name(text, source)
        calls = re.findall(
            r"let \((v\d+),(v\d+)\) = \(let [^\n]+ in\n\s+\(" +
            re.escape(name) + r"\b([^\n]+)\)\) in", text)
        self.assertEqual(len(calls), 1, text)
        return calls[0]

    def test_literal_boolean_short_circuit_keeps_only_live_rhs_register_write(self):
        helper = """
val touched : bits(64) -> bool
function touched(x) = { X_set(1,64,x); true }
"""
        for live, expressions in (
                (False, ("false & touched(x)", "true | touched(x)",
                         "and_bool(false,touched(x))", "or_bool(true,touched(x))")),
                (True, ("true & touched(x)", "false | touched(x)",
                        "and_bool(true,touched(x))", "or_bool(false,touched(x))"))):
            for expression in expressions:
                with self.subTest(expression=expression):
                    text, deps = self.run_computation(
                        self.boolean_computation_fixture(expression, helper))
                    self.assertEqual(text.count("write (XREG"), 1 + int(live))
                    if live:
                        self.assertIn("inlined touched", deps)
                    else:
                        self.assertNotIn("inlined touched", deps)

    def test_boolean_short_circuit_skips_only_unreachable_unsupported_rhs(self):
        helper = 'val opaque = impure "opaque" : bits(64) -> bool\n'
        for skipped, live in (("false & opaque(x)", "true & opaque(x)"),
                              ("true | opaque(x)", "false | opaque(x)")):
            with self.subTest(skipped=skipped):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(skipped, helper))
                self.assertEqual(text.count("write (XREG"), 1)
                self.assertNotIn("primitive-contract opaque", deps)
                self.run_computation(
                    self.boolean_computation_fixture(live, helper),
                    error='unsupported primitive opaque')

    def test_boolean_short_circuit_skips_only_unreachable_failing_assertion(self):
        for skipped, live in (
                ("false & ({ assert(false); true })",
                 "true & ({ assert(false); true })"),
                ("true | ({ assert(false); false })",
                 "false | ({ assert(false); false })")):
            with self.subTest(skipped=skipped):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(skipped))
                self.assertEqual(text.count("write (XREG"), 1)
                self.assertNotIn("statically-proved-assertion", deps)
                failed, failed_deps = self.run_computation(
                    self.boolean_computation_fixture(live))
                self.assert_failed_relation(failed, failed_deps)
                self.assertNotIn("write (XREG", failed)

    def test_boolean_short_circuit_skips_unreachable_throw(self):
        helper = "union exception = { Rejected : unit }\n"
        for expression in ("false & (throw(Rejected(())))",
                           "true | (throw(Rejected(())))"):
            with self.subTest(expression=expression):
                text, _ = self.run_computation(
                    self.boolean_computation_fixture(expression, helper))
                self.assertEqual(text.count("write (XREG"), 1)

    def test_boolean_short_circuit_retains_live_throw_refusal(self):
        helper = "union exception = { Rejected : unit }\n"
        for expression in ("true & (throw(Rejected(())))",
                           "false | (throw(Rejected(())))"):
            with self.subTest(expression=expression):
                self.run_computation(
                    self.boolean_computation_fixture(expression, helper),
                    error='unsupported pure AST node')

    def test_boolean_short_circuit_skips_rhs_early_return(self):
        for expression in ("false & ({ return(x + x); true })",
                           "true | ({ return(x + x); false })"):
            with self.subTest(expression=expression):
                text, _ = self.run_computation(
                    self.boolean_computation_fixture(
                        expression, after="X_set(1,64,x);\n"))
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertNotIn("word_add", text)

    def test_boolean_short_circuit_keeps_rhs_early_return_scope(self):
        for expression in (
                "true & ({ X_set(0,64,x); return(x + x); true })",
                "false | ({ X_set(0,64,x); return(x + x); false })"):
            with self.subTest(expression=expression):
                text, _ = self.run_computation(
                    self.boolean_computation_fixture(
                        expression, after="X_set(1,64,x);\n"))
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertIn("word_add", text)
                self.assertFalse(self.constant_register_write_positions(text, 1))

    def test_boolean_short_circuit_callee_return_does_not_exit_its_caller(self):
        helper = """
val returned : bits(64) -> bool
function returned(x) = {
    X_set(0,64,x);
    return(false);
    X_set(2,64,x);
    true
}
"""
        for expression in ("true & returned(x)", "false | returned(x)"):
            with self.subTest(expression=expression):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(
                        expression, helper, after="X_set(1,64,x);\n"))
                self.assertEqual(text.count("write (XREG"), 3)
                self.assertIn("inlined returned", deps)
                self.assertFalse(self.constant_register_write_positions(text, 2))

    def test_boolean_short_circuit_preserves_boolean_result(self):
        for operator in ("&", "|"):
            for first in (False, True):
                for second in (False, True):
                    with self.subTest(operator=operator, first=first,
                                      second=second):
                        left = str(first).lower()
                        right = str(second).lower()
                        helper = f"""
val touched : bits(64) -> bool
function touched(x) = {{ X_set(0,64,x); {right} }}
"""
                        source = self.computation_fixture(helper + f"""
val checked : bits(64) -> bits(64)
function checked(x) = {{
    let flag = {left} {operator} touched(x);
    if flag then X_set(1,64,x) else X_set(2,64,x);
    x
}}
""", "checked(x)")
                        text, _ = self.run_computation(source)
                        live = first if operator == "&" else not first
                        expected = first and second if operator == "&" else first or second
                        self.assertEqual(text.count("write (XREG"), 3 if live else 2)
                        self.assertEqual(len(self.constant_register_write_positions(
                            text, 0)), int(live))
                        self.assertEqual(len(self.constant_register_write_positions(
                            text, 1)), int(expected))
                        self.assertEqual(len(self.constant_register_write_positions(
                            text, 2)), int(not expected))

    def test_boolean_short_circuit_preserves_mutable_local_updates(self):
        for expression, live in (
                ("false & ({ flag = true; true })", False),
                ("true | ({ flag = true; true })", False),
                ("true & ({ flag = true; true })", True),
                ("false | ({ flag = true; true })", True)):
            with self.subTest(expression=expression):
                source = self.computation_fixture("""
val checked : bits(64) -> bits(64)
function checked(x) = {
    flag : bool = false;
    let ignored = """ + expression + """;
    if flag then X_set(1,64,x) else X_set(2,64,x);
    x
}
""", "checked(x)")
                text, _ = self.run_computation(source)
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertEqual(len(self.constant_register_write_positions(
                    text, 1)), int(live))
                self.assertEqual(len(self.constant_register_write_positions(
                    text, 2)), int(not live))

    def test_symbolic_boolean_short_circuit_guards_rhs_register_write(self):
        helper = """
val touched : bits(64) -> bool
function touched(x) = { X_set(1,64,x); true }
"""
        for expression in ("(unsigned(x) == 0) & touched(x)",
                           "(unsigned(x) == 0) | touched(x)"):
            with self.subTest(expression=expression):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(expression, helper))
                self.assertIn("if ", text)
                self.assertIn("inlined touched", deps)
                # The write must occur inside the conditional, rather than
                # before the branch as it would under eager evaluation.
                calls = self.shared_call_positions(text, "touched")
                self.assertEqual(len(calls), 1)
                self.assertLess(text.index("if "), calls[0])
                self.assertEqual(len(self.constant_register_write_positions(
                    text, 1)), 1)

    def test_symbolic_boolean_short_circuit_refuses_reachable_unknown_rhs(self):
        helper = 'val opaque = impure "opaque" : bits(64) -> bool\n'
        for expression in ("(unsigned(x) == 0) & opaque(x)",
                           "(unsigned(x) == 0) | opaque(x)"):
            with self.subTest(expression=expression):
                self.run_computation(
                    self.boolean_computation_fixture(expression, helper),
                    error='unsupported primitive opaque')

    def test_nested_boolean_short_circuit_keeps_only_reachable_effects(self):
        helper = """
val touched : bits(64) -> bool
function touched(x) = { X_set(1,64,x); true }
val opaque = impure "opaque" : bits(64) -> bool
"""
        for expression in (
                "false & (touched(x) | opaque(x))",
                "true | (touched(x) & opaque(x))",
                "(false & opaque(x)) | touched(x)",
                "(true | opaque(x)) & touched(x)"):
            with self.subTest(expression=expression):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(expression, helper))
                live = expression.startswith("(")
                self.assertEqual(text.count("write (XREG"), 2 if live else 1)
                self.assertEqual("inlined touched" in deps, live)
                self.assertNotIn("primitive-contract opaque", deps)

    def test_boolean_short_circuit_evaluates_effectful_lhs_once(self):
        helper = """
val left : bits(64) -> bool
function left(x) = { X_set(0,64,x); false }
val right : bits(64) -> bool
function right(x) = { X_set(1,64,x); true }
"""
        for expression, live in (("left(x) & right(x)", False),
                                  ("left(x) | right(x)", True)):
            with self.subTest(expression=expression):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(expression, helper))
                self.assertEqual(text.count("write (XREG"), 3 if live else 2)
                left = self.constant_register_write_positions(text, 0)
                self.assertEqual(len(left), 1)
                self.assertEqual("inlined right" in deps, live)
                if live:
                    right = self.constant_register_write_positions(text, 1)
                    self.assertEqual(len(right), 1)
                    self.assertLess(left[0], right[0])

    def test_boolean_short_circuit_symbolic_effectful_lhs_is_not_duplicated(self):
        helper = """
val left : bits(64) -> bool
function left(x) = { X_set(0,64,x); unsigned(x) == 0 }
val right : bits(64) -> bool
function right(x) = { X_set(1,64,x); true }
"""
        for expression in ("left(x) & right(x)", "left(x) | right(x)"):
            with self.subTest(expression=expression):
                text, _ = self.run_computation(
                    self.boolean_computation_fixture(expression, helper))
                left = self.constant_register_write_positions(text, 0)
                right = self.constant_register_write_positions(text, 1)
                self.assertEqual(len(left), 1)
                self.assertEqual(len(right), 1)
                left_calls = self.shared_call_positions(text, "left")
                right_calls = self.shared_call_positions(text, "right")
                self.assertEqual(len(left_calls), 1)
                self.assertEqual(len(right_calls), 1)
                self.assertLess(left_calls[0], text.index("if "))
                self.assertLess(text.index("if "), right_calls[0])

    def test_boolean_short_circuit_lhs_return_skips_rhs_and_continuation(self):
        helper = """
val touched : bits(64) -> bool
function touched(x) = { X_set(2,64,x); true }
"""
        for expression in (
                "({ X_set(0,64,x); return(x); true }) & touched(x)",
                "({ X_set(0,64,x); return(x); false }) | touched(x)"):
            with self.subTest(expression=expression):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(
                        expression, helper, after="X_set(1,64,x);\n"))
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertNotIn("inlined touched", deps)
                self.assertFalse(self.constant_register_write_positions(text, 1))
                self.assertFalse(self.constant_register_write_positions(text, 2))

    def test_ordinary_boolean_helper_keeps_eager_argument_effects(self):
        helper = """
val eager_and : (bool,bool) -> bool
function eager_and(left,right) = left & right
val eager_or : (bool,bool) -> bool
function eager_or(left,right) = left | right
function and_bool_no_flow(left,right) = left & right
val or_bool_no_flow = pure "or_bool" : (bool,bool) -> bool
function or_bool_no_flow(left,right) = left | right
val touched : bits(64) -> bool
function touched(x) = { X_set(1,64,x); true }
val opaque = impure "opaque" : bits(64) -> bool
"""
        # The no_flow functions have the same external symbol as the special
        # calls, but ordinary AST identifiers. Their arguments remain eager.
        for operation, first in (("eager_and", "false"), ("eager_or", "true"),
                                  ("and_bool_no_flow", "false"),
                                  ("or_bool_no_flow", "true")):
            with self.subTest(operation=operation):
                text, deps = self.run_computation(
                    self.boolean_computation_fixture(f'{operation}({first},touched(x))', helper))
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertIn("inlined touched", deps)
                self.run_computation(
                    self.boolean_computation_fixture(f'{operation}({first},opaque(x))', helper),
                    error='unsupported primitive opaque')

    def test_pure_boolean_short_circuit_skips_only_unreachable_unknown_rhs(self):
        helper = 'val opaque = pure "opaque" : unit -> bool\n'
        for skipped, live, literal in (
                ("false & opaque()", "true & opaque()", "F"),
                ("true | opaque()", "false | opaque()", "T")):
            with self.subTest(skipped=skipped):
                source = helper + """
val ROOT : unit -> bool
function ROOT() = """ + skipped + "\n"
                text, deps = self.run_sail(source, roots=("ROOT",))
                self.assertRegex(text, r"\b" + literal + r"\b")
                self.assertNotIn("primitive-contract opaque", deps)
                self.run_sail(source.replace(skipped, live),
                              roots=("ROOT",),
                              error="unsupported primitive opaque")

    def test_pure_boolean_short_circuit_symbolic_rhs_is_not_discarded(self):
        for expression in ("(unsigned(x) == 0) & opaque()",
                           "(unsigned(x) == 0) | opaque()"):
            with self.subTest(expression=expression):
                source = """
val opaque = pure "opaque" : unit -> bool
val ROOT : bits(64) -> bool
function ROOT(x) = """ + expression + "\n"
                self.run_sail(source, roots=("ROOT",),
                              error="unsupported primitive opaque")

    def test_refined_boolean_selection_retains_evaluated_operand_effects(self):
        for predicate, expression, writes, live in (
                ("0 <= 'p", "predicate(position,x) | opaque()", 2, False),
                ("'p < 0", "predicate(position,x) & opaque()", 2, False),
                ("0 <= 'p", "predicate(position,x) & touched(x)", 3, True),
                ("'p < 0", "predicate(position,x) | touched(x)", 3, True)):
            with self.subTest(predicate=predicate, expression=expression):
                source = self.computation_fixture("""
val opaque = impure "opaque" : unit -> bool
val predicate : forall 'p. (int('p),bits(64)) -> bool(""" + predicate + """)
function predicate(position,x) = {
    X_set(0,64,x);
    """ + predicate.replace("'p", "position") + """
}
val touched : bits(64) -> bool
function touched(x) = { X_set(1,64,x); true }
val checked : forall 'p. (int('p),bits(64)) -> bits(64)
function checked(position,x) = {
    let ignored = """ + expression + """;
    x
}
""", "checked(unsigned(x[2..0]) * 8,x)")
                text, deps = self.run_computation(source)
                self.assertEqual(text.count("write (XREG"), writes)
                self.assertEqual(
                    len(self.constant_register_write_positions(text, 0)), 1)
                self.assertIn("inlined predicate", deps)
                self.assertNotIn("primitive-contract opaque", deps)
                if live:
                    self.assertIn("inlined touched", deps)
                    self.run_computation(
                        source.replace(expression, expression.replace('touched(x)', 'opaque()')),
                        error='unsupported primitive opaque')
                else:
                    self.assertNotIn("inlined touched", deps)
                # The checked return type must never suppress a failing
                # calculation in the left operand itself.
                self.run_computation(
                    source.replace("    X_set(0,64,x);",
                                   "    let ignored = opaque();\n"
                                   "    X_set(0,64,x);"),
                    error="unsupported primitive opaque")
                failed, failed_deps = self.run_computation(
                    source.replace("    X_set(0,64,x);",
                                   "    assert(false);\n    X_set(0,64,x);"))
                self.assert_failed_relation(failed, failed_deps)
                self.assertNotIn("write (XREG", failed)
                self.assertNotIn("primitive-contract opaque", failed_deps)

    def test_refined_boolean_selection_does_not_trust_an_opaque_operand(self):
        for result_type, expression in (
                ("true", "opaque() | true"),
                ("false", "opaque() & false")):
            with self.subTest(result_type=result_type):
                source = self.boolean_computation_fixture(
                    expression,
                    "val opaque = impure \"opaque\" : unit -> bool("
                    + result_type + ")\n")
                self.run_computation(source, error='unsupported primitive opaque')

    def test_static_integer_shift_discharge_plain_assertion(self):
        source = self.computation_fixture("""
val pow2 = pure "pow2" : forall 'n, 'n >= 0. int('n) -> int(2 ^ 'n)
val checked : bits(64) -> bits(64)
function checked(x) = {
    let len = 6;
    assert(64 >= _shl_int(1, len));
    assert(pow2(len) == 64);
    x
}
""", "checked(x)")
        text, deps = self.run_computation(source)
        self.assertIn("EXP", text)
        self.assertIn("primitive-contract _shl_int", deps)
        self.assertIn("primitive-contract pow2", deps)
        guarded, guarded_deps = self.run_computation(
            source.replace('64 >= _shl_int', '32 >= _shl_int'))
        self.assert_guarded_relation(guarded, guarded_deps,
                                     "gteq_int(32, _shl_int(1, len))")
        self.assertIn("EXP", guarded)
        self.assertIn("primitive-contract _shl_int", guarded_deps)

    def test_signed_integer_right_shift_uses_floor_division(self):
        source = self.computation_fixture(
            "", "get_slice_int(64,_shr_int(signed(x),1),0)")
        text, deps = self.run_computation(source)
        self.assertIn(" div ", text)
        self.assertIn("EXP", text)
        self.assertIn("primitive-contract _shr_int", deps)

    def test_integer_shift_rejects_unproved_or_negative_amount(self):
        declaration = """
val _shl_int = pure "shl_int" : (int, int) -> int
"""
        source = self.computation_fixture(
            declaration, "get_slice_int(64,_shl_int(1,signed(x)),0)")
        self.run_computation(
            source,
            error='integer shifts require a proved nonnegative amount')
        self.run_computation(
            source.replace('signed(x)', 'negate_atom(1)'),
            error='integer shifts require a proved nonnegative amount')

    def test_integer_shift_rejects_foreign_word_signature(self):
        source = self.computation_fixture("""
val _shl_int = pure "shl_int" : (bits(64), int) -> bits(64)
""", "_shl_int(x,1)")
        self.run_computation(
            source,
            error='integer shifts require integer arguments and result')

    def test_defined_integer_shift_is_inlined_not_contracted(self):
        source = self.computation_fixture("""
function _shl_int(x, amount) = x + amount
""", "get_slice_int(64,_shl_int(signed(x),1),0)")
        text, deps = self.run_computation(source)
        self.assertIn("inlined _shl_int", deps)
        self.assertNotIn("primitive-contract _shl_int", deps)
        self.assertNotIn("EXP", text)

    def test_power_of_two_rejects_negative_or_foreign_word_exponent(self):
        for declaration, expression, diagnostic in (
                ('val pow2 = pure "pow2" : int -> int',
                 "get_slice_int(64,pow2(negate_atom(1)),0)",
                 "power of two requires a proved nonnegative exponent"),
                ('val pow2 = pure "pow2" : bits(64) -> bits(64)',
                 "pow2(x)", "power of two requires an integer argument and result")):
            source = self.computation_fixture(declaration + "\n", expression)
            self.run_computation(source, error=diagnostic)

    def test_shift_argument_helper_write_is_retained(self):
        source = self.computation_fixture("""
val amount : bits(64) -> int(1)
function amount(x) = { X_set(0,64,x); 1 }
""", "get_slice_int(64,_shl_int(1,amount(x)),0)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined amount", deps)

    def test_original_type_alias_is_selected_with_its_dependency(self):
        source = """
type PARTIDtype = bits(16)
type PMGtype = bits(8)
struct MPAMinfo = { partid : PARTIDtype, pmg : PMGtype }
val ROOT : MPAMinfo -> PARTIDtype
function ROOT(x) = x.partid
"""
        text, _ = self.run_sail(
            source, roots=("ROOT",))
        self.assertIn("16 word", text)
        self.assertIn("8 word", text)
        changed, _ = self.run_sail(
            source.replace("PARTIDtype = bits(16)", "PARTIDtype = bits(32)"),
            roots=("ROOT",))
        self.assertIn("32 word", changed)
        self.assertNotEqual(text, changed)

    def test_missing_original_type_dependency_is_refused_by_frontend(self):
        source = """
type PARTIDtype = bits(16)
struct MPAMinfo = { partid : PARTIDtype }
val ROOT : MPAMinfo -> PARTIDtype
function ROOT(x) = x.partid
"""
        self.run_sail(source.replace("type PARTIDtype = bits(16)", ""),
                      roots=("ROOT",),
                      error="PARTIDtype")

    def mask_bounds_fixture(self, mask="0b011111", extra=""):
        return self.computation_fixture("""
val checked : forall 'p. (int('p), bits(64)) -> bits(64)
function checked(p, x) = { assert(constraint('p <= 31)); x }
""" + extra + """
val selected : bits(64) -> bits(64)
function selected(x) = {
    let 'p = unsigned(and_vec(x[5 .. 0], """ + mask + """));
    checked(p, x)
}
""", "selected(x)")

    def test_mask_unsigned_upper_bound_discharge_helper_assertion(self):
        text, deps = self.run_computation(self.mask_bounds_fixture())
        self.assertIn("word_and", text)
        self.assertIn("statically-proved-assertion", deps)
        for mask in ("0b111111", "0b100000"):
            with self.subTest(mask=mask):
                guarded, guarded_deps = self.run_computation(
                    self.mask_bounds_fixture(mask))
                self.assert_guarded_relation(guarded, guarded_deps,
                                             "lteq_int(__id(p), 31)")
                self.assertIn("word_and", guarded)
                self.assertIn("(& 31)", guarded)
                self.assertNotIn("statically-proved-assertion", guarded_deps)

    def test_widened_word_bounds_preserve_actual_mask_helper_body(self):
        source = self.mask_bounds_fixture("sail_zero_extend(x[4 .. 0], 6)")
        text, deps = self.run_computation(source)
        self.assertIn("word_zx", text)
        self.assertIn("statically-proved-assertion", deps)
        helper = """
val mask : bits(64) -> bits(6)
function mask(x) = sail_zero_extend(x[4 .. 0], 6)
"""
        source = self.mask_bounds_fixture("mask(x)", helper)
        text, deps = self.run_computation(source)
        self.assertIn("inlined mask", deps)
        guarded, guarded_deps = self.run_computation(
            source.replace('sail_zero_extend(x[4 .. 0], 6)', '0b111111'))
        self.assert_guarded_relation(guarded, guarded_deps,
                                     "lteq_int(__id(p), 31)")
        self.assertIn("inlined mask", guarded_deps)
        self.assertIn("word 63", guarded)

    @staticmethod
    def integer_selection_fixture(selector):
        return """
register Side : bits(64)
register D : bits(64)
val selected : bits(64) -> int
function selected(x) = { Side = x; """ + selector + """ }
val ROOT : bits(64) -> unit
function ROOT(x) = {
    D = match selected(x) {
        1 => sub_bits(x,x),
        2 => add_bits(x,x),
        _ => not_vec(x)
    }
}
"""

    def test_known_integer_match_keeps_actual_clause_and_selector_effects(self):
        operations = ("word_sub", "word_add", "word_not")
        for selector, operation in (("1", "word_sub"), ("2", "word_add"),
                                    ("7", "word_not")):
            with self.subTest(selector=selector):
                text, deps = self.run_computation(
                    self.integer_selection_fixture(selector))
                self.assertIn(operation, text)
                for unused in set(operations) - {operation}:
                    self.assertNotIn(unused, text)
                self.assertEqual(text.count("write reg_Side"), 1)
                self.assertEqual(text.count("write reg_D"), 1)
                self.assertIn("inlined selected", deps)
                root = text.split("let sail_hl_ROOT = new_definition", 1)[1]
                if "write reg_Side" in root:
                    self.assertLess(root.index("write reg_Side"),
                                    root.index("write reg_D"))
                else:
                    _, state, _ = self.shared_result(text, "selected")
                    self.assertRegex(root, r"write reg_D[^\n]+\b" + state + r"\b")

    def test_unknown_integer_match_refuses_a_dynamic_selector(self):
        self.run_computation(
            self.integer_selection_fixture("signed(x)"),
            error="integer matches require a statically known selector")

    def test_known_integer_match_skips_only_unreachable_unsupported_body(self):
        source = self.integer_selection_fixture("2").replace(
            "val selected :", 'val opaque = impure "opaque" : unit -> bits(64)\n'
            "val selected :").replace("1 => sub_bits(x,x)", "1 => opaque()")
        text, deps = self.run_computation(source)
        self.assertIn("word_add", text)
        self.assertIn("write reg_Side", text)
        self.assertNotIn("primitive-contract opaque", deps)
        self.run_computation(
            source.replace("Side = x; 2", "Side = x; 1"),
            error="unsupported primitive opaque")

    @staticmethod
    def replication_scale_fixture(opcode, size):
        # Retain the actual LD1R decoder's scale/index dataflow. This is a
        # language-construct regression, not a substitute instruction model.
        return """
register D : bits(64)
val configured : (bits(3), bits(2)) -> unit
function configured(opcode,size) = {
    let 'init_scale = unsigned(opcode[2 .. 1]);
    scale : int = init_scale;
    index : int = undefined;
    match scale {
        3 => { scale = unsigned(size) },
        0 => { index = 0 },
        1 => { index = 1 },
        2 => { index = 2 },
        _ => ()
    };
    let 'scale = scale;
    let 'index = index;
    let 'esize = _shl_int_general(8,scale);
    assert(constraint('esize in {8,16,32,64}));
    D = get_slice_int(64,esize,0)
}
val ROOT : bits(3) -> unit
function ROOT(raw_opcode) = configured(""" + opcode + "," + size + ")\n"

    def test_ld1r_scale_match_keeps_checked_slice_and_undefined_index(self):
        for size, element in (("0b00", 8), ("0b01", 16), ("0b10", 32), ("0b11", 64)):
            with self.subTest(size=size, element=element):
                text, deps = self.run_computation(
                    self.replication_scale_fixture("0b110", size))
                self.assert_existential_choice(text, deps, "int")
                self.assertIn("word_subword", text)
                self.assertIn("word 6", text)
                self.assertIn("EXP", text)
                self.assertIn("write reg_D", text)
                self.assertIn("inlined configured", deps)
                self.assertIn("statically-proved-assertion", deps)
                self.assertNotIn("guarded-assertion", deps)

    def test_ld1r_scale_match_refuses_unfixed_opcode_slice(self):
        self.run_computation(
            self.replication_scale_fixture("raw_opcode", "0b10"),
            error="integer matches require a statically known selector")

    def test_unused_mutable_plain_integer_retains_an_existential_choice(self):
        source = """
register D : bits(64)
val ignored : bits(64) -> bits(64)
function ignored(x) = {
    index : int = undefined;
    x + x
}
val ROOT : bits(64) -> unit
function ROOT(x) = D = ignored(x)
"""
        text, deps = self.run_computation(source)
        self.assert_existential_choice(text, deps, "int")
        self.assertIn("word_add", text)
        self.assertIn("write reg_D", text)
        self.assertIn("inlined ignored", deps)
        self.assertNotIn("unobserved-undefined-local index", deps)
        self.assertNotIn("sail_hl_shared_output_ignored", text)
        choice = re.search(r"\(\?\((v\d+):int\)", text).group(1)
        self.assertEqual(len(re.findall(r"\b" + choice + r"\b", text)), 1)
        self.assertNotIn("(& 0)", text)

    def test_used_mutable_integer_choice_reaches_guard_and_register_value(self):
        source = """
register D : bits(64)
val ROOT : unit -> unit
function ROOT() = {
    index : int = undefined;
    assert(index == 7);
    D = get_slice_int(64,index,0)
}
"""
        text, deps = self.run_computation(source)
        self.assert_existential_choice(text, deps, "int")
        self.assert_guarded_relation(text, deps, "eq_int(index, 7)")
        self.assertIn("primitive-contract get_slice_int", deps)
        self.assertIn("write reg_D", text)
        choice = re.search(r"\(\?\((v\d+):int\)", text).group(1)
        self.assertGreaterEqual(len(re.findall(r"\b" + choice + r"\b", text)), 3)
        self.assertIn("(& 7)", text)
        # Both the guard and conversion must read the chosen integer, not
        # an invented zero initializer or a constant replacement for its use.
        cast = re.search(r"\(iword \((v\d+):int\)\)", text)
        self.assertIsNotNone(cast, text)
        self.assertRegex(text, r"\blet " + cast.group(1) + r" = \(\(" +
                         choice + r":int\):int\)")
        output = re.search(r"\blet (v\d+) = \(\(iword \(" +
                           cast.group(1) + r":int\)\):64 word\)", text)
        self.assertIsNotNone(output, text)
        self.assertIn("write reg_D " + output.group(1) + " s", text)

    def test_mask_bounds_keep_argument_effects_and_refuse_unknown_call(self):
        helper = """
val mask : bits(64) -> bits(6)
function mask(x) = { X_set(0,64,x); 0b011111 }
"""
        source = self.mask_bounds_fixture("mask(x)", helper)
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined mask", deps)
        source = self.mask_bounds_fixture(
            "opaque(x)", 'val opaque = impure "opaque" : bits(64) -> bits(6)\n')
        self.run_computation(source, error='unsupported primitive opaque')

    def config_fixture(self, extra_fields=None, statements=""):
        if extra_fields is None:
            extra_fields = "EL : bits(2), BTYPE : bits(2), nRW : bits(1)"
        return self.computation_fixture("""
struct config_state = {
    N : bits(1), Z : bits(1), C : bits(1), V : bits(1),
""" + extra_fields + """
}
register PSTATE : config_state
val selected : bits(64) -> bits(64)
function selected(x) = {
""" + statements + """
    get_slice_int(64,unsigned(PSTATE.EL) + unsigned(PSTATE.N),0)
}
""", "selected(x)")

    def test_explicit_pstate_configuration_preserves_real_flag_reads(self):
        source = self.config_fixture(statements="PSTATE.N = 0b1;")
        text, deps = self.run_computation(source)
        self.assertIn("reg_PSTATE", text)
        self.assertIn("read reg_PSTATE", text)
        self.assertIn("write NF", text)
        written = re.search(r"let (v[0-9]+) = \(write NF", text)
        self.assertIsNotNone(written, text)
        self.assertIn("read NF " + written.group(1), text)
        self.assertIn("primitive-contract Arm-explicit-PSTATE-config-projection", deps)
        self.assertIn("primitive-contract PSTATE-NZCV-projection", deps)

    def test_pstate_single_configuration_field_keeps_explicit_component(self):
        text, _ = self.run_computation(self.config_fixture('EL : bits(2)'))
        self.assertIn("reg_PSTATE", text)
        self.assertIn("2 word", text)

    def test_pstate_configuration_foreign_shape_or_writes_are_refused(self):
        for fields in ("EL : bits(1)", "EL : bits(2), opaque : bits(8)",
                       "EL : bits(2), nRW : bits(2)"):
            self.run_computation(
                self.config_fixture(fields),
                error='PSTATE configuration requires exact')
        self.run_computation(
            self.config_fixture(statements='PSTATE.EL = 0b11;'),
            error='unsupported PSTATE field write')
        self.run_computation(
            self.config_fixture(statements='PSTATE = PSTATE;'),
            error='whole PSTATE writes are unsupported')

    def test_original_top_level_let_is_imported_and_not_replaced(self):
        source = """
let EL0 : bits(2) = 0b00
val ROOT : bits(2) -> bits(2)
function ROOT(x) = EL0
"""
        text, _ = self.run_sail(source, roots=("ROOT",))
        changed, _ = self.run_sail(source.replace("0b00", "0b11"),
                                   roots=("ROOT",))
        self.assertIn("word 0", text)
        self.assertIn("word 3", changed)
        self.assertNotEqual(text, changed)
        self.run_sail(source.replace("function ROOT(x) = EL0",
                                    "function ROOT(x) = EL1"),
                      roots=("ROOT",), error="EL1")

    def test_original_top_level_let_unknown_producer_is_not_discarded(self):
        source = """
val opaque = pure "opaque" : unit -> bits(2)
let EL0 = opaque()
val ROOT : bits(2) -> bits(2)
function ROOT(x) = EL0
"""
        # The actual binding must reach the exporter, not a guessed EL0.
        self.run_sail(source, roots=("ROOT",),
                      error="unsupported primitive opaque")

    def gcs_fixture(self, extra="", feature="FEAT_GCS", el="0b00"):
        # The disabled feature must skip the right operand and its argument.
        return self.computation_fixture("""
enum Feature = { FEAT_GCS, FEAT_OTHER }
val IsFeatureImplemented = pure "IsFeatureImplemented" : Feature -> bool
val GCSEnabled = pure "GCSEnabled" : bits(2) -> bool
val opaque = impure "opaque" : bits(64) -> bits(64)
""" + extra + """
val selected : bits(64) -> bits(64)
function selected(x) = {
    if IsFeatureImplemented(""" + feature + ") & GCSEnabled(" + el + """)
    then opaque(x) else x
}
""", "selected(x)")

    def test_disabled_gcs_skips_the_right_operand_and_its_argument(self):
        cases = (
            ("", "0b00"),
            ("""
val el : bits(64) -> bits(2)
function el(x) = { X_set(0,64,x); 0b00 }
""", "el(x)"),
            ('val unknown = impure "unknown" : bits(64) -> bits(2)\n',
             "unknown(x)"))
        for helper, argument in cases:
            with self.subTest(argument=argument):
                text, deps = self.run_computation(
                    self.gcs_fixture(helper, el=argument))
                self.assertEqual(text.count("write (XREG"), 1)
                self.assertNotIn("inlined el", deps)
                self.assertNotIn("primitive-contract unknown", deps)
                self.assertIn("disabled-extension Arm-GCS", deps)

    def test_disabled_gcs_refuses_other_feature_or_shadowed_name(self):
        self.run_computation(
            self.gcs_fixture(feature='FEAT_OTHER'),
            error='disabled GCS feature query requires the actual')
        source = self.gcs_fixture().replace(
            "function selected(x) = {",
            "function selected(x) = { let FEAT_GCS = FEAT_OTHER;")
        self.run_computation(
            source,
            error='disabled GCS feature query requires the actual')

    def test_defined_gcs_helpers_are_not_replaced_by_disabled_contracts(self):
        source = self.gcs_fixture("""
function IsFeatureImplemented(feature) = true
function GCSEnabled(el) = true
""")
        self.run_computation(source, error='unsupported primitive opaque')

    def test_normal_word_and_bool_register_writes_keep_components(self):
        source = self.computation_fixture("""
register BookkeepingWord : bits(2)
register BookkeepingFlag : bool
val selected : bits(64) -> bits(64)
function selected(x) = { BookkeepingWord = 0b10; BookkeepingFlag = true; x }
""", "selected(x)")
        text, deps = self.run_computation(source)
        self.assertIn("write reg_BookkeepingWord", text)
        self.assertIn("write reg_BookkeepingFlag", text)
        self.assertIn("reg_BookkeepingWord:(armstate,2 word)component", text)
        self.assertIn("reg_BookkeepingFlag:(armstate,bool)component", text)
        self.assertIn("primitive-contract typed-register-component-write", deps)
        source = source.replace(
            "BookkeepingWord = 0b10; BookkeepingFlag = true;",
            "(BookkeepingWord, BookkeepingFlag) = (0b10,true);")
        text, _ = self.run_computation(source)
        self.assertIn("write reg_BookkeepingWord", text)
        self.assertIn("write reg_BookkeepingFlag", text)

    def test_normal_register_write_retains_rhs_helper_effects(self):
        source = self.computation_fixture("""
register BookkeepingWord : bits(2)
val retained : bits(64) -> bits(2)
function retained(x) = { X_set(0,64,x); 0b10 }
val selected : bits(64) -> bits(64)
function selected(x) = { BookkeepingWord = retained(x); x }
""", "selected(x)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("write reg_BookkeepingWord", text)
        self.assertIn("inlined retained", deps)
        source = source.replace("val retained : bits(64) -> bits(2)",
                                'val retained = impure "retained" : bits(64) -> bits(2)')
        source = source.replace(
            "function retained(x) = { X_set(0,64,x); 0b10 }\n", "")
        self.run_computation(source, error='unsupported primitive retained')

    def test_normal_register_write_refuses_uninitialized_rhs(self):
        source = self.computation_fixture("""
register BTypeNext : bits(2)
val selected : bits(64) -> bits(64)
function selected(x) = {
    unknown : bits(2) = undefined;
    BTypeNext = unknown;
    x
}
""", "selected(x)")
        self.run_computation(source, error='uninitialized bits')

    def test_normal_register_write_refuses_foreign_datatype(self):
        source = self.computation_fixture("""
register counter : int
val selected : bits(64) -> bits(64)
function selected(x) = { counter = 1; x }
""", "selected(x)")
        self.run_computation(source, error='normal register writes support only')

    def test_tuple_assignment_cannot_write_frozen_source_pc(self):
        source = self.computation_fixture("""
register _PC : bits(64)
register Bookkeeping : bits(64)
val selected : bits(64) -> bits(64)
function selected(x) = { (_PC,Bookkeeping) = (x,x); x }
""", "selected(x)")
        self.run_computation(source, error='projected or frozen source registers')
        source = self.computation_fixture("""
register SPESampleInFlight : bool
val selected : bits(64) -> bits(64)
function selected(x) = { SPESampleInFlight = true; x }
""", "selected(x)")
        self.run_computation(source, error='projected or frozen source registers')

    def ordered_match_fixture(self, clauses, expression="0b0100010",
                              extra=""):
        return self.computation_fixture("""
val opaque = impure "opaque" : bits(64) -> bits(64)
""" + extra + """
val selected : (bits(7), bits(64)) -> bits(64)
function selected(c,x) = match c {
""" + clauses + """
}
""", "selected(" + expression + ",x)")

    def test_ordered_bit_masks_keep_first_match_and_known_selection(self):
        clauses = """
    [0b0,0b1,0b0,0b0,_,_,0b0] => x,
    0b0100010 => opaque(x),
    _ => x
"""
        source = self.ordered_match_fixture(clauses)
        text, deps = self.run_computation(source)
        self.assertNotIn("opaque", text)
        self.assertIn("inlined selected", deps)
        reversed_source = self.ordered_match_fixture("""
    0b0100010 => opaque(x),
    [0b0,0b1,0b0,0b0,_,_,0b0] => x,
    _ => x
""")
        self.run_computation(reversed_source, error='unsupported primitive opaque')

    def test_ordered_bit_masks_keep_scrutinee_helper_effects(self):
        source = self.ordered_match_fixture("""
    [0b0,0b1,0b0,0b0,_,_,0b0] => x,
    _ => opaque(x)
""", expression="selector(x)", extra="""
val selector : bits(64) -> bits(7)
function selector(x) = { X_set(0,64,x); 0b0100010 }
""")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined selector", deps)

    def test_ordered_bit_masks_dynamic_scrutinee_keeps_reachable_cases(self):
        source = self.ordered_match_fixture("""
    [0b0,0b1,0b0,0b0,_,_,0b0] => x,
    _ => not_vec(x)
""", expression="0b00 @ d")
        text, _ = self.run_computation(source)
        self.assertIn("word_and", text)
        self.assertIn("word_not", text)
        self.run_computation(
            source.replace('not_vec(x)', 'opaque(x)'),
            error='unsupported primitive opaque')

    def test_ordered_bit_masks_validate_duplicate_and_incomplete_patterns(self):
        duplicate = self.ordered_match_fixture("""
    0b0000000 => x,
    0b0000000 => x,
    _ => x
""")
        self.run_computation(
            duplicate,
            error='ordered bit match contains duplicate patterns')
        incomplete = self.ordered_match_fixture("""
    [0b0,_,_,_,_,_,_] => x
""")
        self.run_computation(
            incomplete,
            error='ordered bit match must cover every possible value')

    def test_ordered_bit_masks_refuse_unselected_noncanonical_guards(self):
        source = self.ordered_match_fixture("""
    matched if unsigned(matched) == 127 => opaque(x),
    _ => x
""")
        self.run_computation(
            source,
            error='ordered bit matches reject guarded patterns')

    def guarded_word_fixture(self, width, equality, effectful, guarded):
        """Compare a canonical pattern guard with the same ordinary call."""
        literal = f"0b{(0 if width == 2 else 22):0{width}b}"
        declarations = f"""
val eq_bits = {('impure' if equality == 'impure' else 'pure')} "eq_bits" :
    forall 'n. (bits('n),bits('n)) -> bool
register Dummy : bool
"""
        if equality == "defined":
            declarations += "function eq_bits(x,y) = { Dummy = true; false }\n"
        if guarded:
            remaining = ("0b01 => x, 0b10 => x, 0b11 => not_vec(x)"
                         if width == 2 else "_ => not_vec(x)")
            expression = (
                "match c {\n"
                f"    matched if eq_bits(matched,{literal}) => x,\n"
                f"    {remaining}\n"
                "}")
        else:
            expression = f"if eq_bits(c,{literal}) then x else not_vec(x)"
        helper = declarations + f"""
val selected : (bits({width}),bits(64)) -> bits(64)
function selected(c,x) = {{
    {('Dummy = true;' if effectful else '')}
    {expression}
}}
"""
        selector = ("d[1..0]" if width == 2 else "d" if width == 5 else
                    "0b" + "0" * (width - 5) + " @ d")
        return self.computation_fixture(helper, f"selected({selector},x)")

    def test_word_pattern_guards_are_refused(self):
        for width in (2, 5, 8):
            with self.subTest(width=width):
                self.run_computation(
                    self.guarded_word_fixture(width, "pure", False, True),
                    error="bit matches require unguarded binary literal cases"
                    if width == 2 else "ordered bit matches reject guarded patterns")

    def test_ordinary_word_equality_retains_defined_bodies_and_rejects_impurity(self):
        for width in (2, 5, 6, 7, 8):
            for effectful in (False, True):
                for equality in ("pure", "impure", "defined"):
                    with self.subTest(width=width, effectful=effectful,
                                      equality=equality):
                        result = self.run_computation(
                            self.guarded_word_fixture(width, equality, effectful, False),
                            error='stateless operations require a pure external declaration' if equality == 'impure' else None)
                        if equality != "impure":
                            text, dependencies = result
                            self.assertEqual(text.count("write reg_Dummy"),
                                             int(effectful) + int(equality == "defined"))
                            if equality == "defined":
                                self.assertIn("inlined eq_bits", dependencies)
                                self.assertNotIn("primitive-contract eq_bits", dependencies)

    def test_generic_defined_helper_types_are_specialized_per_call(self):
        source = self.computation_fixture("""
val eq_any = pure "eq_any" : forall ('a : Type). ('a,'a) -> bool
enum Mode = { Mode_A, Mode_B }
val ident : forall ('a : Type). 'a -> 'a
function ident(x) = x
val different : forall ('a : Type). ('a,'a) -> bool
function different(x,y) = not_bool(eq_any(ident(x),ident(y)))
val selected : bits(64) -> bits(64)
function selected(x) = {
    assert(not_bool(different(0b00,0b00)));
    assert(not_bool(different(false,false)));
    if different(Mode_A,Mode_B) then ident(x) else not_vec(ident(x))
}
""", "selected(x)")
        text, deps = self.run_computation(source)
        self.assertIn(":2 word", text)
        self.assertIn("inlined ident", deps)
        self.assertIn("inlined different", deps)
        self.assertNotIn("primitive-contract different", deps)

    def test_generic_helper_accepts_enum_declared_after_helper(self):
        # Arm defines neq_any in prelude.sail, before v8_base.sail's MemOp.
        # A substituted type needs that actual enum declaration, without
        # importing the caller's local variables or numeric assumptions.
        helpers = """
val eq_any = pure "eq_any" : forall ('a : Type). ('a,'a) -> bool
val different : forall ('a : Type). ('a,'a) -> bool
function different(x,y) = not_bool(eq_any(x,y))
enum Mode = { Mode_A, Mode_B }
val selected : bits(64) -> bits(64)
function selected(x) = {
    mode : Mode = undefined;
    mode = Mode_A;
    if different(mode,Mode_B) then x else not_vec(x)
}
"""
        text, deps = self.run_computation(
            self.computation_fixture(helpers, "selected(x)"))
        self.assertIn("inlined different", deps)
        self.assertIn("unobserved-undefined-local mode", deps)
        self.assertIn("sail_hl_ctor_Mode_5fA", text)
        self.assertIn("sail_hl_ctor_Mode_5fB", text)
        # The same failure must not be mistaken for undefined initialization.
        self.run_computation(self.computation_fixture(
            helpers.replace("mode : Mode = undefined;\n    mode = Mode_A;",
                            "let mode = Mode_A;"), "selected(x)"))

    def test_generic_defined_helper_retains_inequality_body_and_effects(self):
        source = self.computation_fixture("""
val eq_any = pure "eq_any" : forall ('a : Type). ('a,'a) -> bool
val neq_any : forall ('a : Type). ('a,'a) -> bool
function neq_any(x,y) = not_bool(eq_any(x,y))
val touched : bits(64) -> bits(2)
function touched(x) = { X_set(0,64,x); 0b00 }
val selected : bits(64) -> bits(64)
function selected(x) = {
    assert(not_bool(neq_any(touched(x),0b00)));
    x
}
""", "selected(x)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined neq_any", deps)
        self.assertNotIn("primitive-contract neq_any", deps)
        guarded, guarded_deps = self.run_computation(
            source.replace('function neq_any(x,y) = not_bool(eq_any(x,y))',
                           'function neq_any(x,y) = true'))
        self.assert_guarded_relation(guarded, guarded_deps, "neq_any")
        self.assertIn("inlined neq_any", guarded_deps)
        self.assertNotIn("primitive-contract neq_any", guarded_deps)
        self.assertEqual(guarded.count("write (XREG"), 2)

    def test_generic_helper_unknown_effect_is_not_hidden_by_type_specialization(self):
        source = self.computation_fixture("""
val foreign = impure "foreign" : unit -> unit
val ident : forall ('a : Type). 'a -> 'a
function ident(x) = { foreign(); x }
""", "ident(x)")
        self.run_computation(source, error='unsupported primitive foreign')

    def test_guarded_assertion_retains_condition_helper_state(self):
        source = HEADER + """
union ExecutionResult = { Retire_Success : unit, Trap : unit }
register PC : bits(32)
val set_next_pc = impure "set_next_pc" : bits(32) -> unit
val touched : bits(32) -> bool
function touched(x) = { set_next_pc(x); unsigned(x) == 0 }
val ROOT : bits(32) -> ExecutionResult
function ROOT(x) = { assert(touched(x)); Retire_Success() }
"""
        text, deps = self.run_sail(
            source, roots=("ROOT",), architecture="rv32",
            normal_retirement=True)
        written = re.search(r"let (v[0-9]+) = \(write PC", text)
        self.assertIsNotNone(written, text)
        self.assertIn("read PC " + written.group(1), text)
        self.assertIn("guarded-assertion", deps)
        self.assertIn("inlined touched", deps)

    def test_retirement_abort_has_no_successful_outcome(self):
        source = HEADER + """
union ExecutionResult = { Retire_Success : unit, Trap : unit }
val set_next_pc = impure "set_next_pc" : bits(32) -> unit
val ROOT : bits(32) -> ExecutionResult
function ROOT(x) = { set_next_pc(x); exit(); Retire_Success() }
"""
        for guarded in (False, True):
            with self.subTest(guarded=guarded):
                program = source.replace(
                    "exit();", "assert(x == 0x00000000); exit();"
                ) if guarded else source
                text, deps = self.run_sail(
                    program, roots=("ROOT",), architecture="rv32",
                    normal_retirement=True)
                code = without_comments(text)
                self.assertIn("Sail-exit-no-normal-state", deps)
                self.assertIn("write PC", code)
                self.assertRegex(code, r"\bin\s+F\b|\.\s*F\b|/\\\s+F\b")
                self.assertNotIn("EventJump", code)
                self.assertNotIn("fault-any-final-state", deps)

    def test_internal_256_bit_word_does_not_expand_register_contracts(self):
        source = HEADER + """
val ROOT : bits(128) -> bits(256)
function ROOT(x) = x @ x
"""
        text, _ = self.run_sail(source, roots=("ROOT",))
        self.assertIn("256 word", text)
        self.assertIn("word_join", text)
        for width in (384, 2048):
            with self.subTest(internal_width=width):
                text, _ = self.run_sail(HEADER + f"""
val ROOT : bits({width}) -> bits({width})
function ROOT(x) = x
""", roots=("ROOT",))
                self.assertIn(f"{width} word", text)
        oversized = HEADER + """
val ROOT : bits(2049) -> bits(2049)
function ROOT(x) = x
"""
        self.run_sail(oversized, roots=("ROOT",), error="0 through 2048")
        source = self.vector_fixture(
            "V_set(r,128,V_read(0,256)[127..0])").replace(
                "{8,16,32,64,128}", "{8,16,32,64,128,256}")
        self.run_computation(
            source,
            error='V_read requires a matching 8/16/32/64/128-bit result')

    def test_packed_table_slice_keeps_symbolic_in_bounds_byte_index(self):
        source = HEADER + """
val ROOT : (bits(2048), bits(8)) -> bits(8)
function ROOT(table, index) = slice(table, unsigned(index) * 8, 8)
"""
        text, deps = self.run_sail(source, roots=("ROOT",))
        self.assertIn("word_subword", text)
        self.assertIn("num_of_int", text)
        self.assertIn("primitive-contract slice", deps)

    def test_slice_refuses_negative_overflow_and_unproved_offsets(self):
        for start in ("0 - 1", "57", "unsigned(index)"):
            with self.subTest(start=start):
                source = HEADER + f"""
val ROOT : (bits(64), bits(8)) -> bits(8)
function ROOT(value, index) = slice(value, {start}, 8)
"""
                self.run_sail(source, roots=("ROOT",), error=(
                    "proved in-bounds offset" if start == "unsigned(index)"
                    else "positions are out of bounds"))

    def test_slice_offset_helper_effect_is_retained(self):
        source = self.computation_fixture("""
val offset : bits(64) -> int(8)
function offset(x) = { X_set(1,64,x); 8 }
""", "sail_zero_extend(slice(x,offset(x),8),64)")
        text, deps = self.run_computation(source)
        self.assertIn("inlined offset", deps)
        self.assertGreaterEqual(text.count("(write"), 2)
        self.assertIn("word_subword", text)

    def test_set_slice_bits_preserves_partial_initialization_masks(self):
        source = self.computation_fixture("""
val initialized : bits(64) -> bits(64)
function initialized(x) = {
    out : bits(64) = undefined;
    foreach (i from 0 to 7 by 1 in inc) {
        out = set_slice_bits(8,out,i*8,slice(x,i*8,8))
    };
    out
}
""", "initialized(x)")
        text, deps = self.run_computation(source)
        self.assertIn("word_insert", text)
        self.assertIn("inlined initialized", deps)
        partial = source.replace("i from 0 to 7", "i from 0 to 6")
        self.run_computation(partial, error='undefined local before assignment')

    def test_set_slice_bits_can_read_only_the_initialized_slice(self):
        source = self.computation_fixture("""
val initialized : bits(64) -> bits(64)
function initialized(x) = {
    out : bits(64) = undefined;
    out = set_slice_bits(8,out,8,slice(x,0,8));
    sail_zero_extend(slice(out,8,8),64)
}
""", "initialized(x)")
        text, _ = self.run_computation(source)
        self.assertIn("word_insert", text)
        self.run_computation(
            source.replace('slice(out,8,8)', 'slice(out,0,8)'),
            error='uninitialized bits')

    def test_set_slice_bits_checks_dynamic_bounds_and_partial_offset(self):
        known = HEADER + """
val ROOT : (bits(64),bits(8),bits(3)) -> bits(64)
function ROOT(value,inserted,index) =
    set_slice_bits(8,value,unsigned(index)*8,inserted)
"""
        text, _ = self.run_sail(known, roots=("ROOT",))
        self.assertIn("word_insert", text)
        self.run_sail(known.replace("bits(3)", "bits(4)"), roots=("ROOT",),
                      error="proved in-bounds offset")
        partial = self.computation_fixture("""
val inserted : (bits(64),bits(3)) -> bits(64)
function inserted(x,index) = {
    out : bits(64) = undefined;
    out = set_slice_bits(8,out,unsigned(index)*8,slice(x,0,8));
    out
}
""", "inserted(x,0b000)")
        # Keep the position symbolic: passing a literal would legitimately
        # specialize it and fail later only when the untouched bits are read.
        partial = partial.replace("inserted(x,0b000)", "inserted(x,x[2..0])")
        self.run_computation(
            partial,
            error='partial set_slice_bits requires a static offset')

    def test_exhaustive_small_bit_match_drops_only_unreachable_default(self):
        source = self.computation_fixture("""
val selected : (bits(2),bits(64)) -> bits(64)
function selected(selector,value) = match selector {
    0b00 => value, 0b01 => value + 0x0000000000000001,
    0b10 => value + 0x0000000000000002,
    0b11 => value + 0x0000000000000003,
    _ => undefined : bits(64)
}
""", "selected(x[1..0],x)")
        text, deps = self.run_computation(source)
        self.assertIn("word_add", text)
        self.assertNotIn("Sail-undefined-existential", deps)
        partial, partial_deps = self.run_computation(
            source.replace('0b11 => value + 0x0000000000000003,', ''))
        self.assert_existential_choice(partial, partial_deps, "64 word")
        self.assertIn("word_add", partial)
        # The uncovered selector retains a fresh choice; it is not silently
        # replaced by one of the three explicitly selected arithmetic values.
        self.assertGreaterEqual(partial.count("if "), 3)

    def test_small_bit_default_covers_every_remaining_value(self):
        source = self.computation_fixture("""
val selected : (bits(2),bits(64)) -> bits(64)
function selected(selector,value) = match selector {
    0b00 => value, _ => value + 0x0000000000000001
}
""", "selected(x[1..0],x)")
        text, _ = self.run_computation(source)
        self.assertIn("word_add", text)
        self.run_computation(
            source.replace('_ => value + 0x0000000000000001', '0b00 => value, _ => value + 0x0000000000000001'),
            error='every value exactly once')

    def test_direct_recursion_unfolds_only_decreasing_static_instances(self):
        source = self.computation_fixture("""
val countdown : forall 'n, 'n >= 0. int('n) -> bits(64)
function countdown(n) =
    if n == 0 then 0x0000000000000000 else countdown(n - 1)
""", "x + countdown(4)")
        text, deps = self.run_computation(source)
        self.assertIn("word_add", text)
        self.assertIn("inlined countdown", deps)
        for call in ("countdown(n)", "countdown(n + 1)"):
            with self.subTest(call=call):
                self.run_computation(
                    source.replace('countdown(n - 1)', call),
                    error='decreasing static instance')
        self.run_computation(
            source.replace('countdown(4)', 'countdown(unsigned(x))'),
            error='decreasing static instance')

    def test_static_recursive_helper_keeps_executed_writes(self):
        source = self.computation_fixture("""
val countdown : forall 'n, 'n >= 0. int('n) -> bits(64)
function countdown(n) = {
    X_set(1,64,0x0000000000000001);
    if n == 0 then 0x0000000000000000 else countdown(n - 1)
}
""", "countdown(3)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("(write"), 5)
        self.assertIn("inlined countdown", deps)

    def test_static_recursion_can_carry_unmeasured_runtime_values(self):
        source = self.computation_fixture("""
val countdown : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (int('n),int('m),bits(64)) -> bits(64)
function countdown(n,m,x) =
    if n == 0 then x else countdown(n-1,m,x)
""", "countdown(3,4,x)")
        self.run_computation(source)
        # n remains a fixed decreasing type argument; m need not be a
        # termination measure when it carries unrelated runtime data.
        self.run_computation(
            source.replace('countdown(n-1,m,x)', 'countdown(n-1,unsigned(x),x)'))
        self.run_computation(
            source.replace('countdown(n-1,m,x)', 'countdown(n-1,m+1,x)'),
            error='decreasing static instance')

    def test_single_field_records_preserve_declared_field_and_value(self):
        source = HEADER + """
struct Packed = { payload : bits(64) }
val ROOT : bits(64) -> bits(64)
function ROOT(value) = {
    let packed : Packed = struct { payload = value };
    packed.payload
}
"""
        text, _ = self.run_sail(source, roots=("ROOT",))
        self.assertIn("64 word", text)
        self.assertNotIn("FST", text)

    def test_single_packed_register_write_keeps_updated_state(self):
        source = self.computation_fixture("""
struct Packed = { payload : bits(64) }
register Extra : Packed
val updated : bits(64) -> bits(64)
function updated(value) = {
    Extra = struct { payload = value };
    Extra.payload
}
""", "updated(x)")
        text, deps = self.run_computation(source)
        self.assertIn("write reg_Extra", text)
        written = re.search(r"let (v[0-9]+) = \(write reg_Extra", text)
        self.assertIsNotNone(written, text)
        self.assertIn("read reg_Extra " + written.group(1), text)
        self.assertIn("inlined updated", deps)

    def test_arm_fpsr_write_exclusion_retains_reads_and_other_writes(self):
        for declaration, target, read_value in (
                ("register FPSR : bits(64)", "FPSR", "FPSR"),
                ("struct Packed = { bits : bits(64) }\nregister FPSR : Packed",
                 "FPSR", "FPSR.bits"),
                ("struct Packed = { bits : bits(64) }\nregister FPSR : Packed",
                 "FPSR.bits", "FPSR.bits")):
            with self.subTest(target=target, declaration=declaration):
                value = ("struct { bits = value(x) }"
                         if target == "FPSR" and "Packed" in declaration
                         else "value(x)")
                source = self.computation_fixture(declaration + """
val value : bits(64) -> bits(64)
function value(x) = { X_set(1,64,x); x + x }
val updated : bits(64) -> bits(64)
function updated(x) = {
    """ + target + " = " + value + ";\n    " + read_value + """
}
""", "updated(x)")
                text, deps = self.run_computation(source)
                self.assertNotIn("write reg_FPSR", text)
                self.assertIn("read reg_FPSR", text)
                self.assertIn("word_add", text)
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertIn("primitive-contract Arm-FPSR-write-exclusion", deps)
                self.assertIn("inlined value", deps)
                failed, failed_deps = self.run_computation(
                    source.replace("X_set(1,64,x); x + x", "assert(false); x"))
                self.assert_failed_relation(failed, failed_deps)
                self.assertNotIn("write reg_FPSR", failed)
                self.assertNotIn("write (XREG", failed)
                unknown = source.replace("X_set(1,64,x); x + x", "unknown(); x")
                unknown = unknown.replace("val value :",
                    'val unknown = impure "unknown" : unit -> unit\nval value :')
                self.run_computation(unknown, error="unsupported primitive unknown")
                choice, choice_deps = self.run_computation(
                    source.replace("X_set(1,64,x); x + x",
                                   "undefined : bits(64)"))
                self.assert_existential_choice(choice, choice_deps, "64 word")
                self.assertNotIn("write reg_FPSR", choice)
                self.assertIn("read reg_FPSR", choice)
                self.assertIn("Arm-FPSR-write-exclusion", choice_deps)

    def test_arm_fpsr_range_exclusion_retains_selector_and_value_effects(self):
        source = self.computation_fixture("""
struct Packed = { bits : bits(64) }
register FPSR : Packed
val high : unit -> int(27)
function high() = { X_set(1,64,0x0000000000000001); 27 }
val low : unit -> int(27)
function low() = { X_set(2,64,0x0000000000000002); 27 }
val bit_value : bits(64) -> bits(1)
function bit_value(x) = { X_set(3,64,x); 0b1 }
val updated : bits(64) -> bits(64)
function updated(x) = {
    FPSR.bits[high() .. low()] = bit_value(x);
    FPSR.bits
}
""", "updated(x)")
        text, deps = self.run_computation(source)
        self.assertNotIn("write reg_FPSR", text)
        self.assertIn("read reg_FPSR", text)
        writes = [self.constant_register_write_positions(text, index)
                  for index in (1, 2, 3)]
        self.assertTrue(all(len(positions) == 1 for positions in writes), text)
        positions = [positions[0] for positions in writes]
        self.assertEqual(positions, sorted(positions), text)
        self.assertEqual(text.count("write (XREG"), 4)
        self.assertIn("primitive-contract Arm-FPSR-write-exclusion", deps)
        # The packed range replacement itself reads the original FPSR.
        # Preserve that read even when no subsequent expression uses FPSR.
        text, deps = self.run_computation(source.replace("    FPSR.bits\n", "    x\n"))
        self.assertIn("read reg_FPSR", text)
        self.assertIn("word_insert", text)
        self.assertNotIn("write reg_FPSR", text)
        self.assertEqual(text.count("write (XREG"), 4)
        self.run_computation(source.replace("bits(64) }\nregister FPSR", "bits(32) }\nregister FPSR")
                             .replace("    FPSR.bits\n", "    sail_zero_extend(FPSR.bits,64)\n"),
                             error="declared 64-bit container")

    def test_fpsr_exclusion_is_specific_to_declared_arm_state_register(self):
        source = HEADER + """
register FPSR : bits(64)
val ROOT : bits(64) -> unit
function ROOT(x) = FPSR = x
"""
        text, deps = self.run_computation(source)
        self.assertNotIn("write reg_FPSR", text)
        self.assertIn("Arm-FPSR-write-exclusion", deps)
        text, deps = self.run_computation(source, architecture="rv32")
        self.assertIn("write reg_FPSR", text)
        self.assertNotIn("Arm-FPSR-write-exclusion", deps)
        text, deps = self.run_computation(source.replace("FPSR", "Other"))
        self.assertIn("write reg_Other", text)
        self.assertNotIn("Arm-FPSR-write-exclusion", deps)
        local = self.computation_fixture("""
val local_value : bits(64) -> bits(64)
function local_value(x) = { FPSR : bits(64) = x; FPSR = x + x; FPSR }
""", "local_value(x)")
        text, deps = self.run_computation(local)
        self.assertIn("word_add", text)
        self.assertNotIn("Arm-FPSR-write-exclusion", deps)

    def test_arm_btype_exclusion_retains_reads_value_effects_and_checks(self):
        for name, typ, value in (
                ("BTypeNext", "bits(2)", "0b01"),
                ("BTypeCompatible", "bool", "true")):
            source = self.computation_fixture("""
register """ + name + " : " + typ + """
val value : bits(64) -> """ + typ + """
function value(x) = { X_set(1,64,x); """ + value + """ }
val updated : bits(64) -> bits(64)
function updated(x) = {
    """ + name + """ = value(x);
    if """ + name + " == " + value + """ then x + x else x
}
""", "updated(x)")
            with self.subTest(register=name):
                text, deps = self.run_computation(source, with_sources=True)
                self.assertNotIn("write reg_" + name, text)
                self.assertIn("read reg_" + name, text)
                self.assertIn("word_add", text)
                self.assertEqual(text.count("write (XREG"), 2)
                self.assertIn("primitive-contract Arm-BType-write-exclusion", deps)
                self.assertIn("branch-protection behavior", text)
                self.assertIn("inlined value", deps)
                failed, failed_deps = self.run_computation(
                    source.replace("X_set(1,64,x);", "assert(false);"))
                self.assert_failed_relation(failed, failed_deps)
                self.assertNotIn("write reg_" + name, failed)
                self.assertNotIn("write (XREG", failed)
                choice, choice_deps = self.run_computation(
                    source.replace("X_set(1,64,x); " + value,
                                   "undefined : " + typ))
                self.assert_existential_choice(
                    choice, choice_deps, "2 word" if typ == "bits(2)" else "bool")
                self.assertNotIn("write reg_" + name, choice)
                self.assertIn("read reg_" + name, choice)
                self.assertIn("Arm-BType-write-exclusion", choice_deps)

    def test_btype_exclusion_is_specific_to_declared_arm_register_types(self):
        for name, typ, value, wrong in (
                ("BTypeNext", "bits(2)", "0b01", "bits(3)"),
                ("BTypeCompatible", "bool", "true", "bits(1)")):
            source = HEADER + f"""
register {name} : {typ}
val ROOT : unit -> unit
function ROOT() = {name} = {value}
"""
            with self.subTest(register=name):
                text, deps = self.run_computation(source)
                self.assertNotIn("write reg_" + name, text)
                self.assertIn("Arm-BType-write-exclusion", deps)
                text, deps = self.run_computation(source, architecture="rv32")
                self.assertIn("write reg_" + name, text)
                self.assertNotIn("Arm-BType-write-exclusion", deps)
                other, deps = self.run_computation(source.replace(name, "Other"))
                self.assertIn("write reg_Other", other)
                self.assertNotIn("Arm-BType-write-exclusion", deps)
                bad_value = "0b001" if name == "BTypeNext" else "0b1"
                self.run_computation(
                    source.replace(typ, wrong).replace(value, bad_value),
                    error="write exclusion requires its declared")
                local = self.computation_fixture(f"""
val local_value : bits(64) -> bits(64)
function local_value(x) = {{
    {name} : {typ} = {value};
    {name} = {value};
    if {name} == {value} then x + x else x
}}
""", "local_value(x)")
                text, deps = self.run_computation(local)
                self.assertIn("word_add", text)
                self.assertNotIn("Arm-BType-write-exclusion", deps)

    @staticmethod
    def sail_string_literal(value):
        # Decimal byte escapes avoid dependence on the terminal's encoding.
        return '"' + "".join(f"\\{byte:03d}" for byte in value) + '"'

    def string_lookup_fixture(self, query, helper="", default="assert(false); false"):
        return self.computation_fixture(helper + """
val lookup : string -> bool
function lookup(query) = {
    if query == "enabled" then true
    else if query == "disabled" then false
    else { """ + default + """ }
}
val checked : bits(64) -> bits(64)
function checked(x) =
    if lookup(""" + query + """) then x + x else x
""", "checked(x)")

    def test_string_literal_lookup_uses_exact_bytes(self):
        for query, enabled in ((b"enabled", True), (b"disabled", False)):
            with self.subTest(query=query):
                text, deps = self.run_computation(
                    self.string_lookup_fixture(self.sail_string_literal(query)))
                self.assertEqual("word_add" in text, enabled)
                self.assertIn("inlined lookup", deps)
                self.assertIn("primitive-contract eq_string", deps)
        for query in (b"Enabled", b"enabled ", b"enabled\x00", b""):
            with self.subTest(query=query):
                failed, failed_deps = self.run_computation(
                    self.string_lookup_fixture(self.sail_string_literal(query)))
                self.assert_failed_relation(failed, failed_deps)
                self.assertNotIn("write (XREG", failed)

    def test_string_literal_escaping_preserves_actual_hol_character_codes(self):
        for value in (
                b"", b"A", b"\x01", b"\x80", b"\xff",
                b'quote" slash\\ tick` newline\n nul\x00',
                "éλ".encode("utf-8"), bytes(range(256))):
            with self.subTest(value=value):
                source = """
val ROOT : unit -> bits(8)
function ROOT() = {
    let text = """ + self.sail_string_literal(value) + """;
    0x00
}
"""
                text, _ = self.run_sail(source, roots=("ROOT",))
                # HOL's ASCII constructor takes the most significant bit
                # first: byte65 is ASCII F T F F F F F T, not byte130.
                characters = re.findall(
                    r"\bASCII\s+((?:[TF]\s+){7}[TF])\b", text)
                decoded = bytes(sum(
                    (bit == "T") << (7 - index)
                    for index, bit in enumerate(character.split()))
                    for character in characters)
                self.assertEqual(decoded, value)
                self.assertEqual(text.count("`"), 2)
                self.assertNotIn("\x00", text)
                self.assertIn("char list", text)

    def test_defined_string_helper_keeps_its_answer_and_effects(self):
        source = self.computation_fixture("""
val ImpDefBool : string -> bool
function ImpDefBool(query) =
    if query == "known" then true else { assert(false); false }
val checked : bits(64) -> bits(64)
function checked(x) = if ImpDefBool("known") then x + x else x
""", "checked(x)")
        original, deps = self.run_computation(source)
        changed, changed_deps = self.run_computation(
            source.replace('query == "known" then true', 'query == "known" then false'))
        self.assertIn("word_add", original)
        self.assertNotIn("word_add", changed)
        self.assertNotEqual(original, changed)
        self.assertIn("inlined ImpDefBool", deps)
        self.assertIn("inlined ImpDefBool", changed_deps)
        written, written_deps = self.run_computation(
            source.replace('query == "known" then true', 'query == "known" then { X_set(1,64,0x0000000000000001); true }'))
        self.assertEqual(len(self.constant_register_write_positions(written, 1)), 1)
        self.assertIn("inlined ImpDefBool", written_deps)
        self.assertNotIn("primitive-contract ImpDefBool", written_deps)

    def test_string_lookup_retains_failed_default_and_refuses_unknown_effects(self):
        failed, failed_deps = self.run_computation(
            self.string_lookup_fixture('"unknown"', default="assert(false); false"))
        self.assert_failed_relation(failed, failed_deps)
        self.assertNotIn("write (XREG", failed)
        self.run_computation(
            self.string_lookup_fixture(
                '"unknown"', 'val opaque = impure "opaque" : unit -> bool\n',
                default="opaque()"),
            error="unsupported primitive opaque")
        source = self.string_lookup_fixture(
            "unknown(x)",
            'val unknown = impure "unknown" : bits(64) -> string\n')
        self.run_computation(source, error='unsupported primitive unknown')

    def test_string_equality_keeps_argument_effects_in_source_order(self):
        source = self.computation_fixture("""
val left : bits(64) -> string
function left(x) = { X_set(0,64,x); "enabled" }
val right : bits(64) -> string
function right(x) = { X_set(1,64,x); "enabled" }
val checked : bits(64) -> bits(64)
function checked(x) = if left(x) == right(x) then x + x else x
""", "checked(x)")
        text, deps = self.run_computation(source)
        left = self.constant_register_write_positions(text, 0)
        right = self.constant_register_write_positions(text, 1)
        self.assertEqual(len(left), 1)
        self.assertEqual(len(right), 1)
        self.assertLess(left[0], right[0])
        self.assertIn("word_add", text)
        self.assertIn("inlined left", deps)
        self.assertIn("inlined right", deps)
        unequal, _ = self.run_computation(
            source.replace('X_set(1,64,x); "enabled"', 'X_set(1,64,x); "disabled"'))
        self.assertNotIn("word_add", unequal)
        self.assertEqual(len(self.constant_register_write_positions(unequal, 0)), 1)
        self.assertEqual(len(self.constant_register_write_positions(unequal, 1)), 1)

    def test_string_equality_retains_defined_same_named_helper(self):
        source = self.computation_fixture("""
val eq_string : (string,string) -> bool
function eq_string(left,right) = {
    X_set(1,64,0x0000000000000001);
    false
}
val checked : bits(64) -> bits(64)
function checked(x) = if eq_string("same","same") then x + x else x
""", "checked(x)").replace(
            "$include <prelude.sail>",
            "$include <flow.sail>\n$include <vector.sail>\n"
            "$include <arith.sail>")
        text, deps = self.run_computation(source)
        self.assertNotIn("word_add", text)
        self.assertEqual(len(self.constant_register_write_positions(text, 1)), 1)
        self.assertIn("inlined eq_string", deps)
        self.assertNotIn("primitive-contract eq_string", deps)

    def test_string_equality_requires_its_checked_pure_signature(self):
        for declaration, arguments, diagnostic in (
                ('val eq_string = impure "foreign_eq" : (string,string) -> bool',
                 '"same","same"',
                 "stateless operations require a pure external declaration"),
                ('val eq_string = pure "foreign_eq" : (bits(64),bits(64)) -> bool',
                 "x,x", "string equality requires"),
                ('val eq_string = pure "foreign_eq" : string -> bool',
                 '"same"', "unsupported primitive eq_string")):
            with self.subTest(declaration=declaration):
                # Do not include string.sail: its pure eq_string declaration
                # would conflict with the deliberately foreign signature.
                source = """default Order dec
type bits('n) = bitvector('n)
""" + declaration + """
register Result : bool
val ROOT : bits(64) -> unit
function ROOT(x) = Result = eq_string(""" + arguments + """)
"""
                self.run_computation(source, error=diagnostic)

    def test_stateless_primitives_reject_impure_external_declarations(self):
        # Do not include standard libraries: each declaration intentionally
        # changes a supported primitive's effects, not its operand types.
        header = """default Order dec
type bits('n) = bitvector('n)
val eq_int = pure "eq_int" : (int,int) -> bool
"""
        for name, signature, arguments, result in (
                ("abs_int_plain", "int -> int", "3", 3),
                ("add_int", "(int,int) -> int", "3,1", 4),
                ("eq_bits", "(bits(64),bits(64)) -> bool",
                 "0x0000000000000001,0x0000000000000001", None),
                ("not_bool", "bool -> bool", "false", None),
                ("bitvector_length", "bits(64) -> int",
                 "0x0000000000000001", 64)):
            expression = f"{name}({arguments})"
            if result is not None:
                expression = f"eq_int({expression},{result})"
            for purity in ("pure", "impure"):
                with self.subTest(primitive=name, purity=purity):
                    source = header + f"""
register Result : bool
val {name} = {purity} "foreign_{name}" : {signature}
val ROOT : unit -> unit
function ROOT() = Result = {expression}
"""
                    self.run_computation(
                        source,
                        error='stateless operations require a pure external declaration' if purity == 'impure' else None)

    def test_finite_mapping_bodies_do_not_require_external_purity_records(self):
        source = """default Order dec
type bits('n) = bitvector('n)
mapping bool_bit : bool <-> bits(1) = {
    true <-> 0b1,
    false <-> 0b0
}
register Flag : bool
register Result : bool
register BitResult : bits(1)
val ROOT : bits(1) -> unit
function ROOT(x) = {
    Result = bool_bit(x);
    BitResult = bool_bit(Flag)
}
"""
        text, dependencies = self.run_computation(source)
        self.assertIn("write reg_Result", text)
        self.assertIn("write reg_BitResult", text)
        self.assertIn("inlined-mapping bool_bit backwards", dependencies)
        self.assertIn("inlined-mapping bool_bit forwards", dependencies)
        self.assertNotIn("primitive-contract bool_bit", dependencies)

    def test_string_condition_survives_integer_bounds_normalization(self):
        # The unrestricted modulus signature lets the exporter check the
        # nonnegative dividend itself. Its arithmetic equality key traverses
        # an integer helper whose condition contains an actual string
        # literal and a symbolic string parameter.
        source = """default Order dec
type bits('n) = bitvector('n)
val eq_string = pure "eq_string" : (string,string) -> bool
val unsigned = pure "unsigned" : bits(64) -> int
val sub_int = pure "sub_int" : (int,int) -> int
val mult_int = pure "mult_int" : (int,int) -> int
val ediv_int = pure "ediv_int" : (int,int) -> int
val emod_nat = pure "emod_nat" : (int,int) -> int
val get_slice_int = pure "slice" : (int(64),int,int(0)) -> bits(64)
val selected : (string,int) -> int
function selected(label,n) =
    if eq_string(label,"positive") then n else sub_int(0,n)
val wrapped : int -> int
function wrapped(n) = {
    let q = ediv_int(n,64);
    sub_int(n,mult_int(64,q))
}
val ROOT : (string,bits(64)) -> bits(64)
function ROOT(label,x) =
    get_slice_int(64,emod_nat(wrapped(selected(label,unsigned(x))),7),0)
"""
        text, deps = self.run_sail(source, roots=("ROOT",))
        self.assertIn("if ", text)
        self.assertIn("ASCII", text)
        self.assertIn(" div ", text)
        self.assertIn("inlined selected", deps)
        self.assertIn("inlined wrapped", deps)
        self.assertIn("primitive-contract eq_string", deps)
        self.run_sail(
            source.replace("sub_int(n,mult_int(64,q))",
                           "sub_int(n,mult_int(63,q))"),
            roots=("ROOT",), error="proved nonnegative dividend")

    def test_record_projection_evaluates_effectful_base_once(self):
        source = self.computation_fixture("""
struct Packed = { bits : bits(64) }
register Extra : Packed
val produced : bits(64) -> Packed
function produced(x) = {
    X_set(0,64,x);
    Extra = struct { bits = x + x };
    Extra
}
""", "produced(x).bits")
        text, deps = self.run_computation(source)
        self.assertEqual(len(self.constant_register_write_positions(text, 0)), 1)
        writes = re.findall(r"let (v[0-9]+) = \(write reg_Extra", text)
        self.assertEqual(len(writes), 1)
        self.assertIn("read reg_Extra " + writes[0], text)
        self.assertIn("word_add", text)
        self.assertIn("inlined produced", deps)

    def test_record_construction_keeps_source_field_order(self):
        source = self.computation_fixture("""
struct Pair = { first : bits(64), second : bits(64) }
register Seen : bits(64)
val first : bits(64) -> bits(64)
function first(x) = { X_set(0,64,x); Seen }
val second : bits(64) -> bits(64)
function second(x) = { X_set(1,64,x); Seen = x + x; x }
val produced : bits(64) -> Pair
function produced(x) = struct { second = second(x), first = first(x) }
""", "produced(x).first")
        text, deps = self.run_computation(source)
        first = self.constant_register_write_positions(text, 0)
        second = self.constant_register_write_positions(text, 1)
        self.assertEqual(len(first), 1)
        self.assertEqual(len(second), 1)
        self.assertLess(second[0], first[0])
        writes = re.findall(r"let (v[0-9]+) = \(write reg_Seen", text)
        self.assertEqual(len(writes), 1)
        # first() also writes XREG0 before reading Seen. Its write must take
        # the state produced by second(), and its read must take that newer
        # state rather than the state before either helper ran.
        _, second_state, second_arguments = self.shared_result(text, "second")
        _, _, first_arguments = self.shared_result(text, "first")
        self.assertTrue(second_arguments.endswith(" entry s"), text)
        self.assertTrue(first_arguments.endswith(" entry " + second_state), text)
        first_worker = self.shared_name(text, "first")
        first_body = text.split("let " + first_worker + " = new_definition", 1)[1]
        first_body = first_body.split("`;;", 1)[0]
        first_written = re.search(
            r"let (v[0-9]+) = \(write \(XREG \(num_of_int \(+& 0\b"
            r"[^\n]+ s\) in", first_body)
        self.assertIsNotNone(first_written, text)
        self.assertIn("read reg_Seen " + first_written.group(1), first_body)
        self.assertIn("FST", text)
        self.assertIn("inlined first", deps)
        self.assertIn("inlined second", deps)

    def test_record_projection_keeps_unused_field_effects_and_failures(self):
        helper = """
struct Pair = { first : bits(64), second : bits(64) }
val unused : bits(64) -> bits(64)
function unused(x) = { X_set(0,64,x); x + x }
val produced : bits(64) -> Pair
function produced(x) = struct { first = x, second = unused(x) }
"""
        source = self.computation_fixture(helper, "produced(x).first")
        text, deps = self.run_computation(source)
        self.assertEqual(len(self.constant_register_write_positions(text, 0)), 1)
        self.assertIn("word_add", text)
        self.assertIn("inlined unused", deps)
        failed, failed_deps = self.run_computation(
            source.replace('X_set(0,64,x); x + x', 'assert(false); x'))
        self.assert_failed_relation(failed, failed_deps)
        self.assertNotIn("write (XREG", failed)
        self.run_computation(
            source.replace(
                "val unused : bits(64) -> bits(64)\n"
                "function unused(x) = { X_set(0,64,x); x + x }",
                'val unused = impure "opaque" : bits(64) -> bits(64)'),
            error="unsupported primitive unused")

    def test_record_field_return_keeps_direct_and_callee_scopes(self):
        helper = """
struct Pair = { first : bits(64), second : bits(64) }
val later : bits(64) -> bits(64)
function later(x) = { X_set(1,64,x); x }
val produced : bits(64) -> Pair
function produced(x) = {
    let packed : Pair = struct {
        first = ({ X_set(0,64,x);
                   return(struct { first = x, second = x }); x }),
        second = later(x)
    };
    X_set(3,64,x);
    packed
}
"""
        text, deps = self.run_computation(
            self.computation_fixture(helper, 'produced(x).first'))
        self.assertEqual(len(self.constant_register_write_positions(text, 0)), 1)
        self.assertFalse(self.constant_register_write_positions(text, 1))
        self.assertFalse(self.constant_register_write_positions(text, 3))
        self.assertNotIn("inlined later", deps)
        callee = helper.replace(
            "val produced : bits(64) -> Pair",
            """
val early : bits(64) -> bits(64)
function early(x) = { X_set(0,64,x); return(x); X_set(2,64,x); x }
val produced : bits(64) -> Pair""").replace(
                "({ X_set(0,64,x);\n"
                "                   return(struct { first = x, second = x }); x })",
                "early(x)")
        text, deps = self.run_computation(
            self.computation_fixture(callee, 'produced(x).first'))
        positions = [
            self.constant_register_write_positions(text, index)
            for index in (0, 1, 3)]
        self.assertTrue(all(len(position) == 1 for position in positions))
        self.assertEqual([position[0] for position in positions],
                         sorted(position[0] for position in positions))
        self.assertFalse(self.constant_register_write_positions(text, 2))
        self.assertIn("inlined early", deps)
        self.assertIn("inlined later", deps)

    def test_mutable_single_field_record_preserves_mask_and_effects(self):
        source = self.computation_fixture("""
struct Packed = { bits : bits(64) }
val normalized : Packed -> Packed
function normalized(value) = {
    tmp : Packed = value;
    tmp = struct { bits = tmp.bits & 0xffffffffffffff00 };
    X_set(0,64,tmp.bits);
    tmp
}
""", "normalized(struct { bits = x }).bits")
        text, deps = self.run_computation(source)
        self.assertIn("word_and", text)
        self.assertIn("word 18446744073709551360", text)
        self.assertEqual(len(self.constant_register_write_positions(text, 0)), 1)
        self.assertIn("inlined normalized", deps)
        changed, _ = self.run_computation(
            source.replace('0xffffffffffffff00', '0xffffffffffffffff'))
        self.assertNotEqual(text, changed)
        self.assertIn("word 18446744073709551615", changed)

    def test_record_construction_does_not_manufacture_uninitialized_fields(self):
        source = self.computation_fixture("""
struct Pair = { first : bits(64), second : bits(64) }
val produced : bits(64) -> Pair
function produced(x) = {
    missing : bits(64) = undefined;
    struct { first = x, second = missing }
}
""", "produced(x).first")
        diagnostic = self.run_computation(source, error='HOL Light:')
        self.assertRegex(diagnostic, r"undefined local|uninitialized bits")

    def test_record_construction_still_refuses_projected_pstate(self):
        source = self.computation_fixture("""
struct ProcState = {
    N : bits(1), Z : bits(1), C : bits(1), V : bits(1),
    EL : bits(2), BTYPE : bits(2), nRW : bits(1), SM : bits(1)
}
val produced : bits(64) -> bits(64)
function produced(x) = {
    let ignored : ProcState = struct {
        N = 0b0, Z = 0b0, C = 0b0, V = 0b0,
        EL = 0b00, BTYPE = 0b00, nRW = 0b0, SM = 0b0
    };
    x
}
""", "produced(x)")
        self.run_computation(
            source,
            architecture='aarch64',
            error='projected upstream records require an explicit construction contract')

    def test_dynamic_local_range_write_keeps_all_legal_lanes(self):
        source = self.computation_fixture("""
val inserted : (bits(64),bits(3)) -> bits(64)
function inserted(x,lane) = {
    let 'e = unsigned(lane);
    out : bits(64) = x;
    out[e*8+7 .. e*8] = x[7..0];
    out
}
""", "inserted(x,d[2..0])")
        text, _ = self.run_computation(source)
        self.assertIn("word_insert", text)
        self.assertIn("num_of_int", text)
        self.run_computation(
            source.replace('bits(3)', 'bits(4)').replace('d[2..0]', 'd[3..0]'),
            error='Failed to prove constraint')

    def test_dynamic_range_write_refuses_unknown_base_or_inserted_bits(self):
        source = self.computation_fixture("""
val inserted : (bits(64),bits(3)) -> bits(64)
function inserted(x,lane) = {
    let 'e = unsigned(lane);
    out : bits(64) = undefined;
    out[e*8+7 .. e*8] = x[7..0];
    out
}
""", "inserted(x,d[2..0])")
        self.run_computation(source, error='fully initialized')
        self.run_computation(
            source.replace('out : bits(64) = undefined;', 'out : bits(64) = x; byte : bits(8) = undefined;').replace('= x[7..0]', '= byte'),
            error='fully initialized')

    def test_range_selectors_run_before_rhs_and_keep_helper_writes(self):
        source = self.computation_fixture("""
val high : unit -> int(15)
function high() = { X_set(1,64,0x0000000000000001); 15 }
val low : unit -> int(8)
function low() = { X_set(2,64,0x0000000000000002); 8 }
val byte : bits(64) -> bits(8)
function byte(x) = { X_set(3,64,0x0000000000000003); x[7..0] }
val inserted : bits(64) -> bits(64)
function inserted(x) = {
    out : bits(64) = x;
    out[high() .. low()] = byte(x);
    out
}
""", "inserted(x)")
        text, deps = self.run_computation(source)
        writes = [self.constant_register_write_positions(text, index)
                  for index in (1, 2, 3)]
        self.assertTrue(all(len(positions) == 1 for positions in writes), text)
        positions = [positions[0] for positions in writes]
        self.assertEqual(positions, sorted(positions), text)
        self.assertEqual(text.count("write (XREG"), 4)
        for helper in ("high", "low", "byte", "inserted"):
            self.assertIn("inlined " + helper, deps)

    def test_packed_register_range_write_reads_and_updates_current_state(self):
        source = self.computation_fixture("""
struct Packed = { bits : bits(32) }
register Extra : Packed
val updated : bits(64) -> bits(64)
function updated(x) = {
    Extra.bits[27..27] = 0b1;
    Extra.bits[26..26] = 0b1;
    sail_zero_extend(Extra.bits,64)
}
""", "updated(x)")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write reg_Extra"), 2)
        self.assertEqual(text.count("word_insert"), 2)
        self.assertIn("typed-packed-register-field-write", deps)
        writes = re.findall(r"let (v[0-9]+) = \(write reg_Extra", text)
        self.assertEqual(len(writes), 2, text)
        self.assertIn("read reg_Extra " + writes[0], text)
        self.assertIn("read reg_Extra " + writes[1], text)
        self.run_computation(
            source.replace('struct Packed = { bits : bits(32) }', 'struct Packed = { bits : bits(32), other : bool }'),
            error='sole declared packed register field')

    def test_mutable_vector_index_retains_initial_and_remainder_bounds(self):
        source = self.vector_fixture("""
index : int = r;
V_set(index,128,V_read(index,128));
foreach (i from 0 to 2 by 1 in inc) {
    index = emod_nat(index + 1,32);
    V_set(index,128,V_read(index,128))
}
""", 'val emod_nat = pure "emod_nat" : (int,int) -> int\n')
        text, deps = self.run_computation(source)
        self.assertIn(" rem ", text)
        self.assertEqual(text.count("write (QREG"), 4)
        self.assertIn("unrolled-static-loop", deps)
        self.run_computation(
            source.replace('index : int = r', 'index : int = 32'),
            error='index is not proved in 0..31')
        self.run_computation(
            source.replace('index + 1,32', 'index + 1,33'),
            error='index is not proved in 0..31')

    def test_loop_index_interval_join_does_not_ignore_an_unbounded_exit(self):
        source = self.vector_fixture("""
index : int = r;
foreach (i from 0 to 1 by 1 in inc) {
    if x[0..0] == 0b1 then index = emod_nat(index + 1,32)
    else index = unsigned(x);
    V_set(index,128,V_read(index,128))
}
""", 'val emod_nat = pure "emod_nat" : (int,int) -> int\n')
        self.run_computation(source, error='index is not proved in 0..31')

    def dynamic_mask_fixture(self, body="sail_ones(n)"):
        return self.computation_fixture("""
val ZeroExtend0 = pure "zero_extend" : forall 'n 'm,
  'n >= 0 & 'm >= 'n. (bits('n),int('m)) -> bits('m)
val mask : forall 'n, 0 <= 'n & 'n <= 64. int('n) -> bits('n)
function mask(n) = """ + body + """
val extended : bits(64) -> bits(64)
function extended(x) = ZeroExtend0(mask(unsigned(x[5..0]) + 1),64)
""", "extended(x)")

    def test_dynamic_ones_preserves_actual_helper_bodies_and_width(self):
        text, deps = self.run_computation(self.dynamic_mask_fixture())
        self.assertIn("int#num", text)
        self.assertIn("FST", text)
        self.assertIn("SND", text)
        self.assertIn(" EXP ", text)
        self.assertIn("inlined sail_ones", deps)
        self.assertIn("checked-dynamic-bit-zeros", deps)
        self.assertIn("checked-dynamic-bit-complement", deps)
        self.assertIn("checked-dynamic-zero-extension", deps)
        zero, changed_deps = self.run_computation(
            self.dynamic_mask_fixture('sail_zeros(n)'))
        self.assertNotEqual(text, zero)
        self.assertNotIn("checked-dynamic-bit-complement", changed_deps)

    def test_dynamic_mask_helper_writes_are_not_erased(self):
        source = self.dynamic_mask_fixture(
            "{ X_set(1,64,0x0000000000000001); sail_ones(n) }")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined mask", deps)

    def test_dynamic_bits_refuse_unsupported_operations(self):
        self.run_computation(
            self.dynamic_mask_fixture('sail_zeros(n) + sail_zeros(n)'),
            error='unsupported primitive on internal dynamic bitvectors')
        source = self.dynamic_mask_fixture().replace(
            "x[5..0]", "x[6..0]").replace("'n <= 64", "'n <= 128")
        self.run_computation(source, error='Could not resolve quantifiers')

    def test_single_dynamic_replication_keeps_original_mask_body(self):
        source = self.dynamic_mask_fixture("replicate_bits(sail_ones(n),1)")
        text, deps = self.run_computation(source)
        self.assertIn("inlined sail_ones", deps)
        self.assertIn("primitive-contract replicate_bits", deps)
        self.assertIn("checked-dynamic-single-replication", deps)
        self.assertIn(" EXP ", text)
        self.assertNotIn("word_duplicate", text)

    def test_multiple_dynamic_replication_remains_rejected(self):
        source = self.dynamic_mask_fixture(
            "replicate_bits(sail_ones(n),2)").replace(
                "x[5..0]", "x[4..0]").replace(
                    "'n <= 64", "'n <= 32").replace(
                        "int('n) -> bits('n)", "int('n) -> bits(2 * 'n)")
        self.run_computation(
            source,
            error='positive static count and its exact word width')

    def test_dynamic_bits_cannot_be_register_components(self):
        source = HEADER + """
register Extra : bits('width)
val ROOT : unit -> unit
function ROOT() = Extra = Extra
"""
        # A runtime-sized architectural register is not a supported Sail
        # declaration, rather than an invitation to widen the HOL interface.
        self.run_computation(source, error='Type error')

    def test_signed_mutable_shift_keeps_both_full_byte_domain_branches(self):
        source = self.computation_fixture("""
val checked : forall 'n. (int,int('n)) -> int
function checked(value,n) = { assert(n > 0); _shr_int_general(value,n) }
val shifted : bits(64) -> bits(64)
function shifted(x) = {
    amount : int = signed(x[7..0]);
    if amount >= 0 then get_slice_int(64,_shl_int_general(unsigned(x),amount),0)
    else {
        let 'positive = negate(amount);
        get_slice_int(64,checked(unsigned(x),positive),0)
    }
}
""", "shifted(x)")
        text, deps = self.run_computation(source)
        self.assertIn("if ", text)
        self.assertIn("ival", text)
        self.assertIn(" div ", text)
        self.assertIn("statically-proved-assertion", deps)
        bad = source.replace("if amount >= 0", "if x[0..0] == 0b1")
        guarded, guarded_deps = self.run_computation(bad)
        self.assert_guarded_relation(guarded, guarded_deps, "gt_int(n, 0)")
        self.assertIn("ival", guarded)
        self.assertIn(" div ", guarded)
        self.assertIn("EXP", guarded)

    def test_false_branch_shift_assertion_cannot_use_a_stale_local(self):
        source = self.computation_fixture("""
val shifted : bits(64) -> bits(64)
function shifted(x) = {
    amount : int = signed(x[7..0]);
    if amount >= ({ amount = 0; 0 }) then x
    else { assert(negate(amount) > 0); x }
}
""", "shifted(x)")
        text, deps = self.run_computation(source)
        self.assert_guarded_relation(text, deps, "gt_int(negate_atom(amount), 0)")
        self.assertIn("ival", text)
        self.assertIn("(& 0)", text)
        self.assertNotIn("statically-proved-assertion", deps)

    def test_defined_remainder_body_retains_math_and_bounds(self):
        source = self.vector_fixture("""
index : int = r;
foreach (i from 0 to 2 by 1 in inc) {
    index = wrapped(index+1,32);
    V_set(index,128,V_read(index,128))
}
""", """
val wrapped : (int,int) -> int
function wrapped(n,m) = { let q = tdiv_int(n,m); n - m*q }
""")
        text, deps = self.run_computation(source)
        self.assertIn("inlined wrapped", deps)
        self.assertIn(" div ", text)
        self.assertNotIn(" rem ", text)
        self.assertEqual(text.count("write (QREG"), 3)
        for change in ("n - m*q + 1", "n - m*(q-1)"):
            with self.subTest(change=change):
                self.run_computation(
                    source.replace('n - m*q', change),
                    error='index is not proved in 0..31')
        self.run_computation(
            source.replace('index+1,32', 'index+1,33'),
            error='index is not proved in 0..31')

    def test_truncating_division_keeps_signed_rounding_and_checks_zero(self):
        source = self.computation_fixture("", "get_slice_int(64,tdiv_int(signed(x),3),0)")
        text, _ = self.run_computation(source)
        self.assertNotIn(" quot ", text)
        self.assertIn(" div ", text)
        self.assertRegex(text, r"if .* < \(& 0\)\) then \(--")
        for divisor in ("0", "negate(3)"):
            with self.subTest(divisor=divisor):
                self.run_computation(
                    source.replace('signed(x),3', 'signed(x),' + divisor),
                    error='proved positive divisor')

    def test_euclidean_division_uses_floor_and_checks_positive_divisor(self):
        source = self.computation_fixture("""
val ediv_int = pure "ediv_int" : (int,int) -> int
""", "get_slice_int(64,ediv_int(signed(x),3),0)")
        text, deps = self.run_computation(source)
        self.assertIn(" div ", text)
        self.assertNotIn(" quot ", text)
        self.assertIn("primitive-contract ediv_int", deps)
        for divisor in ("0", "negate(3)", "signed(x)"):
            with self.subTest(divisor=divisor):
                self.run_computation(
                    source.replace('signed(x),3', 'signed(x),' + divisor),
                    error='proved positive divisor')

    def test_nonnegative_quotient_remainder_names_keep_domain_and_effects(self):
        for name, operation in (("quot_positive_round_zero", "div"),
                                ("rem_positive_round_zero", "rem")):
            with self.subTest(name=name):
                source = f"""
register D : bits(64)
register Side : bits(8)
val {name} = pure "{name}" : (int,int) -> int
val value : unit -> int
function value() = {{ Side = 0x11; 8 }}
val ROOT : unit -> unit
function ROOT() = D = get_slice_int(64,{name}(value(),2),0)
"""
                text, deps = self.run_computation(source)
                self.assertIn(" " + operation + " ", text)
                self.assertIn("primitive-contract " + name, deps)
                self.assertLess(text.index("write reg_Side"), text.index("write reg_D"))
                for arguments, diagnostic in (
                        ("negate(1),2", "proved nonnegative dividend"),
                        ("8,0", "proved positive divisor"),
                        ("8,negate(2)", "proved positive divisor")):
                    self.run_computation(
                        source.replace("value(),2", arguments), error=diagnostic)
                self.run_computation(
                    source.replace('= pure "' + name + '"', '= impure "' + name + '"'),
                    error="stateless operations require a pure external declaration")
                self.run_computation(f"""
register D : bool
val {name} = pure "{name}" : (int,int) -> bool
val ROOT : unit -> unit
function ROOT() = D = {name}(8,2)
""", error="require integer arguments and result")
                defined = source.replace(
                    f'val {name} = pure "{name}" : (int,int) -> int',
                    f'val {name} : (int,int) -> int\n'
                    f'function {name}(n,d) = {{ Side = 0x22; n+d }}')
                actual, actual_deps = self.run_computation(defined)
                self.assertIn("inlined " + name, actual_deps)
                self.assertNotIn("primitive-contract " + name, actual_deps)
                self.assertIn("write reg_Side", actual)
                self.assertNotIn(" " + operation + " ", actual)

    def test_defined_euclidean_name_retains_body_and_effects(self):
        source = self.computation_fixture("""
val x_mask : unit -> bits(64)
function x_mask() = 0xffffffffffffffff
val ediv_int : (int,int) -> int
function ediv_int(n,m) = { X_set(1,64,x_mask()); n+m }
""", "get_slice_int(64,ediv_int(signed(x),3),0)")
        text, deps = self.run_computation(source)
        self.assertIn("inlined ediv_int", deps)
        self.assertNotIn("primitive-contract ediv_int", deps)
        self.assertIn("write (XREG", text)
        self.assertIn(" + ", text)
        self.assertNotIn(" div ", text)

    def test_false_specialized_helper_assertion_has_no_normal_state(self):
        source = self.computation_fixture("""
val checked : forall 'N, 'N >= 0. bits('N) -> bits('N)
function checked(x) = { assert(constraint('N > 128)); x }
""", "x + checked(x)")
        text, deps = self.run_computation(source)
        self.assert_guarded_relation(text, deps, "gt_int(bitvector_length(x), 128)")
        self.assertIn("(& 128)", text)
        self.assertNotIn("statically-proved-assertion", deps)

    def test_literal_boolean_parameter_selects_actual_helper_branch(self):
        source = self.computation_fixture("""
val opaque = pure "opaque" : bits(64) -> bits(64)
val selected : (bool, bits(64)) -> bits(64)
function selected(flag, x) = if flag then x else opaque(x)
""", "selected(true, x)")
        text, _ = self.run_computation(source)
        self.assertNotIn("opaque", text)
        self.run_computation(
            source.replace('selected(true, x)', 'selected(false, x)'),
            error='unsupported primitive opaque')

    def test_literal_word_equality_selects_actual_helper_branch(self):
        source = self.computation_fixture("""
val opaque = pure "opaque" : bits(64) -> bits(64)
val selected : (bits(1), bits(64)) -> bits(64)
function selected(op, x) = {
    let enabled = op == 0b1;
    if enabled then x else opaque(x)
}
""", "selected(0b1, x)")
        self.run_computation(source)
        self.run_computation(
            source.replace('selected(0b1, x)', 'selected(0b0, x)'),
            error='unsupported primitive opaque')

    def test_literal_enum_parameter_selects_actual_helper_branch(self):
        source = self.computation_fixture("""
enum choice = { Keep, Reject }
val opaque = pure "opaque" : bits(64) -> bits(64)
val selected : (choice, bits(64)) -> bits(64)
function selected(op, x) = match op {
    Keep => x,
    Reject => opaque(x)
}
""", "selected(Keep, x)")
        self.run_computation(source)
        self.run_computation(
            source.replace('selected(Keep, x)', 'selected(Reject, x)'),
            error='unsupported primitive opaque')

    def test_literal_bit_match_selects_only_the_actual_reachable_case(self):
        source = self.computation_fixture("""
val opaque = pure "opaque" : bits(64) -> bits(64)
val selected : (bits(2), bits(64)) -> bits(64)
function selected(op, x) = match op {
    0b00 => x + 1,
    0b01 => x,
    0b10 => x + 2,
    _ => opaque(x)
}
""", "selected(0b01, x)")
        text, dependencies = self.run_computation(source)
        self.assertIn("inlined selected", dependencies)
        self.assertNotIn("opaque", text)
        self.run_computation(
            source.replace('selected(0b01, x)', 'selected(0b11, x)'),
            error='unsupported primitive opaque')

    def test_literal_bit_match_retains_scrutinee_helper_state_effects(self):
        source = self.computation_fixture("""
val opaque = pure "opaque" : bits(64) -> bits(64)
val touched : bits(64) -> bits(2)
function touched(x) = { X_set(0,64,x); 0b01 }
val selected : (bits(2), bits(64)) -> bits(64)
function selected(op, x) = match op {
    0b00 => x + 1,
    0b01 => x,
    0b10 => x + 2,
    _ => opaque(x)
}
""", "selected(touched(x), x)")
        text, dependencies = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined touched", dependencies)
        self.assertNotIn("opaque", text)

    def test_dynamic_bit_match_cannot_discard_a_reachable_case(self):
        source = self.computation_fixture("""
val opaque = pure "opaque" : bits(64) -> bits(64)
val selected : (bits(2), bits(64)) -> bits(64)
function selected(op, x) = match op {
    0b00 => x + 1,
    0b01 => x,
    0b10 => x + 2,
    _ => opaque(x)
}
""", "selected(x[1..0], x)")
        self.run_computation(source, error='unsupported primitive opaque')

    def test_literal_bit_match_still_checks_all_case_patterns(self):
        source = self.computation_fixture("""
val selected : (bits(2), bits(64)) -> bits(64)
function selected(op, x) = match op {
    0b00 => x + 1,
    0b01 => x,
    0b01 => x + 2,
    0b11 => x
}
""", "selected(0b01, x)")
        self.run_computation(source, error='every value exactly once')

    def test_local_range_assignment_preserves_the_other_bits(self):
        source = self.computation_fixture("""
val cleared : bits(64) -> bits(64)
function cleared(x) = {
    value : bits(64) = x;
    value[11..0] = 0x000;
    return(value)
}
""", "cleared(x)")
        text, _ = self.run_computation(source)
        self.assertIn("word_insert", text)
        self.assertIn("(0,12)", text)
        self.run_computation(
            source.replace('value : bits(64) = x;', 'value : bits(64) = undefined;'),
            error='uninitialized bits')

    def test_empty_vector_is_not_a_hol_zero_word(self):
        text, _ = self.run_computation(
            self.computation_fixture('', 'x @ sail_zeros(0)'))
        self.assertNotIn(":0 word", text)
        self.assertIn(":1)", text)

    def test_unknown_empty_producer_is_not_discarded(self):
        source = self.computation_fixture(
            'val empty = impure "empty" : unit -> bits(0)\n',
            "x @ empty()")
        self.run_computation(
            source,
            error='unsupported primitive on empty bitvectors: empty')

    def test_unsupported_empty_word_operation_fails_before_model(self):
        source = self.computation_fixture(
            "", "x @ not_vec(sail_zeros(0))")
        self.run_computation(
            source,
            error='unsupported primitive on empty bitvectors: not_vec')

    def test_effectful_defined_empty_producer_retains_its_write(self):
        source = self.computation_fixture("""
val empty : bits(64) -> bits(0)
function empty(x) = { X_set(0, 64, x); sail_zeros(0) }
""", "x @ empty(x)")
        text, deps = self.run_computation(source)
        self.assertGreaterEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined empty", deps)

    def test_static_integer_ssa_and_minimum_specialize_actual_slice(self):
        source = self.computation_fixture("""
val narrowed : bits(64) -> bits(64)
function narrowed(x) = {
    len : int = 8;
    len = len + 4;
    let 'len = min_int(len, 64);
    assert(constraint('len > 0 & 'len <= 64));
    return(sail_zero_extend(x[len - 1 .. 0], 64))
}
""", "narrowed(x)")
        text, deps = self.run_computation(source)
        self.assertIn("(0,12)", text)
        self.assertIn("statically-proved-assertion", deps)

    def test_immutable_let_hides_outer_undefined_local(self):
        source = self.computation_fixture("""
val selected : bits(64) -> bits(64)
function selected(x) = {
    value : bits(64) = undefined;
    { let value = x; return(value) };
    return(x)
}
""", "selected(x)")
        self.run_computation(source)
        source = source.replace("{ let value = x; return(value) };",
                                "{ let value = x; () };").replace(
                                    "return(x)\n}", "return(value)\n}")
        self.run_computation(source, error='uninitialized bits')

    def test_enum_final_wildcard_retains_and_selects_actual_body(self):
        source = self.computation_fixture("""
enum choice = { Keep, Other, Reject }
val opaque = pure "opaque" : bits(64) -> bits(64)
val selected : (choice, bits(64)) -> bits(64)
function selected(op, x) = match op { Keep => x, _ => opaque(x) }
""", "selected(Keep, x)")
        self.run_computation(source)
        self.run_computation(
            source.replace('selected(Keep, x)', 'selected(Other, x)'),
            error='unsupported primitive opaque')

    def test_enum_final_wildcard_emits_one_effectful_fallback(self):
        source = HEADER + """
enum choice = { Keep, Other, Third, Fourth, Reject }
register Mode : choice
register Result : bits(64)
register Side : bits(64)
val ROOT : bits(64) -> unit
function ROOT(x) = {
    match Mode {
      Keep => Result = x,
      _ => { Side = x + x; Result = sub_bits(x,x) }
    }
}
"""
        text, _ = self.run_computation(source)
        code = without_comments(text)
        self.assertEqual(code.count("write reg_Side"), 1)
        self.assertEqual(code.count("word_sub"), 1)
        self.assertEqual(code.count("write reg_Result"), 2)
        self.assertIn("sail_hl_ctor_Keep", code)
        # All constructors remain in the logical datatype; only their shared
        # wildcard computation is emitted once.
        for name in ("Other", "Third", "Fourth", "Reject"):
            self.assertIn("sail_hl_ctor_" + name, code)

    def test_stack_pointer_read_uses_actual_unit_64_signature(self):
        source = self.computation_fixture(
            'val SP_read = impure "SP_read" : unit -> bits(64)\n',
            "SP_read()")
        text, deps = self.run_computation(source)
        self.assertIn("read SP", text)
        self.assertIn("primitive-contract SP_read", deps)
        malformed = source.replace("unit -> bits(64)", "int -> bits(64)").replace(
            "SP_read()", "SP_read(0)")
        self.run_computation(malformed, error='SP_read requires unit -> bits(64)')

    def vector_fixture(self, body, extra=""):
        return HEADER + """
val V_read = impure "V_read" : forall 'n 'width,
  'width in {8,16,32,64,128}. (int('n),int('width)) -> bits('width)
val V_set = impure "V_set" : forall 'n 'width,
  'width in {8,16,32,64,128}. (int('n),int('width),bits('width)) -> unit
val CheckFPAdvSIMDEnabled64 = impure "enabled" : unit -> unit
""" + extra + """
val ROOT : (bits(5),bits(128)) -> unit
function ROOT(d,x) = { let 'r = unsigned(d);
""" + body + "\n}\n"

    def test_vector_projection_covers_register31_and_low64_writes(self):
        source = self.vector_fixture(
            "CheckFPAdvSIMDEnabled64(); V_set(r,64,V_read(31,64))")
        text, deps = self.run_computation(source)
        self.assertIn("read (DREG", text)
        self.assertIn("write (DREG", text)
        self.assertNotIn("rvalue", text)
        self.assertIn("successful-check Arm-AdvSIMD-enabled-access", deps)
        self.assertIn("primitive-contract V_read", deps)
        self.assertIn("primitive-contract V_set", deps)

    def test_vector_projection_rejects_bad_or_unknown_indices(self):
        for index in ("0 - 1", "32", "signed(x)"):
            with self.subTest(index=index):
                source = self.vector_fixture(
                    f"V_set(r,128,V_read({index},128))")
                self.run_computation(
                    source,
                    error='V_read index is not proved in 0..31')

    def test_vector_projection_reads_low_scalar_bits(self):
        for width in (8, 16, 32):
            with self.subTest(width=width):
                source = self.vector_fixture(
                    f"V_set(r,128,sail_zero_extend(V_read(31,{width}),128))")
                text, deps = self.run_computation(source)
                self.assertIn("read (DREG", text)
                self.assertIn(f"{width} word", text)
                self.assertIn("word_zx", text)
                self.assertIn("primitive-contract V_read", deps)
        malformed = self.vector_fixture(
            "V_set(r,128,V_read(0,8))").replace(
                "(int('n),int('width)) -> bits('width)",
                "(int('n),int('width)) -> bits(128)")
        self.run_computation(
            malformed,
            error='V_read requires a matching 8/16/32/64/128-bit result')

    def test_enabled_check_requires_unit_result(self):
        source = self.vector_fixture(
            "let ignored = CheckFPAdvSIMDEnabled64(); V_set(r,128,x)").replace(
                '"enabled" : unit -> unit', '"enabled" : unit -> bool')
        self.run_computation(
            source,
            error='CheckFPAdvSIMDEnabled64 requires unit -> unit')

    def test_fp_enabled_check_has_its_own_exact_contract(self):
        source = self.vector_fixture(
            "CheckFPEnabled64(); V_set(r,128,x)",
            'val CheckFPEnabled64 = impure "FP_enabled" : unit -> unit\n')
        text, deps = self.run_computation(source)
        self.assertIn("write (QREG", text)
        self.assertIn("primitive-contract CheckFPEnabled64", deps)
        self.assertIn("successful-check Arm-FP-enabled-access", deps)
        self.assertNotIn("successful-check Arm-AdvSIMD-enabled-access", deps)
        self.run_computation(
            source.replace('"FP_enabled" : unit -> unit', '"FP_enabled" : unit -> bool').replace('CheckFPEnabled64();', 'let ignored = CheckFPEnabled64();'),
            error='CheckFPEnabled64 requires unit -> unit')
        self.run_computation(
            source.replace('"FP_enabled" : unit -> unit', '"FP_enabled" : int -> unit').replace('CheckFPEnabled64();', 'CheckFPEnabled64(0);'),
            error='CheckFPEnabled64 requires unit -> unit')

    def test_enabled_check_argument_keeps_helper_effects(self):
        for check in ("CheckFPEnabled64", "CheckFPAdvSIMDEnabled64"):
            with self.subTest(check=check):
                extra = (
                    'val CheckFPEnabled64 = impure "FP_enabled" : unit -> unit\n'
                    if check == "CheckFPEnabled64" else "")
                source = self.vector_fixture(
                    f"{check}(touched(x)); V_set(r,128,x)", extra + """
val touched : bits(128) -> unit
function touched(x) = { V_set(0,128,x); () }
""")
                text, deps = self.run_computation(source)
                self.assertEqual(text.count("write (QREG"), 2)
                self.assertIn("inlined touched", deps)
                self.assertIn("primitive-contract " + check, deps)

    def test_fp_enabled_check_does_not_ignore_unknown_argument_effects(self):
        source = self.vector_fixture(
            "CheckFPEnabled64(opaque()); V_set(r,128,x)", """
val CheckFPEnabled64 = impure "FP_enabled" : unit -> unit
val opaque = impure "opaque" : unit -> unit
""")
        self.run_computation(source, error='unsupported primitive opaque')

    def test_defined_fp_check_is_inlined_not_replaced(self):
        source = self.vector_fixture(
            "CheckFPEnabled64(); V_set(r,128,x)", """
val CheckFPEnabled64 : unit -> unit
function CheckFPEnabled64() = { V_set(0,128,sail_zeros(128)); () }
""")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (QREG"), 2)
        self.assertIn("inlined CheckFPEnabled64", deps)
        self.assertNotIn("primitive-contract CheckFPEnabled64", deps)
        self.assertNotIn("successful-check Arm-FP-enabled-access", deps)

    def test_integer_absolute_value_keeps_signed_minimum_and_plain_types(self):
        for operation in ("abs_int_atom", "abs_int_plain"):
            with self.subTest(operation=operation):
                source = self.computation_fixture(
                    "$include <smt.sail>\n",
                    f"get_slice_int(64,{operation}(signed(x)),0)")
                text, deps = self.run_computation(source)
                self.assertIn("(abs ", text)
                self.assertIn("ival", text)
                self.assertIn("iword", text)
                self.assertIn("primitive-contract " + operation, deps)
        source = self.computation_fixture(
            "$include <smt.sail>\n",
            "get_slice_int(64,abs_int_atom(0 - 9223372036854775808),0)")
        text, _ = self.run_computation(source)
        self.assertIn("9223372036854775808", text)
        self.assertIn("abs", text)

    def test_defined_integer_absolute_value_is_not_replaced(self):
        source = self.computation_fixture("""
function abs_int_plain(x) = x
""", "get_slice_int(64,abs_int_plain(signed(x)),0)")
        text, deps = self.run_computation(source)
        self.assertNotIn("(abs ", text)
        self.assertIn("inlined abs_int_plain", deps)
        self.assertNotIn("primitive-contract abs_int_plain", deps)

    def test_integer_absolute_value_rejects_foreign_word_signature(self):
        for operation in ("abs_int_atom", "abs_int_plain"):
            with self.subTest(operation=operation):
                source = f"""default Order dec
type bits('n) = bitvector('n)
val {operation} = pure "foreign_abs" : bits(64) -> bits(64)
val ROOT : bits(64) -> bits(64)
function ROOT(x) = {operation}(x)
"""
                self.run_sail(
                    source, roots=("ROOT",),
                    error="integer absolute value requires an integer argument and result")

    def branch_fixture(self, body, extra=""):
        return HEADER + """
enum BranchType = {
  BranchType_DIRCALL, BranchType_INDCALL, BranchType_ERET,
  BranchType_DBGEXIT, BranchType_RET, BranchType_DIR, BranchType_INDIR,
  BranchType_EXCEPTION, BranchType_TMFAIL, BranchType_RESET, BranchType_UNKNOWN
}
register _PC : bits(64)
val BranchTo = impure "BranchTo" :
  forall 'N, 'N >= 0. (bits('N), BranchType, bool) -> unit
val BranchNotTaken = impure "BranchNotTaken" : (BranchType, bool) -> unit
val X_set = impure "X_set" : forall 'r,
  0 <= 'r & 'r <= 31. (int('r),int(64),bits(64)) -> unit
""" + extra + """
val ROOT : (bits(64),bits(5),bits(1)) -> unit
function ROOT(x,d,encoded_cond) = {
let c = encoded_cond == 0b1;
""" + body + "\n}\n"

    def test_arm_branch_updates_pc_and_keeps_event_projection(self):
        source = self.branch_fixture("BranchTo(x,BranchType_DIR,c)")
        text, deps = self.run_computation(source)
        self.assertIn("write PC", text)
        self.assertIn("EventJump", text)
        self.assertIn("read reg__5fPC s", text)
        self.assertIn("read events", text)
        self.assertIn("primitive-contract BranchTo", deps)
        self.assertIn("primitive-contract Arm-frozen-instruction-PC64", deps)
        self.assertIn("successful-check Arm-flat-branch-PC-event", deps)
        source = self.branch_fixture("BranchNotTaken(BranchType_DIR,c)")
        text, deps = self.run_computation(source)
        self.assertNotIn("write PC", text)
        self.assertIn("read PC s", text)
        self.assertIn("EventJump", text)
        self.assertIn("primitive-contract BranchNotTaken", deps)

    def test_arm_branch_evaluates_target_type_and_boolean_helpers(self):
        source = self.branch_fixture(
            "BranchTo(touched(x),kind(x),flag(x))", """
val touched : bits(64) -> bits(64)
function touched(x) = { X_set(0,64,x); x }
val kind : bits(64) -> BranchType
function kind(x) = { X_set(1,64,x); BranchType_DIR }
val flag : bits(64) -> bool
function flag(x) = { X_set(2,64,x); true }
""")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 3)
        self.assertLess(text.rfind("write (XREG"), text.index("write PC"))
        for helper in ("touched", "kind", "flag"):
            self.assertIn("inlined " + helper, deps)

    def test_arm_source_pc_is_frozen_after_branch_and_read_only(self):
        source = self.branch_fixture("""
let old = _PC;
BranchTo(x,BranchType_DIR,c);
X_set(0,64,_PC)
""")
        text, _ = self.run_computation(source)
        self.assertEqual(text.count("read reg__5fPC s"), 3)
        self.assertNotRegex(text, r"read reg__5fPC v[0-9]+")
        self.run_computation(
            self.branch_fixture('_PC = x'),
            error='source instruction PC is read-only')
        self.run_computation(
            source.replace('register _PC : bits(64)', 'register _PC : bits(32)').replace('X_set(0,64,_PC)', 'X_set(0,64,sail_zero_extend(_PC,64))'),
            error='source instruction PC must be a 64-bit word')

    def test_arm_branch_rejects_bad_width_missing_pc_and_spoofed_enum(self):
        source = self.branch_fixture(
            "BranchTo(x[31..0],BranchType_DIR,c)")
        self.run_computation(
            source,
            error='BranchTo requires (bits(64), BranchType, bool) -> unit')
        source = self.branch_fixture("BranchTo(x,BranchType_DIR,c)").replace(
            "register _PC : bits(64)\n", "")
        self.run_computation(source, error='explicit source _PC register')
        source = self.branch_fixture("BranchTo(x,BranchType_DIR,c)").replace(
            "  BranchType_DIRCALL, BranchType_INDCALL, BranchType_ERET,\n"
            "  BranchType_DBGEXIT, BranchType_RET, BranchType_DIR, BranchType_INDIR,\n"
            "  BranchType_EXCEPTION, BranchType_TMFAIL, BranchType_RESET, BranchType_UNKNOWN",
            "  BranchType_DIR")
        self.run_computation(source, error='declared Arm branch constructors')

    def test_arm_branch_rejects_result_and_boolean_signature_changes(self):
        source = self.branch_fixture(
            "let ignored = BranchTo(x,BranchType_DIR,c); ()").replace(
                "(bits('N), BranchType, bool) -> unit",
                "(bits('N), BranchType, bool) -> bool")
        self.run_computation(
            source,
            error='BranchTo requires (bits(64), BranchType, bool) -> unit')
        source = self.branch_fixture(
            "BranchNotTaken(BranchType_DIR,0)").replace(
                "(BranchType, bool) -> unit", "(BranchType, int) -> unit")
        self.run_computation(
            source,
            error='BranchNotTaken requires (BranchType, bool) -> unit')

    def test_defined_arm_branch_is_not_replaced_by_pc_contract(self):
        source = self.branch_fixture("BranchTo(x,BranchType_DIR,c)").replace(
            'val BranchTo = impure "BranchTo"', "val BranchTo")
        source = source.replace(
            'val BranchNotTaken = impure "BranchNotTaken"', """
function BranchTo(x,kind,conditional) = { () }
val BranchNotTaken = impure "BranchNotTaken" """)
        source = source.replace(
            "BranchTo(x,BranchType_DIR,c)\n}",
            "X_set(0,64,x); BranchTo(x,BranchType_DIR,c)\n}")
        text, deps = self.run_computation(source)
        self.assertNotIn("write PC", text)
        self.assertNotIn("EventJump", text)
        self.assertIn("inlined BranchTo", deps)
        self.assertNotIn("primitive-contract BranchTo", deps)

    def test_arm_branch_does_not_discard_unknown_argument_effect(self):
        source = self.branch_fixture(
            "BranchTo(x,BranchType_DIR,opaque())",
            'val opaque = impure "opaque" : unit -> bool\n')
        self.run_computation(source, error='unsupported primitive opaque')

    def test_dynamic_bit_access_uses_only_proved_positions(self):
        source = HEADER + """
val ROOT : (bits(64),bits(6)) -> bits(1)
function ROOT(x,position) = {
    let 'bit_position = unsigned(position);
    x[bit_position]
}
"""
        text, _ = self.run_sail(source, roots=("ROOT",))
        self.assertIn("num_of_int", text)
        self.assertIn("(bit ", text)
        # The actual prelude already constrains access positions. Supply a
        # weaker, still typed external signature so the backend guard itself
        # must reject this larger symbolic domain.
        weak_source = """default Order dec
type bits('n) = bitvector('n)
val bitvector_access = pure "access" : (bits(64),int) -> bits(1)
val unsigned = pure "unsigned" : bits(7) -> int
val ROOT : (bits(64),bits(7)) -> bits(1)
function ROOT(x,position) = bitvector_access(x,unsigned(position))
"""
        self.run_sail(weak_source,
                      roots=("ROOT",), error="proved in-bounds index")

    def prefix_fixture(self, prefix="0b0", extra="", second=""):
        return self.computation_fixture("""
val checked : forall 'p, 0 <= 'p & 'p <= 63.
  (int('p), bits(64)) -> bits(64)
function checked(position,x) = {
  assert(constraint('p < 32));
  x
}
""" + extra, """{
  let 'position = unsigned(""" + prefix + """ @ x[4..0]);
  let result = checked(position,x);
""" + second + """
  result
}""")

    def test_zero_prefix_uint_bounds_survive_cps_and_formal_aliases(self):
        text, deps = self.run_computation(self.prefix_fixture())
        self.assertIn("word_join", text)
        self.assertIn("val", text)
        self.assertIn("statically-proved-assertion", deps)
        self.assertIn("inlined checked", deps)

    def test_nonzero_and_dynamic_prefixes_cannot_prove_small_index(self):
        for prefix in ("0b1", "x[5]"):
            with self.subTest(prefix=prefix):
                text, deps = self.run_computation(self.prefix_fixture(prefix))
                self.assert_guarded_relation(text, deps, "lt_int(__id(position), 32)")
                self.assertIn("word_join", text)
                self.assertIn("(& 32)", text)
                self.assertNotIn("statically-proved-assertion", deps)

    def test_prefix_uint_metadata_retains_effectful_argument_evaluation(self):
        source = self.prefix_fixture("touched(x)", """
val touched : bits(64) -> bits(1)
function touched(x) = { X_set(0,64,x); 0b0 }
""")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 2)
        self.assertIn("inlined touched", deps)

    def test_prefix_metadata_cannot_replace_a_defined_unsigned_body(self):
        source = self.prefix_fixture(extra="""
function unsigned(x) = { assert(constraint('n == 6)); 63 }
""").replace("let 'r = unsigned(d);", "let 'r = 0;")
        text, deps = self.run_computation(source)
        self.assert_guarded_relation(text, deps, "lt_int(__id(position), 32)")
        self.assertIn("inlined unsigned", deps)
        self.assertNotIn("primitive-contract unsigned", deps)
        self.assertIn("(& 63)", text)

    def test_prefix_bounds_do_not_escape_a_numeric_shadow(self):
        source = self.prefix_fixture(second="""
  {
    let 'position = unsigned(0b1 @ x[4..0]);
    let ignored = checked(position,x);
    ()
  };
""")
        text, deps = self.run_computation(source)
        self.assert_guarded_relation(text, deps, "lt_int(__id(position), 32)")
        self.assertIn("word_join", text)
        self.assertIn("word 1", text)
        self.assertIn("statically-proved-assertion", deps)

    def test_prefix_bounds_do_not_leak_to_a_later_helper_call(self):
        source = self.prefix_fixture(second="""
  let 'bad_position = unsigned(0b1 @ x[4..0]);
  let ignored = checked(bad_position,x);
""")
        text, deps = self.run_computation(source)
        self.assert_guarded_relation(text, deps, "lt_int(__id(position), 32)")
        self.assertIn("word_join", text)
        self.assertIn("word 1", text)
        self.assertIn("statically-proved-assertion", deps)

    def test_known_prefix_bit_reads_select_actual_helper_returns(self):
        source = self.computation_fixture("""
val opaque = pure "opaque" : bits(64) -> bits(64)
val selected : (bits(1),bits(5),bits(64)) -> bits(64)
function selected(prefix,index,x) =
  if (prefix @ index)[5] == 0b1 then x else opaque(x)
""", "selected(0b1,x[4..0],x)")
        text, _ = self.run_computation(source)
        self.assertNotIn("opaque", text)
        self.run_computation(
            source.replace('selected(0b1,', 'selected(0b0,'),
            error='unsupported primitive opaque')

    def test_small_vector_writes_zero_extend_only_exact_widths(self):
        for width in (8, 16, 32):
            with self.subTest(width=width):
                source = self.vector_fixture(
                    f"V_set(r,{width},x[{width - 1}..0])")
                text, deps = self.run_computation(source)
                self.assertIn("write (QREG", text)
                self.assertIn("word_zx", text)
                self.assertIn("128 word", text)
                self.assertIn("primitive-contract V_set-small-zero-top", deps)
        source = self.vector_fixture("V_set(r,7,x[6..0])").replace(
            "{8,16,32,64,128}", "{7,8,16,32,64,128}")
        self.run_computation(source, error='only 8/16/32/64/128-bit vector values')

    def test_small_vector_write_retains_value_helper_effects(self):
        source = self.vector_fixture("V_set(r,8,touched(x))", """
val touched : bits(128) -> bits(8)
function touched(x) = { V_set(0,128,x); x[7..0] }
""")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (QREG"), 2)
        self.assertIn("inlined touched", deps)
        self.assertIn("V_set-small-zero-top", deps)

    def test_small_vector_write_still_checks_index_and_definedness(self):
        self.run_computation(
            self.vector_fixture('V_set(32,8,x[7..0])'),
            error='V_set index is not proved in 0..31')
        source = self.vector_fixture("""
value : bits(8) = undefined;
V_set(r,8,value)
""")
        self.run_computation(source, error='undefined local before assignment')

    def test_defined_small_vector_setter_is_not_replaced_by_projection(self):
        source = self.vector_fixture(
            "CheckFPAdvSIMDEnabled64(); V_set(r,8,x[7..0])", """
function V_set(index,width,value) = { () }
""").replace('val V_set = impure "V_set"', "val V_set")
        text, deps = self.run_computation(source)
        self.assertNotIn("write (QREG", text)
        self.assertIn("inlined V_set", deps)
        self.assertNotIn("primitive-contract V_set", deps)

    def test_ones_fill_is_typed_word_complement(self):
        source = self.vector_fixture("V_set(r,128,sail_ones(128))")
        text, _ = self.run_computation(source)
        self.assertIn("word_not", text)
        self.assertNotIn(":0 word", text)

    def test_checked_replication_uses_only_exact_literal_profiles(self):
        for count in (1, 2):
            with self.subTest(count=count):
                source = self.vector_fixture(
                    f"V_set(r,128,sail_zero_extend(replicate_bits(x[63..0],{count}),128))")
                text, deps = self.run_computation(source)
                self.assertIn("primitive-contract replicate_bits", deps)
                if count == 2:
                    self.assertIn("word_join", text)
        for count in (3, 8, 16):
            with self.subTest(count=count):
                source = self.vector_fixture(
                    f"V_set(r,128,sail_zero_extend(replicate_bits(x[7..0],{count}),128))")
                text, _ = self.run_computation(source)
                self.assertIn("word_duplicate", text)
        for count in (0,):
            with self.subTest(count=count):
                source = self.vector_fixture(
                    f"V_set(r,128,sail_zero_extend(replicate_bits(x[7..0],{count}),128))")
                self.run_computation(source, error='positive static count')

    def test_vector_write_requires_bounded_index(self):
        source = self.vector_fixture("V_set(32,128,x)")
        self.run_computation(source, error='V_set index is not proved in 0..31')

    def filled_bytes_fixture(self, helper="", call=""):
        if not call:
            call = "result[i * 8 + 7 .. i * 8] = x[i * 8 + 7 .. i * 8]"
        return self.computation_fixture(helper + """
val filled : bits(64) -> bits(64)
function filled(x) = {
    result : bits(64) = undefined;
    foreach (i from 0 to 7 by 1 in inc) {
""" + call + """
    };
    return(result)
}
""", "filled(x)")

    def test_static_loop_assigns_every_initially_unknown_bit(self):
        source = self.filled_bytes_fixture()
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("word_insert"), 8)
        self.assertIn("unrolled-static-loop i 0 7 1 inc", deps)
        self.run_computation(
            source.replace('i from 0 to 7', 'i from 0 to 6'),
            error='uninitialized')

    def test_partial_word_masks_survive_actual_helper_copy_and_return(self):
        helper = """
val replaced : forall 'e, 0 <= 'e & 'e <= 7.
  (bits(64),int('e),bits(8)) -> bits(64)
function replaced(argument,e,value) = {
    copied : bits(64) = argument;
    copied[e * 8 + 7 .. e * 8] = value;
    return(copied)
}
"""
        source = self.filled_bytes_fixture(
            helper, "result = replaced(result,i,x[i * 8 + 7 .. i * 8])")
        self.run_computation(source)
        self.run_computation(
            source.replace('return(copied)', 'return(argument)'),
            error='uninitialized')
        self.run_computation(
            source.replace('= argument;', '= not_vec(argument);'),
            error='uninitialized')

    def test_partial_word_masks_survive_tuple_aliases_and_helpers(self):
        # A tuple copies the word and its initialized-bit mask together.
        # Writing the original word later must not initialize the copy.
        transfers = (
            ("tuple initializer", """
    var pair : (bits(16),bits(64)) = (p,x);
    let (first,second) = pair;
    first[{slice}]
""", None),
            ("tuple assignment", """
    var pair : (bits(16),bits(64)) = (x[15..0],x);
    pair = (p,x);
    let (first,second) = pair;
    first[{slice}]
""", None),
            ("captured initializer", """
    var pair : (bits(16),bits(64)) = (p,x);
    p[15..8] = x[15..8];
    let (first,second) = pair;
    first[{slice}]
""", None),
            ("captured assignment", """
    var pair : (bits(16),bits(64)) = (x[15..0],x);
    pair = (p,x);
    p[15..8] = x[15..8];
    let (first,second) = pair;
    first[{slice}]
""", None),
            ("immutable tuple binding", """
    let pair = (p,x);
    let (first,second) = pair;
    first[{slice}]
""", None),
            ("helper-produced tuple RHS", """
    var pair : (bits(16),bits(64)) = (x[15..0],x);
    pair = copy_pair(p,x);
    let (first,second) = pair;
    first[{slice}]
""", "copy"),
            ("pure helper formal", """
    var pair : (bits(16),bits(64)) = (p,x);
    read_pair(pair,())
""", "pure"),
            ("stateful helper formal", """
    var pair : (bits(16),bits(64)) = (p,x);
    read_pair(pair,())
""", "stateful"),
            ("early-return helper formal", """
    var pair : (bits(16),bits(64)) = (p,x);
    read_pair(pair,())
""", "return"),
            ("nested helper formal", """
    var pair : (bits(16),(bits(16),bits(64))) = (x[15..0],(p,x));
    read_pair(pair,())
""", "nested"),
        )
        for name, statements, helper_mode in transfers:
            for complete, slice in ((False, "7..0"), (False, "15..8"),
                                    (True, "15..8")):
                with self.subTest(transfer=name, complete=complete, slice=slice):
                    helper = ""
                    if helper_mode == "copy":
                        helper = """
val copy_pair : (bits(16),bits(64)) -> (bits(16),bits(64))
function copy_pair(first,second) = return((first,second))
"""
                    elif helper_mode is not None:
                        pair_type = ("(bits(16),(bits(16),bits(64)))"
                                     if helper_mode == "nested" else
                                     "(bits(16),bits(64))")
                        unpack = ("let (unused_word,nested) = pair;\n"
                                  "    let (first,second) = nested;"
                                  if helper_mode == "nested" else
                                  "let (first,second) = pair;")
                        effect = ("X_set(0,64,second);"
                                  if helper_mode == "stateful" else "")
                        result = (f"return(first[{slice}])"
                                  if helper_mode == "return" else f"first[{slice}]")
                        helper = f"""
val read_pair : ({pair_type},unit) -> bits(8)
function read_pair(pair,unused) = {{
    {unpack}
    {effect}
    {result}
}}
"""
                    initial = "x[15..0]" if complete else "undefined"
                    source = self.computation_fixture(helper + f"""
val selected : bits(64) -> bits(8)
function selected(x) = {{
    var p : bits(16) = {initial};
    p[7..0] = x[7..0];
{statements.format(slice=slice)}
}}
""", "get_slice_int(64,unsigned(selected(x)),0)")
                    diagnostic = (None if complete or slice == "7..0" else
                                  "read of uninitialized bits")
                    result = self.run_computation(source, error=diagnostic)
                    if diagnostic is None:
                        text, dependencies = result
                        self.assertEqual(text.count("write (XREG"),
                                         2 if helper_mode == "stateful" else 1)
                        if helper_mode is not None:
                            callee = "copy_pair" if helper_mode == "copy" else "read_pair"
                            self.assertIn("inlined " + callee, dependencies)

    def test_joins_refuse_tuples_with_partially_initialized_fields(self):
        # Joins track the masks of whole words only. A tuple carrying a
        # partial word must not leave a join with its word 0 backing.
        for label, between in (
                ("loop", "    foreach (i from 0 to 0 by 1 in inc) { () };"),
                ("if", "    if x[0] == bitone then { pair = pair } else { () };")):
            with self.subTest(join=label):
                source = self.computation_fixture("""
val selected : bits(64) -> bits(8)
function selected(x) = {
    var p : bits(16) = undefined;
    p[7..0] = x[7..0];
    var pair : (bits(16),bits(64)) = (p,x);
""" + between + """
    let (first,second) = pair;
    first[15..8]
}
""", "get_slice_int(64,unsigned(selected(x)),0)")
                self.run_computation(
                    source, error="control-flow join of a value with partially initialized fields")

    def test_inlined_helpers_do_not_take_the_shared_callers_width_facts(self):
        # F's shared definition fixes or generalizes its 'n. G has its own
        # 'n, with another value at the call; G must not inherit F's facts.
        header = "default Order dec\n$include <prelude.sail>\nregister D : bits(8)\n"
        loop = "  foreach (i from 1 to n) { () };\n"
        assertion = header + """
val G : forall 'n, 'n >= 0. (int('n), bits(8)) -> bits(8)
function G(n, v) = {
  let x = unsigned(v) in
  assert(x < 16, "small");
  v
}
val F : forall 'n, 'n in {8, 16}. (int('n), bits(8)) -> bits(8)
function F(n, v) = {
""" + loop + """  G(4, v)
}
val ROOT : bits(8) -> unit
function ROOT(v) = D = F(8, v)
"""
        _, dependencies = self.run_sail(assertion, roots=("ROOT",))
        self.assertIn("guarded-assertion lt_int(x, 16)", dependencies)
        self.assertNotIn("statically-proved-assertion lt_int(x, 16)", dependencies)
        branch = header + """
val G : forall 'n, 'n >= 0. (int('n), bits(8)) -> bool
function G(n, v) = {
  let x = unsigned(v) in
  (x < 16) & true
}
val F : forall 'n, 'n in {8, 16}. (int('n), bits(8)) -> bits(8)
function F(n, v) = {
""" + loop + """  if G(4, v) then 0x01 else 0x02
}
val ROOT : bits(8) -> unit
function ROOT(v) = D = F(8, v)
"""
        text, _ = self.run_sail(branch, roots=("ROOT",))
        self.assertIn("(word 2)", text)
        width = header + """
val G : forall 'n, 'n > 0. (int('n), bits(8)) -> int
function G(k, v) = {
  let z : bits('n) = sail_zeros(k) in
  unsigned(z) + unsigned(v) + 'n
}
val F : forall 'n 'm, 'n > 0 & 'm > 0. (bits('n), bits('m), bits(8)) -> int
function F(x, y, v) = G('m, v)
val ROOT : (bits(8), bits(16), bits(8)) -> unit
function ROOT(a, b, v) = D = get_slice_int(8, F(a, b, v), 0)
"""
        text, _ = self.run_sail(width, roots=("ROOT",))
        self.assertIn("((& 16):int)", text)
        self.assertNotIn("dimindex(:N0)):int)):int))`", text)

    def test_only_initialized_partial_slices_can_be_read(self):
        source = self.filled_bytes_fixture(call="""
if i == 0 then result[7..0] = x[7..0] else {
    result[i * 8 + 7 .. i * 8] = result[7..0]
}""")
        self.run_computation(source)
        self.run_computation(
            source.replace('= result[7..0]', '= result[15..8]'),
            error='read of uninitialized bits')

    def test_partial_length_reads_type_not_unknown_data(self):
        source = self.filled_bytes_fixture(call="""
assert(bitvector_length(result) == 64);
result[i * 8 + 7 .. i * 8] = x[i * 8 + 7 .. i * 8]""")
        self.run_computation(source)
        self.run_computation(
            source.replace('bitvector_length(result)', 'bitvector_length(not_vec(result))'),
            error='undefined local before assignment')

    def test_partial_length_retains_argument_helper_effects(self):
        source = self.filled_bytes_fixture("""
val retained : bits(64) -> bits(64)
function retained(argument) = { X_set(0,64,0x0000000000000000); return(argument) }
""", """
assert(bitvector_length(retained(result)) == 64);
result[i * 8 + 7 .. i * 8] = x[i * 8 + 7 .. i * 8]""")
        text, deps = self.run_computation(source)
        self.assertEqual(text.count("write (XREG"), 9)
        self.assertIn("inlined retained", deps)

    def test_unknown_and_excessive_static_loops_are_rejected(self):
        source = self.filled_bytes_fixture()
        for replacement, error in (
                ("i from 0 to unsigned(x)", "foreach bounds must be statically"),
                ("i from 0 to 256", "256-iteration static bound"),
                ("i from 0 to 7 by 0", "positive static integer")):
            changed = source.replace("i from 0 to 7 by 1",
                                     replacement if "by" in replacement else
                                     replacement + " by 1")
            changed = changed.replace(
                "result[i * 8 + 7 .. i * 8] = x[i * 8 + 7 .. i * 8]",
                "()")
            self.run_computation(changed, error=error)

    def test_nested_highest_bit_helper_preserves_early_return(self):
        source = self.computation_fixture("""
val highest : bits(64) -> int
function highest(x) = {
    foreach (i from 63 to 0 by 1 in dec) {
        if [x[i]] == 0b1 then return(i);
        ()
    };
    return(negate_atom(1))
}
""", "get_slice_int(64,highest(x) + 1,0)")
        text, deps = self.run_computation(source)
        self.assertIn("unrolled-static-loop i 63 0 1 dec", deps)
        self.assertIn("inlined highest", deps)
        self.assertLess(len(text), 200_000)

    def test_counting_loop_joins_ssa_before_next_iteration(self):
        source = self.computation_fixture("""
val counted : bits(64) -> int
function counted(x) = {
    result : int = 0;
    foreach (i from 0 to 63 by 1 in inc) {
        if [x[i]] == 0b1 then result = result + 1;
        ()
    };
    return(result)
}
""", "get_slice_int(64,counted(x),0)")
        text, _ = self.run_computation(source)
        self.assertLess(len(text), 200_000)

    def test_state_branches_emit_the_following_effect_once(self):
        for condition in ("flag == 0b1", "(flag == 0b1 | false)",
                          "(flag == 0b1 & true)"):
            statements = "\n".join(
                f"if {condition} then D = 0x{index:016x} "
                f"else D = 0x{index + 16:016x};"
                for index in range(8))
            source = """
register D : bits(64)
val ROOT : bits(1) -> unit
function ROOT(flag) = {
""" + statements + """
    D = 0x0000000000000063
}
"""
            with self.subTest(condition=condition):
                text, _ = self.run_sail(source, roots=("ROOT",))
                # The source value is captured and then written, each once.
                self.assertEqual(text.count("word 99"), 2)
                self.assertEqual(text.count("write reg_D"), 17)
                self.assertLess(len(text), 12_000)

    def test_state_match_joins_keep_every_arm_and_one_following_effect(self):
        source = """
enum Operation = { First, Second, Third }
register D : bits(64)
val ROOT : Operation -> unit
function ROOT(operation) = {
    match operation {
        First => D = 0x0000000000000001,
        Second => D = 0x0000000000000002,
        Third => D = 0x0000000000000003
    };
    D = 0x0000000000000063
}
"""
        text, _ = self.run_sail(source, roots=("ROOT",))
        self.assertEqual(text.count("word 99"), 2)
        self.assertEqual(text.count("write reg_D"), 4)
        for value in (1, 2, 3):
            self.assertIn(f"word {value}", text)

    def test_state_branch_join_does_not_initialize_unassigned_bits(self):
        source = """
register D : bits(64)
val ROOT : bits(1) -> unit
function ROOT(flag) = {
    value : bits(64) = undefined;
    if flag == 0b1 then value = 0x0000000000000001
    else value[31 .. 0] = 0x00000002;
    D = value
}
"""
        self.run_sail(source, roots=("ROOT",),
                      error="uninitialized")

    def test_known_shared_enum_survives_a_mutable_branch_join(self):
        source = """
enum Choice = { First, Second }
register D : bits(64)
val eq_any = pure "eq_any" : forall ('a : Type). ('a, 'a) -> bool
val selected : unit -> Choice
function selected() = { D = 0x0000000000000007; First }
val ROOT : bits(1) -> unit
function ROOT(flag) = {
    choice : Choice = Second;
    if flag == 0b1 then choice = selected() else choice = selected();
    D = if eq_any(choice, First) then 0x0000000000000001
        else 0x0000000000000002
}
"""
        text, _ = self.run_sail(source, roots=("ROOT",))
        self.assertIn("sail_hl_ctor_First", text)
        self.assertIn("word 1", text)
        self.assertNotIn("word 2", text)
        self.assertIn("write reg_D", text)

    def test_loop_join_restores_a_shadowed_outer_mutable_index(self):
        source = """
register D : bits(64)
val ROOT : unit -> unit
function ROOT() = {
    index : int = 9;
    foreach (index from 0 to 1) { D = 0x0000000000000001 };
    D = get_slice_int(64, index, 0)
}
"""
        text, _ = self.run_sail(source, roots=("ROOT",))
        self.assertIn("& 9", text)
        self.assertIn("write reg_D", text)
        self.assertEqual(text.count("write reg_D"), 3)

    def test_explicit_bit_guard_rejects_a_defined_equality_helper(self):
        source = self.computation_fixture("""
function eq_bits(x, y) = true
val selected : (bits(2), bits(64)) -> bits(64)
function selected(op, x) = match op {
    matched if eq_bits(matched, 0b00) => x,
    0b01 => x + x, 0b10 => sub_bits(x, x), 0b11 => not_vec(x)
}
""", "selected(0b00, x)")
        self.run_computation(
            source,
            error='bit matches require unguarded binary literal cases')

    def test_numeric_argument_facts_discharge_actual_helper_assertion(self):
        source = self.computation_fixture("""
val checked : forall 'amount. (bits(64), int('amount)) -> bits(64)
function checked(x, amount) = {
    assert(constraint('amount >= 0));
    sail_shiftleft(x, amount)
}
""", "checked(x, unsigned(d))")
        text, deps = self.run_computation(source)
        self.assertIn("word_shl", text)
        self.assertIn("proved-numeric-argument-fact checked", deps)
        guarded, guarded_deps = self.run_computation(
            source.replace('checked(x, unsigned(d))', 'checked(x, 0 - 1)'))
        self.assert_guarded_relation(guarded, guarded_deps,
                                     "gteq_int(__id(amount), 0)")
        self.assertIn("word_shl", guarded)
        self.assertIn("(& 1)", guarded)
        self.assertNotIn("statically-proved-assertion", guarded_deps)

    def test_short_circuit_uses_proved_numeric_operand_refinement(self):
        # Multiplication's runtime interval is deliberately coarse here.
        # Sail's checked singleton types still prove the full source
        # assertion for every three-bit position, without an input premise.
        source = self.computation_fixture("""
val bounded : forall 'p. (int('p),bits(64)) -> bits(64)
function bounded(position,x) = {
    assert(constraint(0 <= 'p & 'p + 64 - 1 < 64 * 2));
    x
}
""", "bounded(unsigned(x[2..0]) * 8,x)")
        text, deps = self.run_computation(source)
        self.assertIn("statically-proved-assertion", deps)
        self.assertIn("inlined bounded", deps)
        self.assertIn(" * ", text)
        for changed in (
                source.replace('x[2..0]', 'x[3..0]'),
                source.replace('unsigned(x[2..0]) * 8', 'signed(x)')):
            with self.subTest(source=changed):
                guarded, guarded_deps = self.run_computation(changed)
                self.assert_guarded_relation(guarded, guarded_deps,
                                             "add_atom(__id(position), 64)")
                self.assertIn("(& 64)", guarded)
                self.assertIn(" * ", guarded)
                self.assertNotIn("statically-proved-assertion", guarded_deps)
        # The 128-bit form permits the complete four-bit byte-position
        # field; the value returned by this synthetic helper stays 64 bits.
        wide = source.replace("'p + 64 - 1 < 64 * 2",
                              "'p + 128 - 1 < 128 * 2")
        self.run_computation(wide.replace('x[2..0]', 'x[3..0]'))

    def test_pure_short_circuit_uses_proved_numeric_operand_refinement(self):
        for predicate, operator in (("0 <= 'p", "|"), ("'p < 0", "&")):
            with self.subTest(predicate=predicate):
                source = HEADER + """
val opaque = pure "opaque" : unit -> bool
val predicate : forall 'p. int('p) -> bool(""" + predicate + """)
function predicate(position) = """ + predicate.replace("'p", "position") + """
val ROOT : bits(64) -> bool
function ROOT(x) = {
    let 'position = unsigned(x[2..0]) * 8;
    predicate(position) """ + operator + """ opaque()
}
"""
                text, deps = self.run_sail(source, roots=("ROOT",))
                self.assertIn("inlined predicate", deps)
                self.assertIn(" * ", text)
                self.assertNotIn("primitive-contract opaque", deps)
                self.run_sail(
                    source.replace("unsigned(x[2..0]) * 8", "signed(x)"),
                    roots=("ROOT",), error="unsupported primitive opaque")
                # An explicit broad Boolean annotation does not carry
                # the singleton proposition used to select this branch.
                self.run_sail(
                    source.replace(
                        "    predicate(position)",
                        "    (predicate(position) : bool)"),
                    roots=("ROOT",), error="unsupported primitive opaque")

    def test_short_circuit_refinement_does_not_capture_shadowed_numeric_facts(self):
        source = self.computation_fixture("""
val opaque = impure "opaque" : unit -> bool
val checked : forall 'amount. (bits(64),int('amount)) -> bits(64)
function checked(x,amount) = {
    let 'amount = signed(x);
    let ignored = (amount >= 0) | opaque();
    x
}
""", "checked(x,unsigned(d))")
        for actual in ("unsigned(d)", "0"):
            with self.subTest(actual=actual):
                self.run_computation(
                    source.replace('checked(x,unsigned(d))', 'checked(x,' + actual + ')'),
                    error='unsupported primitive opaque')

    def test_short_circuit_refinement_does_not_capture_outer_helper_facts(self):
        source = self.computation_fixture("""
val opaque = impure "opaque" : unit -> bool
val inner : forall 'amount. (bits(64),int('amount)) -> bits(64)
function inner(x,amount) = {
    let ignored = (amount >= 0) | opaque();
    x
}
val outer : forall 'amount. (bits(64),int('amount)) -> bits(64)
function outer(x,amount) = inner(x,0 - amount)
""", "outer(x,unsigned(d))")
        self.run_computation(source, error='unsupported primitive opaque')

    def test_precise_lane_bounds_survive_intermediate_helper(self):
        source = self.computation_fixture("""
val lane : forall 'N 'e 'size, 'N >= 0 & 'size > 0.
  (bits('N),int('e),int('size)) -> bits('size)
function lane(vector,e,size) = {
    assert(e >= 0 & (e + 1) * size <= 'N);
    return(vector[e * size + size - 1 .. e * size])
}
val forwarded : forall 'e. (bits(128),int('e)) -> bits(8)
function forwarded(vector,e) = lane(vector,e,8)
""", "sail_zero_extend(forwarded(x @ x,unsigned(d[2..0]) + 8),64)")
        text, deps = self.run_computation(source)
        self.assertIn("word_subword", text)
        self.assertIn("inlined forwarded", deps)
        self.assertIn("statically-proved-assertion", deps)
        for changed in (
                source.replace('d[2..0]', 'd[3..0]'),
                source.replace('unsigned(d[2..0]) + 8', 'signed(x)')):
            with self.subTest(source=changed):
                guarded, guarded_deps = self.run_computation(changed)
                self.assert_guarded_relation(guarded, guarded_deps,
                                             "mult_atom(add_atom(e, 1), size)")
                self.assertIn("word_subword", guarded)
                self.assertIn("(& 128)", guarded)
                self.assertIn("inlined forwarded", guarded_deps)
                self.assertNotIn("statically-proved-assertion", guarded_deps)

    def test_numeric_assertion_substitution_is_simultaneous(self):
        source = self.computation_fixture("""
val checked : forall 'a 'b. (bits(64),int('a),int('b)) -> bits(64)
function checked(x,a,b) = { assert(a < b); x }
val forwarded : (bits(64),bits(5)) -> bits(64)
function forwarded(x,d) = {
    let 'a = unsigned(d);
    let 'b = a + 1;
    checked(x,a,b)
}
""", "forwarded(x,d)")
        self.run_computation(source)
        text, deps = self.run_computation(
            source.replace("    checked(x,a,b)\n", "    checked(x,b,a)\n"))
        self.assert_guarded_relation(text, deps, "lt_int(a, b)")
        self.assertIn(" + ", text)
        self.assertNotIn("statically-proved-assertion", deps)

    def test_unmapped_helper_local_constraint_is_not_assumed(self):
        source = self.computation_fixture("""
val checked : forall 'amount. (bits(64),int('amount)) -> bits(64)
function checked(x,amount) = {
    let 'other = signed(x);
    assert(amount >= 0 & other >= 0);
    x
}
""", "checked(x,0)")
        text, deps = self.run_computation(source)
        self.assert_guarded_relation(text, deps, "other")
        self.assertIn("ival", text)
        self.assertNotIn("statically-proved-assertion", deps)

    def test_nested_numeric_parameters_do_not_capture_caller_facts(self):
        source = self.computation_fixture("""
val inner : forall 'amount. (bits(64), int('amount)) -> bits(64)
function inner(x, amount) = {
    assert(constraint('amount >= 0));
    sail_shiftleft(x, amount)
}
val outer : forall 'amount. (bits(64), int('amount)) -> bits(64)
function outer(x, amount) = inner(x, 0 - amount)
""", "outer(x, unsigned(d))")
        text, deps = self.run_computation(source)
        self.assert_guarded_relation(text, deps, "gteq_int(__id(amount), 0)")
        self.assertIn(" - ", text)
        self.assertIn("word_shl", text)
        self.assertNotIn("statically-proved-assertion", deps)

    def test_numeric_let_shadow_does_not_capture_caller_facts_or_value(self):
        helper = """
val checked : forall 'amount. (bits(64), int('amount)) -> bits(64)
function checked(x, amount) = {
    let 'amount = signed(x);
    assert(constraint('amount >= 0));
    x
}
"""
        for argument in ("unsigned(d)", "0"):
            with self.subTest(argument=argument):
                text, deps = self.run_computation(
                    self.computation_fixture(helper, f'checked(x, {argument})'))
                self.assert_guarded_relation(text, deps,
                                             "gteq_int(__id(amount), 0)")
                self.assertIn("ival", text)
                self.assertNotIn("statically-proved-assertion", deps)

    def test_integer_shift_primitives_require_nonnegative_amounts(self):
        for primitive, operation in (
                ("sail_shiftleft", "word_shl"),
                ("sail_shiftright", "word_ushr"),
                ("sail_arith_shiftright", "word_ishr")):
            source = self.computation_fixture(
                "", f"{primitive}(x, unsigned(d))")
            text, _ = self.run_computation(source)
            self.assertIn(operation, text)
            self.run_computation(
                source.replace('unsigned(d))', '0 - 1)'),
                error='integer shifts require a proved nonnegative')

    def test_unknown_integer_shift_amount_is_rejected(self):
        source = HEADER + """
val X_set = impure "flat_X_set" : forall 'r,
  0 <= 'r & 'r <= 31. (int('r), int(64), bits(64)) -> unit
val ROOT : bits(64) -> unit
function ROOT(x) = X_set(0, 64, sail_shiftleft(x, signed(x)))
"""
        self.run_computation(
            source,
            error='integer shifts require a proved nonnegative')

    def test_source_facing_x_read_still_requires_executed_bounds(self):
        helper = """
val X_read = impure "flat_X_read" : forall 'r 'width,
  'width in {8,16,32,64}. (int('r), int('width)) -> bits('width)
"""
        for index in (-1, 32):
            source = self.computation_fixture(
                helper, f"X_read({'0 - 1' if index < 0 else index}, 64)")
            self.run_computation(source, error='X_read index is not proved in 0..31')
        for width in (8, 16):
            source = self.computation_fixture(
                helper, f"sail_zero_extend(X_read(31, {width}), 64)")
            text, _ = self.run_computation(source)
            self.assertIn("word_zx", text)
            self.assertIn("read (XREG", text)
            self.assertNotIn("read (WREG", text)
            for index in ("0 - 1", "32"):
                self.run_computation(
                    source.replace(f'X_read(31, {width})', f'X_read({index}, {width})'),
                    error='X_read index is not proved in 0..31')
        for width in (4, 128):
            broad = helper.replace("{8,16,32,64}", "{4,8,16,32,64,128}")
            source = self.computation_fixture(
                broad, f"get_slice_int(64,unsigned(X_read(0,{width})),0)")
            self.run_computation(source, error='X_read supports only 8/16/32/64-bit')
        source = HEADER + helper + """
val X_set = impure "flat_X_set" : forall 'r,
  0 <= 'r & 'r <= 31. (int('r), int(64), bits(64)) -> unit
val ROOT : bits(64) -> unit
function ROOT(x) = { let 'r = signed(x); X_set(0, 64, X_read(r, 64)) }
"""
        self.run_computation(source, error='X_read index is not proved in 0..31')

    def test_nonzero_integer_slice_uses_floor_division(self):
        source = self.computation_fixture(
            "", "get_slice_int(64, signed(x) * signed(x), 64)")
        text, _ = self.run_computation(source)
        self.assertIn(" div ", text)
        self.assertIn(" pow 64", text)
        self.assertIn("iword", text)
        self.run_computation(
            source.replace('signed(x) * signed(x), 64)', 'signed(x) * signed(x), 0 - 1)'),
            error='integer slices require a nonnegative static start')

    def test_unknown_integer_slice_start_is_rejected(self):
        source = HEADER + """
val X_set = impure "flat_X_set" : forall 'r,
  0 <= 'r & 'r <= 31. (int('r), int(64), bits(64)) -> unit
val ROOT : (bits(64), bits(5)) -> unit
function ROOT(x, start) = X_set(0, 64, get_slice_int(64, signed(x), unsigned(start)))
"""
        self.run_computation(source, error='only statically known bit positions')

    def test_stack_pointer_contract_requires_64_bit_value(self):
        source = HEADER + """
val SP_set = impure "flat_SP_set" : bits(32) -> unit
val ROOT : bits(32) -> unit
function ROOT(x) = SP_set(x)
"""
        self.run_computation(source, error='SP_set requires bits(64) -> unit')

    def test_local_renaming_does_not_change_export(self):
        before, _ = self.run_sail(MODEL)
        after, _ = self.run_sail(MODEL.replace(
            "add_value(x, y) = x + y", "add_value(left, right) = left + right"))
        self.assertEqual(before, after)

    def test_helper_refactoring_is_accepted(self):
        text, _ = self.run_sail(MODEL.replace(
            "add_value(x, y) = x + y",
            "add_value(x, y) = { let total = x + y; total }"))
        self.assertIn("word_add", text)
        self.assertGreater(text.count("let "), 2)

    def test_callee_mutation_changes_instruction(self):
        text, deps = self.run_sail(MODEL.replace(
            "add_value(x, y) = x + y", "add_value(x, y) = sub_bits(x, y)"))
        self.assertIn("word_sub", text)
        self.assertNotIn("word_add", text)
        self.assertIn("inlined add_value", deps)

    def test_additional_register_write_is_retained(self):
        text, _ = self.run_sail(MODEL, roots=("TWO_WRITES",))
        self.assertEqual(text.count("(write "), 2)
        written = re.search(r"let (v\d+) = \(write reg_D", text).group(1)
        self.assertIn("read reg_D " + written, text)
        self.assertIn("write reg_B", text)

    def test_stateful_conditional(self):
        source = MODEL + """
val BRANCH : unit -> unit
function BRANCH() = if A == 0x0000000000000000
                   then D = A + B else D = sub_bits(A, B)
"""
        text, _ = self.run_sail(source, roots=("BRANCH",))
        self.assertIn("if ", text)
        self.assertIn("word_add", text)
        self.assertIn("word_sub", text)

    def test_unknown_pure_primitive_is_rejected(self):
        source = MODEL.replace(
            "val add_value :", 'val opaque = pure "opaque" : (bits(64), bits(64)) -> bits(64)\nval add_value :'
        ).replace("add_value(x, y) = x + y", "add_value(x, y) = opaque(x, y)")
        self.run_sail(source, error="unsupported primitive opaque")

    def test_unknown_state_effect_is_rejected(self):
        source = MODEL + """
val touch = "touch" : unit -> unit
val BAD : unit -> unit
function BAD() = { D = A; touch() }
"""
        self.run_sail(source, roots=("BAD",), error="unsupported primitive touch")

    def test_type_error_precedes_export(self):
        source = MODEL.replace("add_value(x, y) = x + y", "add_value(x, y) = true")
        self.run_sail(source, error="Type error")

    def test_missing_root_is_rejected(self):
        self.run_sail(MODEL, roots=("missing",), error="root not found")

    def test_no_partial_export_after_second_root_failure(self):
        source = MODEL + """
val opaque = pure "opaque" : bits(64) -> bits(64)
val BAD : bits(64) -> bits(64)
function BAD(x) = opaque(x)
"""
        self.run_sail(source, roots=("ADD", "BAD"),
                      error="unsupported primitive opaque")

    def test_unspecialized_width_is_rejected(self):
        source = HEADER + """
val ident : forall 'n, 'n > 0. bits('n) -> bits('n)
function ident(x) = x
"""
        self.run_sail(source, roots=("ident",), error="uninstantiated numeric type variable")

    def test_numeric_type_division_uses_fixed_operands(self):
        # 100 + floor(65/3) = 121; 100 + floor(-5/3) = 98.
        for n, expected, excluded in ((65, 121, 122), (-5, 98, 99)):
            with self.subTest(n=n):
                text, _ = self.run_computation(HEADER + f"""
val ident : forall 'n 'm.
    (int('n), int('m), bits(div('n,'m) + 100)) -> bits(div('n,'m) + 100)
function ident(n, m, x) = x
register D : bits({expected})
val ROOT : bits({expected}) -> unit
function ROOT(x) = D = ident({n}, 3, x)
""")
                self.assertIn(f":{expected} word", text)
                self.assertNotIn(f":{excluded} word", text)

    def test_refined_integer_root_argument_is_rejected(self):
        source = HEADER + """
val ident : int(3) -> int(3)
function ident(x) = x
"""
        self.run_sail(source, roots=("ident",),
                      error="integer root arguments and their refinements are unsupported")

    def test_refined_boolean_root_argument_is_rejected(self):
        source = HEADER + """
val ident : bool(true) -> bool(true)
function ident(x) = x
"""
        self.run_sail(source, roots=("ident",),
                      error="refined Boolean root arguments are unsupported")

    def test_unit_helper_is_translated(self):
        text, deps = self.run_sail(MODEL, roots=("ZERO_VALUE",))
        self.assertIn("(one:1)", text)
        self.assertIn("word 0", text)
        self.assertIn("inlined zero_value", deps)

    def test_nested_state_let_restores_outer_binding(self):
        source = MODEL + """
val SCOPE : unit -> unit
function SCOPE() = {
    let saved = A;
    { let saved = B; D = saved };
    B = saved
}
"""
        text, _ = self.run_sail(source, roots=("SCOPE",))
        outer = re.search(r"\((v\d+):64 word\) = \(\(read reg_A s\)", text).group(1)
        inner = re.search(r"\((v\d+):64 word\) = \(\(read reg_B s\)", text).group(1)
        for value, register in ((inner, "D"), (outer, "B")):
            self.assertRegex(text, r"= \(" + value + r":64 word\) in\s+"
                             r"\(let v\d+ = \(write reg_" + register + " ")

    def test_enums_are_logical_datatypes(self):
        source = HEADER + """
enum choice = { Plus, Minus }
val choose : (choice, bits(64), bits(64)) -> bits(64)
function choose(op, x, y) = match op {
    Plus => x + y,
    Minus => sub_bits(x, y)
}
"""
        text, _ = self.run_sail(source, roots=("choose",))
        self.assertIn('define_type\n "sail_hl_type_choice =', text)
        self.assertIn('distinctness "sail_hl_type_choice"', text)
        self.assertIn("word_add", text)
        self.assertIn("word_sub", text)

    def test_singleton_enum_needs_no_distinctness_theorem(self):
        source = HEADER + """
enum singleton = { Only }
val ident : singleton -> singleton
function ident(value) = value
"""
        text, _ = self.run_sail(source, roots=("ident",))
        self.assertIn('define_type\n "sail_hl_type_singleton = sail_hl_ctor_Only"', text)
        self.assertNotIn("distinctness", text)

    def test_known_enum_argument_keeps_only_selected_branch(self):
        source = HEADER + """
enum choice = { Plus, Minus }
val opaque = pure "opaque" : bits(64) -> bits(64)
val choose : (choice, bits(64), bits(64)) -> bits(64)
function choose(op, x, y) = match op {
    Plus => x + y,
    Minus => opaque(x)
}
register D : bits(64)
val ROOT : (bits(64), bits(64)) -> unit
function ROOT(x, y) = D = choose(Plus, x, y)
"""
        text, deps = self.run_computation(source)
        self.assertIn("word_add", text)
        self.assertNotIn("opaque", text)
        self.run_computation(source.replace("choose(Plus", "choose(Minus"),
                             error="unsupported primitive opaque")

    def test_record_field_projection_uses_source_fields(self):
        source = HEADER + """
struct pair = { first : bits(64), second : bits(64) }
val choose : pair -> bits(64)
function choose(p) = p.second
"""
        text, _ = self.run_sail(source, roots=("choose",))
        self.assertIn("(SND ", text)
        self.assertIn("64 word#64 word", text)

    def test_enum_kernel_fixture_exports_every_root(self):
        text, _ = self.run_sail(ENUM_MODEL, roots=ENUM_ROOTS)
        for root in ENUM_ROOTS:
            with self.subTest(root=root):
                exported = "sail_hl_" + root.replace("_", "_5f")
                self.assertIn("let " + exported + " = new_definition", text)
        # The record argument retains the full Boolean-product domain;
        # neither field is a specialized or refined Boolean formal.
        self.assertIn("(bool#bool)", text)
        self.assertIn(":string)", text)

    def test_global_constant_is_translated(self):
        source = HEADER + """
let mask : bits(64) = 0x0000000000000007
val masked : bits(64) -> bits(64)
function masked(x) = x + mask
"""
        text, _ = self.run_sail(source, roots=("masked",))
        self.assertIn("word 7", text)

    def test_doubled_result_width_does_not_capture_caller_width(self):
        source = HEADER + """
val wide : forall 'l, 'l > 0. (implicit('l), int) -> bits('l)
function wide(l, n) = get_slice_int(l, n, 0)
val product : (bits(32), bits(32)) -> bits(64)
function product(x, y) = {
    let l : int(32) = 32;
    wide(2*l, signed(x) * signed(y))
}
"""
        text, _ = self.run_sail(source, roots=("product",))
        # The worker returns a word at an inferred type dimension. Its
        # caller, not a same-spelled variable in the worker, chooses 64 bits.
        self.assertRegex(text, r"\(iword [^\n]+:\(N0\)word")
        self.assertRegex(text, r"\(sail_hl_shared_[^\n]+wide[^\n]+:64 word")
        self.assertNotRegex(text, r"\(sail_hl_shared_[^\n]+wide[^\n]+:32 word")
        self.assertIn("(ival (v0:32 word))", text)
        self.assertIn("(ival (v1:32 word))", text)

    def test_shared_helper_reuses_widths_and_retains_boolean_operand(self):
        source = HEADER + """
val choose : forall 'n, 'n > 0. (bits('n), bits('n), bool) -> bits('n)
function choose(x, y, subtract) = if subtract then sub_bits(x, y) else x + y
val ADD32 : (bits(32), bits(32)) -> bits(32)
function ADD32(x, y) = choose(x, y, false)
val SUB64 : (bits(64), bits(64)) -> bits(64)
function SUB64(x, y) = choose(x, y, true)
"""
        text, deps = self.run_sail(source, roots=("ADD32", "SUB64"))
        workers = re.findall(
            r"let (sail_hl_shared_\w+choose\w*) = new_definition", text)
        self.assertEqual(len(workers), 1, text)
        self.assertIn("(v2:bool)", text)
        self.assertIn("if (v2:bool)", text)
        self.assertIn("word_sub", text)
        self.assertIn("word_add", text)
        self.assertIn(":(N0)word", text)
        for width in (32, 64):
            self.assertRegex(text, rf"\({workers[0]} [^\n]+:{width} word")
        self.assertIn("choose|generic|", deps)
        self.assertNotIn("choose|fixed|", deps)

    def test_shared_doubled_width_instantiates_at_numeral_types(self):
        source = HEADER + """
val doubled : forall 'n, 'n > 0. bits('n) -> bits(2*'n)
function doubled(x) = x @ x
val ROOT : bits(32) -> bits(64)
function ROOT(x) = doubled(x)
"""
        text, deps = self.run_sail(source, roots=("ROOT",))
        worker = self.shared_name(text, "doubled")
        self.assertIn("doubled|generic|", deps)
        self.assertNotIn("doubled|fixed|", deps)
        self.assertIn(":((N0)tybit0)word", text)
        self.assertRegex(text, rf"\({worker} [^\n]+:64 word")

    def test_shared_numeric_width_groups_dimindex_as_an_argument(self):
        source = HEADER + """
val top : forall 'n, 'n > 0. bits('n) -> bits(1)
function top(x) = x['n - 1]
val TOP32 : bits(32) -> bits(1)
function TOP32(x) = top(x)
"""
        text, deps = self.run_sail(source, roots=("TOP32",))
        self.shared_name(text, "top")
        self.assertIn("top|generic|", deps)
        self.assertIn("(& (dimindex(:N0)))", text)
        self.assertNotIn("& dimindex", text)

    def test_shared_other_calculated_widths_specialize_at_numeral_calls(self):
        cases = (
            ("joined", """
val joined : forall 'm 'n, 'm > 0 & 'n > 0.
    (bits('m), bits('n)) -> bits('m + 'n)
function joined(x, y) = x @ y
val ROOT : (bits(4), bits(8)) -> bits(12)
function ROOT(x, y) = joined(x, y)
""", "m=4,n=8", "word_join"),
            ("tripled", """
val tripled : forall 'n, 'n > 0. bits('n) -> bits(3*'n)
function tripled(x) = x @ x @ x
val ROOT : bits(4) -> bits(12)
function ROOT(x) = tripled(x)
""", "n=4", "word_join"),
            ("shortened", """
val shortened : forall 'm 'n, 'm > 'n & 'n > 0.
    (bits('m), bits('n)) -> bits('m - 'n)
function shortened(x, y) = x['m - 'n - 1 .. 0]
val ROOT : (bits(12), bits(4)) -> bits(8)
function ROOT(x, y) = shortened(x, y)
""", "m=12,n=4", "word_subword"),
        )
        for name, source, arguments, operation in cases:
            with self.subTest(name=name):
                text, deps = self.run_sail(HEADER + source, roots=("ROOT",))
                self.shared_name(text, name)
                self.assertIn(name + "|fixed|", deps)
                self.assertIn(arguments + " =>", deps)
                self.assertIn(operation, text)
                for constructor in ("finite_sum", "finite_prod", "finite_diff"):
                    self.assertNotIn(constructor, text)

    def test_shared_state_helper_infers_flexible_boolean_operand(self):
        source = HEADER + """
register D : bits(64)
val write_selected : (bits(64), bool) -> unit
function write_selected(x, invert) = D = if invert then not_vec(x) else x
val ROOT : (bits(64), bits(1)) -> unit
function ROOT(x, invert) = write_selected(x, unsigned(invert) == 1)
"""
        text, deps = self.run_computation(source)
        self.assertRegex(text, r"let sail_hl_shared_\w+write_5fselected\w* = new_definition")
        self.assertIn("(v1:bool)", text)
        self.assertIn("if (v1:bool)", text)
        self.assertIn("word_not", text)
        self.assertIn("(entry:armstate) (s:armstate)", text)
        self.assertIn("(write reg_D", text)
        self.assertIn("write_selected|generic|", deps)

    def test_shared_unit_helper_retains_writes_and_following_read(self):
        source = HEADER + """
register D : bits(64)
register A : bits(64)
val copy_value : bits(64) -> unit
function copy_value(x) = A = x
val ROOT : bits(64) -> unit
function ROOT(x) = {
  copy_value(x);
  D = A
}
"""
        text, deps = self.run_computation(source)
        self.assertIn("copy_value|generic|", deps)
        self.assertIn("(write reg_A", text)
        self.assertIn("(read reg_A", text)
        self.assertIn("(write reg_D", text)

    def test_shared_unit_helper_does_not_hide_unknown_effect(self):
        source = HEADER + """
register D : bits(64)
val opaque = "opaque" : unit -> unit
val copy_value : (bits(64), bool) -> unit
function copy_value(x, selected) =
  if selected then D = x else opaque()
val ROOT : (bits(64), bits(1)) -> unit
function ROOT(x, selected) = copy_value(x, unsigned(selected) == 1)
"""
        self.run_sail(source, roots=("ROOT",),
                      error="unsupported primitive opaque")

    def test_shared_loop_fixes_width_but_keeps_operands(self):
        source = self.computation_fixture("""
val copied : forall 'n, 'n > 0.
  (implicit('n), bits('n)) -> bits('n)
function copied(n, x) = {
    out : bits('n) = undefined;
    foreach (i from 0 to n-1 by 1 in inc) {
        out[i .. i] = x[i .. i]
    };
    out
}
""", "sail_zero_extend(copied(8, x[7 .. 0]),64)")
        text, deps = self.run_computation(source)
        self.assertIn("copied|fixed|", deps)
        self.assertIn("n=8", deps)
        self.assertIn("specialization-required copied|generic|", deps)
        worker = self.shared_name(text, "copied")
        self.assertRegex(text, re.escape(worker) + r" \(v1:8 word\)")
        self.assertEqual(text.count("word_insert"), 8)

    def test_shared_slice_fixes_only_the_required_numeric_argument(self):
        source = HEADER + """
val selected_range : forall 'hi 'lo, 'lo <= 'hi.
  (int, int('hi), int('lo)) -> bits('hi-'lo+1)
function selected_range(value, hi, lo) = get_slice_int(hi-lo+1,value,lo)
val resized : forall 'n, 'n > 0.
  (implicit('n), bits('n)) -> bits('n)
function resized(n, x) = selected_range(unsigned(x), n-1, 0)
val ROOT : bits(32) -> bits(32)
function ROOT(x) = resized(32,x)
"""
        text, deps = self.run_sail(source, roots=("ROOT",))
        self.shared_name(text, "resized")
        worker = self.shared_name(text, "selected_range")
        self.assertIn("resized|generic|", deps)
        selected = [line for line in deps.splitlines()
                    if line.startswith("shared-function selected_range|")]
        self.assertEqual(len(selected), 1, deps)
        self.assertTrue(selected[0].split(" => ")[0].endswith("|lo=0"), deps)
        self.assertRegex(text, re.escape(worker) + r" \(v0:int\) \(v1:int\) =")
        self.assertIn(":(N0)word", text)

    def test_unknown_effect_survives_known_enum_argument(self):
        source = MODEL + """
enum choice = { Plus, Minus }
val touch = impure "touch" : unit -> unit
val select : choice -> unit
function select(op) = {
    D = match op { Plus => A + B, Minus => sub_bits(A, B) };
    touch()
}
val ROOT : unit -> unit
function ROOT() = select(Plus)
"""
        self.run_computation(source, error="unsupported primitive touch")

    def test_rv32_register_contracts_choose_correct_state(self):
        source = HEADER + """
val rX_bits = impure "rX_bits" : bits(5) -> bits(32)
val wX_bits = impure "wX_bits" : (bits(5), bits(32)) -> unit
val add_regs : (bits(5), bits(5), bits(5)) -> unit
function add_regs(rd, rs1, rs2) =
    wX_bits(rd, rX_bits(rs1) + rX_bits(rs2))
"""
        text, deps = self.run_sail(source, roots=("add_regs",),
                                   architecture="rv32")
        self.assertIn("\\(s:riscvstate)", text)
        self.assertIn("(write (riscv_gpr", text)
        self.assertIn("primitive-contract rX_bits", deps)
        self.assertIn("primitive-contract wX_bits", deps)

    def test_result_payload_match_is_exported(self):
        source = HEADER + """
$include <result.sail>
val payload : result(bits(32), bits(32)) -> bits(32)
function payload(value) = match value {
    Ok(data) => data,
    Err(error) => error + 0x00000001
}
"""
        text, _ = self.run_sail(source, roots=("payload",))
        self.assertIn("new_recursive_definition sum_RECURSION", text)
        self.assertIn("sail_hl_result_case", text)
        self.assertIn("32 word+32 word", text)
        self.assertIn("word_add", text)

    def test_result_constructor_is_exported(self):
        source = HEADER + """
$include <result.sail>
val wrap : bits(32) -> result(bits(32), unit)
function wrap(value) = Ok(value)
"""
        text, _ = self.run_sail(source, roots=("wrap",))
        self.assertIn("(INL ", text)
        self.assertIn("32 word+1", text)

    def test_incomplete_result_match_is_rejected(self):
        source = HEADER + """
$include <result.sail>
val payload : result(bits(32), bits(32)) -> bits(32)
function payload(value) = match value { Ok(data) => data }
"""
        self.run_sail(source, roots=("payload",),
                      # Sail adds a match-failure effect to this partial match;
                      # the root is rejected before expression translation.
                      error="state-computation roots must return unit")

    def test_refined_integer_result_root_is_rejected(self):
        source = HEADER + """
$include <result.sail>
val payload : result(int(3), unit) -> int
function payload(value) = match value { Ok(data) => data, Err(_) => 0 }
"""
        self.run_sail(source, roots=("payload",),
                      error="integer root arguments and their refinements are unsupported")

    def test_refined_boolean_result_root_is_rejected(self):
        source = HEADER + """
$include <result.sail>
val payload : result(bool(true), unit) -> bool
function payload(value) = match value { Ok(data) => data, Err(_) => false }
"""
        self.run_sail(source, roots=("payload",),
                      error="refined Boolean root arguments are unsupported")

    # Arm flat memory has explicit checked platform boundaries. These toy
    # declarations describe their type contract; no upstream body is copied
    # or replaced in a fixture. Run the production frontend on every case.
    @staticmethod
    def arm_flat_memory_fixture(body, width=64, declarations=""):
        enums = {
            "AccessType": (
                "IFETCH GPR ASIMD SVE SME IC DC DCZero AT NV2 SPE GCS GPTW TTW",
                "AccessType_"),
            "SecurityState": ("NonSecure Root Realm Secure", "SS_"),
            "MemOp": ("LOAD STORE PREFETCH", "MemOp_"),
            "MemAtomicOp": ("GCSSS1 ADD BIC EOR ORR SMAX SMIN UMAX UMIN SWP CAS",
                            "MemAtomicOp_"),
            "CacheOp": ("Clean Invalidate CleanInvalidate", "CacheOp_"),
            "CacheOpScope": ("SetWay PoU PoC PoE PoP PoDP PoPA ALLU ALLUIS",
                             "CacheOpScope_"),
            "CacheType": ("Data Tag Data_Tag Instruction", "CacheType_"),
            "VARange": ("LOWER UPPER", "VARange_"),
            "PARTIDspaceType": ("Secure Root Realm NonSecure", "PIdSpace_"),
        }
        source = "\n".join(
            f"enum {name} = {{" +
            ", ".join(prefix + member for member in members.split()) + "}"
            for name, (members, prefix) in enums.items())
        source += """
struct MPAMinfo = { mpam_sp : PARTIDspaceType, partid : bits(16), pmg : bits(8) }
struct AccessDescriptor = {
  acctype : AccessType, el : bits(2), ss : SecurityState,
  acqsc : bool, acqpc : bool, relsc : bool, limitedordered : bool,
  exclusive : bool, atomicop : bool, modop : MemAtomicOp,
  nontemporal : bool, read : bool, write : bool, cacheop : CacheOp,
  opscope : CacheOpScope, cachetype : CacheType, pan : bool, transactional : bool,
  nonfault : bool, firstfault : bool, first : bool, contiguous : bool,
  streamingsve : bool, ls64 : bool, mops : bool, rcw : bool, rcws : bool,
  toplevel : bool, varange : VARange, a32lsmd : bool, tagchecked : bool,
  tagaccess : bool, mpam : MPAMinfo
}
val CreateAccDescGPR = impure "gpr_descriptor" :
  (MemOp, bool, bool, bool) -> AccessDescriptor
val CreateAccDescASIMD = impure "asimd_descriptor" :
  (MemOp, bool, bool) -> AccessDescriptor
val BigEndian = impure "byte_order" : AccessType -> bool
val Mem_read = impure "flat_read" : forall 'size, 'size * 8 >= 0.
  (bits(64), int('size), AccessDescriptor) -> bits('size * 8)
val Mem_set = impure "flat_set" : forall 'size, 'size * 8 >= 0.
  (bits(64), int('size), AccessDescriptor, bits('size * 8)) -> unit
val Mem_read__1 = impure "flat_pair_read" : forall 'size, 'size * 8 >= 0.
  (bits(64), int('size), AccessDescriptor, bool) -> bits('size * 8)
val Mem_set__1 = impure "flat_pair_set" : forall 'size, 'size * 8 >= 0.
  (bits(64), int('size), AccessDescriptor, bool, bits('size * 8)) -> unit
val Mem_read__2 = impure "flat_ordered_pair_read" : forall 'size, 'size * 8 >= 0.
  (bits(64), int('size), AccessDescriptor, bool, bool) -> bits('size * 8)
val Mem_set__2 = impure "flat_ordered_pair_set" : forall 'size, 'size * 8 >= 0.
  (bits(64), int('size), AccessDescriptor, bool, bool, bits('size * 8)) -> unit
register A : bits(64)
register Side : bits(64)
"""
        return (source + f"\nregister D : bits({width})\n" + declarations +
                "\nval ADD : unit -> unit\nfunction ADD() = {" + body + "}\n")

    def test_arm_flat_memory_preserves_all_supported_sizes_and_access_events(self):
        for size in (1, 2, 4, 8, 16):
            for load in (True, False):
                with self.subTest(size=size, load=load):
                    operation = "LOAD" if load else "STORE"
                    access = (f"D = Mem_read(A,{size},metadata)" if load else
                              f"Mem_set(A,{size},metadata,D)")
                    source = self.arm_flat_memory_fixture(
                        f"let metadata = CreateAccDescGPR(MemOp_{operation},false,true,true);"
                        + access, width=size * 8)
                    text, deps = self.run_sail(
                        source)
                    self.assertIn(f"memory :> (bytes{size * 8} ", text)
                    self.assertEqual(text.count("EventLoad" if load else "EventStore"), 1)
                    self.assertIn("reg_FlatAccDescGPR:", text)
                    self.assertIn("primitive-contract Arm-flat-access-descriptor", deps)
                    self.assertIn("primitive-contract Arm-total-little-endian-flat-memory", deps)
                    self.assertNotIn("reg_FlatAccDescASIMD:", text)

    def test_arm_flat_memory_does_not_merge_source_lane_accesses(self):
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescASIMD(MemOp_LOAD,false,true);
let first = Mem_read(A,8,metadata);
let second = Mem_read(A + 0x0000000000000008,8,metadata);
D = first + second
""")
        text, deps = self.run_sail(source)
        self.assertEqual(text.count("EventLoad"), 2)
        self.assertEqual(text.count("memory :> (bytes64 "), 2)
        self.assertIn("reg_FlatAccDescASIMD:", text)
        self.assertIn("primitive-contract Mem_read", deps)

    def test_arm_pair_memory_retains_flags_and_original_setter_arity(self):
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescGPR(MemOp_LOAD,false,true,true);
let payload = Mem_read__1(A,8,metadata,true);
Mem_set__1(A,8,metadata,true,payload)
""")
        text, deps = self.run_sail(source)
        self.assertEqual(text.count("EventLoad"), 1)
        self.assertEqual(text.count("EventStore"), 1)
        self.assertIn("primitive-contract Mem_read__1", deps)
        self.assertIn("primitive-contract Mem_set__1", deps)

    def test_arm_memory_descriptor_argument_effects_remain_in_source_order(self):
        source = self.arm_flat_memory_fixture("""
let first = Mem_read(address(),size(),descriptor());
Mem_set(address(),size(),descriptor(),data())
""", declarations="""
val address : unit -> bits(64)
function address() = { Side = 0x0000000000000001; A }
val size : unit -> int(8)
function size() = { Side = 0x0000000000000002; 8 }
val descriptor : unit -> AccessDescriptor
function descriptor() = {
    Side = 0x0000000000000003;
    CreateAccDescASIMD(MemOp_LOAD,false,true)
}
val data : unit -> bits(64)
function data() = { Side = 0x0000000000000004; D }
""")
        text, deps = self.run_sail(source)
        # The four helper definitions are shared; count their actual calls,
        # not copies of the writes in their bodies.
        self.assertEqual(text.count("write reg_Side"), 4)
        for helper in ("address", "size", "descriptor", "data"):
            self.assertIn("inlined " + helper, deps)
        address = self.shared_call_positions(text, "address")
        size = self.shared_call_positions(text, "size")
        descriptor = self.shared_call_positions(text, "descriptor")
        data = self.shared_call_positions(text, "data")
        self.assertEqual(list(map(len, (address, size, descriptor, data))), [2, 2, 2, 1])
        first_access = text.index("EventLoad")
        sequence = [address[0], size[0], descriptor[0], first_access,
                    address[1], size[1], descriptor[1], data[0], text.index("EventStore")]
        self.assertEqual(sequence, sorted(sequence))

    def test_arm_descriptor_factory_keeps_flag_argument_effects(self):
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescGPR(MemOp_LOAD,flag1(),flag2(),flag3());
D = Mem_read(A,8,metadata)
""", declarations="""
val flag1 : unit -> bool
function flag1() = { Side = 0x0000000000000001; false }
val flag2 : unit -> bool
function flag2() = { Side = 0x0000000000000002; true }
val flag3 : unit -> bool
function flag3() = { Side = 0x0000000000000003; true }
""")
        text, _ = self.run_sail(source)
        self.assertEqual(text.count("write reg_Side"), 3)
        self.assertLess(text.index("word 1"), text.index("word 2"))
        self.assertLess(text.index("word 2"), text.index("word 3"))
        self.assertLess(text.index("word 3"), text.index("read reg_FlatAccDescGPR"))

    def test_arm_little_endian_boundary_keeps_access_type_argument_effects(self):
        source = self.arm_flat_memory_fixture("""
let endian = BigEndian(access_type());
Side = if endian then 0x0000000000000002 else 0x0000000000000003
""", declarations="""
val access_type : unit -> AccessType
function access_type() = { Side = 0x0000000000000001; AccessType_GPR }
""")
        text, deps = self.run_sail(source)
        self.assertIn("primitive-contract Arm-little-endian-access", deps)
        self.assertIn("inlined access_type", deps)
        self.assertLess(text.index("word 1"), text.index("word 3"))
        self.assertNotIn("word 2", text)

    def test_arm_memory_rejects_wrong_descriptor_record_and_enum_shapes(self):
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescGPR(MemOp_LOAD,false,true,true);
D = Mem_read(A,8,metadata)
""")
        for old, new, error in (
                ("el : bits(2)", "el : bits(3)", "complete original 33-field shape"),
                ("pmg : bits(8)", "pmg : bits(9)", "complete original 33-field shape"),
                ("MemOp_STORE, MemOp_PREFETCH", "MemOp_STORE",
                 "original MemOp enumeration"),
                ("AccessType_GCS, AccessType_GPTW", "AccessType_GCS",
                 "original AccessType enumeration")):
            with self.subTest(shape=old):
                self.assertIn(old, source)
                self.run_sail(source.replace(old, new), error=error)

    def test_arm_memory_rejects_unsupported_sizes_and_wrong_setter_arity(self):
        for size in (0, 3, 32):
            with self.subTest(size=size):
                source = self.arm_flat_memory_fixture(f"""
let metadata = CreateAccDescGPR(MemOp_LOAD,false,true,true);
D = Mem_read(A,{size},metadata)
""", width=size * 8)
                self.run_sail(source,
                              error="only 1/2/4/8/16-byte accesses")
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescGPR(MemOp_STORE,false,true,true);
Mem_set(A,metadata,D)
""").replace(
            'val Mem_set = impure "flat_set" : forall \'size, \'size * 8 >= 0.\n'
            "  (bits(64), int('size), AccessDescriptor, bits('size * 8)) -> unit",
            'val Mem_set = impure "flat_set" : '
            "(bits(64), AccessDescriptor, bits(64)) -> unit")
        self.run_sail(source,
                      error="wrong primitive arity for Mem_set")

    def test_arm_memory_defined_helpers_are_not_replaced_by_flat_contracts(self):
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescGPR(MemOp_STORE,false,true,true);
Mem_set(A,8,metadata,D)
""", declarations="""
function Mem_set(address,size,metadata,payload) = Side = 0x0000000000000001
""")
        text, deps = self.run_sail(source)
        self.assertIn("write reg_Side", text)
        self.assertIn("inlined Mem_set", deps)
        self.assertNotIn("EventStore", text)
        self.assertNotIn("primitive-contract Arm-total-little-endian-flat-memory", deps)

    def test_arm_memory_ignored_metadata_and_flags_do_not_hide_unknown_effects(self):
        cases = (
            ('val unknown = impure "unknown" : unit -> AccessDescriptor\n',
             "D = Mem_read(A,8,unknown())"),
            ('val unknown = impure "unknown" : unit -> bool\n',
             "let metadata = CreateAccDescGPR(MemOp_LOAD,unknown(),true,true);"
             "D = Mem_read(A,8,metadata)"),
            ('val unknown = impure "unknown" : unit -> bool\n',
             "let metadata = CreateAccDescASIMD(MemOp_LOAD,false,true);"
             "D = Mem_read__1(A,8,metadata,unknown())"),
        )
        for declarations, body in cases:
            with self.subTest(body=body):
                self.run_sail(self.arm_flat_memory_fixture(body, declarations=declarations),
                              error="unsupported primitive unknown")

    def test_arm_memory_rejects_changed_factory_and_data_result_types(self):
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescGPR(MemOp_LOAD,false,true,true);
D = Mem_read(A,8,metadata)
""", width=32).replace(
            "(bits(64), int('size), AccessDescriptor) -> bits('size * 8)",
            "(bits(64), int('size), AccessDescriptor) -> bits(32)")
        self.run_sail(source,
                      error="exact size-dependent data/result type")
        source = self.arm_flat_memory_fixture("""
let metadata = CreateAccDescGPR(MemOp_LOAD,false,true,0b1);
D = Mem_read(A,8,metadata)
""").replace("(MemOp, bool, bool, bool) -> AccessDescriptor",
             "(MemOp, bool, bool, bits(1)) -> AccessDescriptor")
        self.run_sail(source,
                      error="original MemOp and Boolean arguments")


    def test_undefined_rejects_refined_fields_inside_tuples_and_records(self):
        # range(0,0) has one permitted value. Choosing an arbitrary HOL int
        # would incorrectly admit nonzero register results.
        cases = (
            ("", "(range(0,0),bits(64))",
             "let (fixed,other) = unknown(); D = get_slice_int(64,fixed,0)"),
            ("struct Refined = { fixed : range(0,0), other : bits(64) }\n",
             "Refined",
             "let value = unknown(); D = get_slice_int(64,value.fixed,0)"),
        )
        for declarations, result_type, body in cases:
            with self.subTest(result_type=result_type):
                source = declarations + f"""
register D : bits(64)
val unknown : unit -> {result_type}
function unknown() = undefined
val ROOT : unit -> unit
function ROOT() = {{ {body} }}
"""
                self.run_sail(source, roots=("ROOT",), architecture="aarch64",
                              error="arbitrary refined values are unsupported")

    def test_undefined_rejects_dynamic_bitvectors_inside_tuples(self):
        # At size=0 the source value is empty, so its extension must be zero.
        # An unconstrained (width,payload) pair would admit any 64-bit word.
        source = """
register D : bits(64)
val ZeroExtend0 = pure "zero_extend" : forall 'n 'm,
    'n >= 0 & 'm >= 'n. (bits('n),int('m)) -> bits('m)
val unknown : forall 'n, 0 <= 'n & 'n <= 31.
    int('n) -> (bits('n),bits(8))
function unknown(n) = undefined
val ROOT : bits(5) -> unit
function ROOT(size) = {
    let (value,other) = unknown(unsigned(size));
    D = ZeroExtend0(value,64)
}
"""
        self.run_sail(source, roots=("ROOT",), architecture="aarch64",
                      error="arbitrary values require a concrete supported type")

    def test_undefined_evaluations_are_fresh_in_calls_and_loop_iterations(self):
        bodies = (
            "let x = unknown(); let y = unknown(); "
            "assert(x != y); A = x; D = y",
            "foreach (i from 0 to 1) { let x = unknown(); "
            "if i == 1 then assert(x != D); D = x }",
        )
        for body in bodies:
            with self.subTest(body=body):
                source = f"""
register A : bits(64)
register D : bits(64)
val unknown : unit -> bits(64)
function unknown() = undefined
val ROOT : unit -> unit
function ROOT() = {{ {body} }}
"""
                text, deps = self.run_sail(
                    source, roots=("ROOT",), architecture="aarch64")
                choices = re.findall(r"\(\?\(v\d+:64 word\)", text)
                self.assertEqual(len(choices), 2)
                self.assertEqual(len(set(choices)), 2)
                self.assertIn("guarded-assertion", deps)

    def test_nonlocal_control_inside_source_sum_matches_is_refused(self):
        source = """
$include <result.sail>
register D : bits(64)
val EndOfInstruction = impure "stop" : unit -> unit
val ROOT : result(bool,unit) -> unit
function ROOT(value) = match value {
    Ok(flag) => { if flag then EndOfInstruction();
                 D = 0x0000000000000001 },
    Err(_) => D = 0x0000000000000002
}
"""
        self.run_sail(source, roots=("ROOT",), architecture="aarch64",
                      error="unsupported value position")


def run_shard(argument):
    """Run every COUNT-th test, starting at INDEX, as one of COUNT processes.

    The shards of one COUNT partition the tests unittest.main would run.
    Each process builds its own frontend in its own run directory.
    """
    index, count = (int(part) for part in argument.split("/"))
    if not 0 <= index < count:
        raise SystemExit("--shard expects INDEX/COUNT with 0 <= INDEX < COUNT")
    tests = []
    def collect(suite):
        for test in suite:
            if isinstance(test, unittest.TestSuite):
                collect(test)
            else:
                tests.append(test)
    collect(unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__]))
    result = unittest.TextTestRunner().run(unittest.TestSuite(tests[index::count]))
    return result.wasSuccessful()


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--shard":
        sys.exit(0 if run_shard(sys.argv[2]) else 1)
    else:
        unittest.main()
