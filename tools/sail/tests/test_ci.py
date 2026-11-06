#!/usr/bin/env python3
"""CI controller regressions, using fake models/logs, not conformance proofs."""
import collections
import functools
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

import _project
import coverage
import x86_forms

CHECK = _project.ROOT / "ci/check.py"
spec = importlib.util.spec_from_file_location("sail_hol_ci_check", CHECK)
ci = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = ci
spec.loader.exec_module(ci)


def required_arm_theorems(family):
    """Independent use of the complete ledger, including sparse selectors."""
    return tuple(
        variant["theorem"].removesuffix("_EQ") + "_SAFE_EQ"
        if coverage.ARM_FAMILIES[family].get("safe_domain_proofs")
        else variant["theorem"]
        for instruction in coverage.ARM_FAMILIES[family]["instructions"]
        for variant in coverage.arm_instruction_variants(family, instruction))


def model_constants():
    constants = {
        "arm-" + family + ".ml": tuple(sorted({
            variant["constant"]
            for instruction in specification["instructions"]
            for variant in coverage.arm_instruction_variants(family, instruction)
        }))
        for family, specification in coverage.ARM_FAMILIES.items()
    }
    for name in ("rv32.ml", "rv32-control.ml"):
        constants[name] = tuple(sorted({
            ci.rv32_constant(row) for row in coverage.RV32.values()
            if row["model"] + ".ml" == name}))
    for family in ("arithmetic", "shift", "vector"):
        constants["x86-" + family + ".ml"] = tuple(sorted(
            row["constant"] for row in x86_forms.required_forms()
            if row["family"] == family))
    for family in ("arithmetic", "shift"):
        constants["x86-rems-" + family + ".ml"] = tuple(sorted(
            ci.rems_constant(row) for row in x86_forms.required_forms()
            if row["family"] == family and
            x86_forms.export_status(row, "rems") == "available"))
    return constants


def completion(mode):
    if mode == "rv32":
        return "SAIL_HOL_LIGHT_RV32_PROOFS_OK"
    if mode.startswith("x86-"):
        return ("SAIL_HOL_LIGHT_X86_" + mode[4:].upper().replace("-", "_") +
                "_PROOFS_OK")
    return coverage.arm_success_marker(mode.removeprefix("arm-"))


@functools.lru_cache(maxsize=None)
def root_types(name):
    return ci.model_roots(name)


def fixture_definition(name, constant):
    """The fake declaration of one root, as model_fixture writes it."""
    state = ("armstate" if name.startswith("arm-") else
             "riscvstate" if name.startswith("rv32") else "x86state")
    # A memory root also takes configuration components, which validation
    # leaves out of the comparison.
    family = coverage.ARM_FAMILIES.get(name.removeprefix("arm-").removesuffix(".ml"), {})
    parameters = " ".join(
        (["(reg_FlatHaveLSE2:(armstate,bool)component)"]
         if family.get("encoded_signatures_only") else []) +
        [f"(v{index}:{typ})" for index, typ in enumerate(root_types(name)[constant])])
    return (f"let {constant} = new_definition\n `{constant} {parameters} =\n"
            f"    \\(s:{state}) (t:{state}). T`;;\n")


def model_fixture(name, constants):
    """Fake declarations exercise validation, not instruction semantics."""
    return "(* Fake CI header fixture; not a Sail model. *)\n" + "".join(
        fixture_definition(name, constant) for constant in constants)


def proof_fixture(mode):
    # These records deliberately contain no actual instruction statement.
    # Acceptance here checks the controller's log structure, not HOL truth.
    return "".join(name + "\n|- T\n" for name in ci.expected_theorems(mode)) + (
        completion(mode) + "\n")


def use_fixture_statements(test):
    """Point ci.STATEMENTS at checked-in statements matching proof_fixture."""
    directory = tempfile.TemporaryDirectory()
    test.addCleanup(directory.cleanup)
    for mode in ci.modes():
        (Path(directory.name) / (mode + ".txt")).write_text("".join(
            name + "\n|- T\n\n" for name in ci.expected_theorems(mode)))
    statements = patch.object(ci, "STATEMENTS", Path(directory.name))
    statements.start()
    test.addCleanup(statements.stop)
    # These statements name no root; CiStatementRootTests checks roots.
    roots = patch.object(ci, "theorem_roots", lambda: collections.defaultdict(set))
    roots.start()
    test.addCleanup(roots.stop)


class CiTestSelectionTests(unittest.TestCase):
    def test_every_test_file_runs_in_the_generation_job(self):
        # test_backend.py runs as shards.
        files = {path.stem for path in (Path(__file__).parent).glob("test_*.py")}
        self.assertEqual(files, set(ci.UNIT_TESTS) | {"test_backend"})


class CiStatementRootTests(unittest.TestCase):
    """The recorded arm-carry statements, each printed under its name."""

    def setUp(self):
        self.recorded = ci.read_statements(ci.statement_path("arm-carry"))
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        statements = patch.object(ci, "STATEMENTS", Path(self.temporary.name))
        statements.start()
        self.addCleanup(statements.stop)

    def audit(self, recorded):
        (Path(self.temporary.name) / "arm-carry.txt").write_text("".join(
            f"{name}\n{statement}\n\n" for name, statement in recorded.items()))
        lines = "".join(f"{name}\n{statement}\n"
                        for name, statement in recorded.items()).splitlines()
        ci.audit_statements("arm-carry", lines)

    def test_recorded_statements_pass(self):
        self.audit(self.recorded)

    def test_a_statement_about_another_root_fails(self):
        swapped = dict(self.recorded)
        swapped["SAIL_HL_ARM_ADC32_EQ"] = self.recorded["SAIL_HL_ARM_ADC64_EQ"]
        with self.assertRaisesRegex(ValueError, "SAIL_HL_ARM_ADC32_EQ is about"):
            self.audit(swapped)

    def test_a_printer_elision_fails(self):
        elided = dict(self.recorded)
        elided["SAIL_HL_ARM_ADC32_EQ"] = elided["SAIL_HL_ARM_ADC32_EQ"].replace(
            "(WREG' n)", ".")
        with self.assertRaisesRegex(ValueError, "elided"):
            self.audit(elided)


class CiInventoryTests(unittest.TestCase):
    def test_registered_instructions_match_the_independent_public_inventory(self):
        self.assertEqual(ci.public_scope(), (221, 48))

    def test_a_new_public_instruction_cannot_disappear_from_the_ci_scope(self):
        required = ci.inventory()
        for architecture in ("aarch64", "rv32im"):
            changed = {
                key: dict(value, instructions=list(value["instructions"]))
                for key, value in required.items()}
            changed[architecture]["instructions"].append(
                {"hol": "new_unregistered_instruction"})
            with self.subTest(architecture=architecture), patch.object(
                    ci, "inventory", return_value=changed), \
                    self.assertRaises(ValueError):
                ci.public_scope()

    def test_a_non_public_registered_instruction_is_refused(self):
        required = ci.inventory()
        changed = {
            key: dict(value, instructions=list(value["instructions"]))
            for key, value in required.items()}
        changed["aarch64"]["instructions"].pop()
        with patch.object(ci, "inventory", return_value=changed), \
                self.assertRaises(ValueError):
            ci.public_scope()

    def test_modes_include_all_arm_rv_and_five_x86_suites(self):
        expected = {"arm-" + family for family in coverage.ARM_FAMILIES} | {
            "rv32", "x86-arithmetic", "x86-shift", "x86-vector",
            "x86-rems-arithmetic", "x86-rems-shift"}
        self.assertEqual(set(ci.modes()), expected)
        self.assertEqual(len(ci.modes()), len(expected))
        self.assertEqual(len(expected), 75)

    def test_rems_suites_require_agreement_or_a_counterexample(self):
        theorems = ci.expected_theorems("x86-rems-arithmetic")
        self.assertEqual(len(set(theorems)), len(theorems))
        for name in ("SAIL_HL_X86_REMS_ADD64_RR_EQ",
                     "SAIL_HL_X86_REMS_IMUL18_LEGACY_R_EQ"):
            self.assertIn(name, theorems)
        # ADCX has no REMS body, so there is nothing to compare.
        self.assertNotIn("SAIL_HL_X86_REMS_ADCX64_RR_EQ", theorems)
        self.assertEqual(len(theorems), 78)
        # Shifts: 22 REMS agreements and 19 REMS counterexamples.
        shift = ci.expected_theorems("x86-rems-shift")
        self.assertEqual(len(shift), 22 + 19)
        self.assertIn("SAIL_HL_X86_REMS_SHL8_LEGACY_RI_EQ", shift)
        self.assertIn("SAIL_HL_X86_REMS_ROR64_RI_DIFF", shift)
        self.assertIn("SAIL_HL_X86_REMS_ROR8_RI_DIFF", shift)
        self.assertIn("SAIL_HL_X86_REMS_RCR8_LEGACY_RI_DIFF", shift)

    def test_model_names_are_the_exact_registered_ml_inputs(self):
        expected = set(model_constants())
        self.assertEqual(set(ci.model_names()), expected)
        self.assertEqual(len(ci.model_names()), len(expected))
        self.assertEqual(len(expected), 76)
        self.assertIn("x86-rems-shift.ml", expected)
        self.assertNotIn("x86-rems-vector.ml", expected)
        self.assertNotIn("arm.ml", expected)
        self.assertNotIn("enums.ml", expected)
        self.assertIn("arm-memory-single.ml", expected)
        self.assertNotIn("arm-vector-polynomial-widen-bytes.ml", expected)

    def test_every_arm_form_and_rv_instruction_has_one_required_marker(self):
        arm_markers = []
        for family in coverage.ARM_FAMILIES:
            with self.subTest(family=family):
                expected = required_arm_theorems(family)
                actual = ci.expected_theorems("arm-" + family)
                self.assertEqual(set(actual), set(expected))
                self.assertEqual(len(actual), len(expected))
                arm_markers.extend(actual)
        self.assertEqual(len(arm_markers), 1404)
        self.assertEqual(len(set(arm_markers)), 1404)
        guarded = ("LH", "LHU", "LW", "SH", "SW", "BEQ", "BNE", "BLT", "BGE",
                   "BLTU", "BGEU", "JAL", "JALR")
        expected_rv = {"SAIL_HL_RV32_" + name + (
            "_SAFE_EQ" if name in guarded else
            "_DIFF" if name in ("ECALL", "EBREAK") else "_EQ")
            for name in coverage.RV32}
        self.assertEqual(set(ci.expected_theorems("rv32")), expected_rv)
        self.assertEqual(len(ci.expected_theorems("rv32")), 50)

    def test_addsub_requires_all_512_forms(self):
        names = ci.expected_theorems("arm-addsub")
        self.assertEqual(len(names), 512)
        self.assertEqual(len(set(names)), 512)
        for required in (
                "SAIL_HL_ARM_ADDS32_IMM_EQ",
                "SAIL_HL_ARM_ADDS64_SHIFT_EQ",
                "SAIL_HL_ARM_ADD32_EXT_UXTX_0_EQ",
                "SAIL_HL_ARM_SUBS64_EXT_SXTX_4_EQ"):
            self.assertIn(required, names)

    def test_compare_requires_four_universal_selector_claims_not_eight_exports(self):
        self.assertEqual(set(ci.expected_theorems("arm-compare")), {
            "SAIL_HL_ARM_CCMN32_EQ", "SAIL_HL_ARM_CCMN64_EQ",
            "SAIL_HL_ARM_CCMP32_EQ", "SAIL_HL_ARM_CCMP64_EQ",
        })
        self.assertEqual(len(ci.expected_theorems("arm-compare")), 4)

    def test_unknown_or_deferred_modes_do_not_acquire_proof_credit(self):
        for mode in ("arm-memory-unsupported", "arm-branch-unconditional",
                     "x86-missing", "x86", "enums", "arm", "nope"):
            with self.subTest(mode=mode), self.assertRaises((ValueError, KeyError)):
                ci.expected_theorems(mode)

    def test_every_x86_form_requires_equality_or_a_closed_counterexample(self):
        forms = x86_forms.required_forms()
        claims = []
        for family in ("arithmetic", "shift", "vector"):
            expected = tuple(
                row["theorem"].removesuffix("_EQ") + suffix
                for row in forms if row["family"] == family
                for suffix in (("_DIFF", "_EXACT")
                               if x86_forms.known_gap(row) else ("_EQ",)))
            self.assertEqual(ci.expected_theorems("x86-" + family), expected)
            claims.extend(expected)
        # A gap form needs a counterexample and its exact relation.
        self.assertEqual(len(claims), 211)
        self.assertEqual(len(set(claims)), 211)
        self.assertEqual(sum(name.endswith("_EQ") for name in claims), 199)
        self.assertEqual(sum(name.endswith("_DIFF") for name in claims), 6)
        self.assertEqual({name.removesuffix("_DIFF") for name in claims
                          if name.endswith("_DIFF")},
                         {name.removesuffix("_EXACT") for name in claims
                          if name.endswith("_EXACT")})

    def test_corrected_shift_forms_cannot_use_old_counterexample_reports(self):
        required = ci.expected_theorems("x86-shift")
        for root in ("SHL8_RI", "SHL8_LEGACY_RI", "SHL16_RI",
                     "SHR8_RI", "SHR8_LEGACY_RI", "SHR16_RI",
                     "SHLD16_RRI", "SHRD16_RRI"):
            self.assertIn("SAIL_HL_X86_" + root + "_EQ", required)
            self.assertNotIn("SAIL_HL_X86_" + root + "_DIFF", required)

    def test_missing_requested_x86_public_definition_is_refused(self):
        with patch.object(ci, "validate_public_scope", side_effect=ValueError(
                "requested x86 HOL definitions missing")), self.assertRaises(ValueError):
            ci.public_scope()


class CiModelTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.expected = self.root / "expected"
        self.actual = self.root / "actual"
        self.expected.mkdir()
        self.actual.mkdir()
        self.constants = model_constants()
        for name, constants in self.constants.items():
            source = model_fixture(name, constants)
            for directory in (self.expected, self.actual):
                (directory / name).write_text(source)
                (directory / name).with_suffix(".dependencies").write_text(
                    "".join("root " + constant + "\n" for constant in constants))

    def test_dependency_reports_are_required_and_compared_byte_exactly(self):
        path = self.actual / "arm-carry.dependencies"
        original = path.read_bytes()
        path.write_bytes(original + b"primitive-contract changed\n")
        with self.assertRaisesRegex(ValueError, "arm-carry.dependencies"):
            ci.compare_models(self.actual, self.expected)
        path.unlink()
        with self.assertRaisesRegex(ValueError, "dependency report inventory"):
            ci.compare_models(self.actual, self.expected)
        path.write_bytes(original)
        ci.compare_models(self.actual, self.expected)

    def test_complete_fixture_sets_and_exact_bytes_pass(self):
        ci.validate_models(self.expected)
        ci.validate_models(self.actual)
        ci.compare_models(self.actual, self.expected)

    def test_missing_model_is_refused_in_either_set(self):
        for directory in (self.actual, self.expected):
            path = directory / "arm-addsub.ml"
            original = path.read_bytes()
            path.unlink()
            with self.subTest(directory=directory), self.assertRaises(ValueError):
                ci.compare_models(self.actual, self.expected)
            path.write_bytes(original)

    def test_extra_model_is_refused_in_either_set(self):
        for directory in (self.actual, self.expected):
            path = directory / "arm-memory-single.ml"
            path.write_text("(* Unregistered fake model. *)\n")
            with self.subTest(directory=directory), self.assertRaises(ValueError):
                ci.compare_models(self.actual, self.expected)
            path.unlink()

    def test_missing_expected_constant_is_refused_for_every_model(self):
        for name, constants in self.constants.items():
            with self.subTest(model=name):
                path = self.actual / name
                original = path.read_text()
                path.write_text(original.replace(constants[0], "missing_constant"))
                with self.assertRaises(ValueError):
                    ci.validate_models(self.actual)
                path.write_text(original)

    def test_unchanged_name_with_changed_bytes_is_refused(self):
        path = self.actual / "arm-addsub.ml"
        path.write_bytes(path.read_bytes() + b"(* changed byte baseline *)\n")
        with self.assertRaises(ValueError):
            ci.compare_models(self.actual, self.expected)

    def test_a_commented_definition_does_not_supply_a_required_constant(self):
        name = "arm-compare.ml"
        constant = self.constants[name][0]
        path = self.actual / name
        source = path.read_text()
        definition = fixture_definition(name, constant)
        self.assertIn(definition, source)
        path.write_text(source.replace(
            definition, "(* outer (* nested *)\n" + definition + "*)\n"))
        with self.assertRaises(ValueError):
            ci.validate_models(self.actual)

    def test_arm_and_rv32_root_types_must_match_coverage(self):
        for name, constant, original, changed in (
                ("arm-bitfield.ml", self.constants["arm-bitfield.ml"][0],
                 "(v0:5 word)", "(v0:6 word)"),
                ("arm-carry.ml", "sail_hl_ARM_5fADC64", " (v2:5 word)", ""),
                ("rv32.ml", "sail_hl_rv_5fLOAD_5fLW", "(v0:12 word)", "(v0:13 word)")):
            path = self.actual / name
            source = path.read_text()
            definition = fixture_definition(name, constant)
            self.assertIn(original, definition)
            path.write_text(source.replace(
                definition, definition.replace(original, changed)))
            with self.subTest(model=name), self.assertRaisesRegex(
                    ValueError, "signatures differ"):
                ci.validate_models(self.actual)
            path.write_text(source)

    def test_symlink_and_directory_models_are_refused(self):
        path = self.actual / "arm-compare.ml"
        original = path.read_bytes()
        path.unlink()
        path.symlink_to(self.expected / path.name)
        with self.assertRaises(ValueError):
            ci.validate_models(self.actual)
        path.unlink()
        path.mkdir()
        with self.assertRaises(ValueError):
            ci.validate_models(self.actual)
        path.rmdir()
        path.write_bytes(original)

    def test_line_endings_and_final_newline_are_compared_byte_exactly(self):
        path = self.actual / "arm-compare.ml"
        original = path.read_bytes()
        for changed in (original.replace(b"\n", b"\r\n"), original.rstrip(b"\n")):
            with self.subTest(change=changed[-20:]), self.assertRaises(ValueError):
                path.write_bytes(changed)
                ci.compare_models(self.actual, self.expected)
        path.write_bytes(original)

    def test_x86_instruction_types_and_count_domains_cannot_be_narrowed(self):
        for filename, original, changed in (
                ("x86-arithmetic.ml", "(v0:3 word)", "(v0:4 word)"),
                ("x86-shift.ml", "(v1:8 word)", "(v1:5 word)"),
                ("x86-vector.ml", "(v0:4 word)", "(v0:3 word)")):
            path = self.actual / filename
            source = path.read_text()
            self.assertIn(original, source)
            path.write_text(source.replace(original, changed, 1))
            with self.subTest(model=filename), self.assertRaises(ValueError):
                ci.validate_models(self.actual)
            path.write_text(source)

    def test_extra_and_duplicate_roots_are_refused(self):
        for name, state in (("x86-shift.ml", "x86state"), ("arm-carry.ml", "armstate"),
                            ("rv32.ml", "riscvstate")):
            path = self.actual / name
            original = path.read_text()
            for extra in (fixture_definition(name, self.constants[name][0]),
                          "let sail_hl_EXTRA = new_definition\n"
                          f" `sail_hl_EXTRA = \\(s:{state}) (t:{state}). T`;;\n",
                          "let sail_hl_EXTRA = new_definition\n"
                          " `sail_hl_EXTRA = T`;;\n"):
                path.write_text(original + extra)
                with self.subTest(model=name, extra=extra[:90]), \
                        self.assertRaises(ValueError):
                    ci.validate_models(self.actual)
            path.write_text(original)

    def test_extra_nonword_x86_parameters_are_not_ignored(self):
        path = self.actual / "x86-arithmetic.ml"
        source = path.read_text()
        for parameter in ("(extra:int)", "(extra:(int#bool))"):
            path.write_text(source.replace("(v0:4 word)",
                                           "(v0:4 word) " + parameter, 1))
            with self.subTest(parameter=parameter), self.assertRaises(ValueError):
                ci.validate_models(self.actual)
        path.write_text(source)


class CiProofLogTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.log = Path(self.temporary.name) / "fake-proof.log"
        use_fixture_statements(self)

    def test_a_changed_statement_is_refused(self):
        mode = "x86-shift"
        name = ci.expected_theorems(mode)[0]
        source = proof_fixture(mode).replace(name + "\n|- T\n", name + "\n|- F\n", 1)
        with self.assertRaisesRegex(ValueError, "statements differ"):
            self.audit(mode, source)
        # A continuation line is part of the statement too.
        source = proof_fixture(mode).replace(name + "\n|- T\n", name + "\n|- T\n  /\\ F\n", 1)
        with self.assertRaisesRegex(ValueError, "statements differ"):
            self.audit(mode, source)

    def test_one_forms_theorem_under_another_name_is_refused(self):
        mode = "x86-shift"
        first, second = ci.expected_theorems(mode)[:2]
        (ci.STATEMENTS / (mode + ".txt")).write_text("".join(
            name + "\n|- " + name + "\n\n" for name in ci.expected_theorems(mode)))
        source = "".join(name + "\n|- " + name + "\n" for name in ci.expected_theorems(mode))
        source = source.replace(second + "\n|- " + second, second + "\n|- " + first)
        with self.assertRaisesRegex(ValueError, "statements differ"):
            self.audit(mode, source + completion(mode) + "\n")

    def test_missing_or_incomplete_statement_files_are_refused(self):
        mode = "rv32"
        path = ci.STATEMENTS / (mode + ".txt")
        lines = path.read_text().split("\n\n")
        path.write_text("\n\n".join(lines[1:]))
        with self.assertRaisesRegex(ValueError, "does not list exactly"):
            self.audit(mode, proof_fixture(mode))
        path.unlink()
        with self.assertRaisesRegex(ValueError, "no checked-in theorem statements"):
            self.audit(mode, proof_fixture(mode))

    def test_refreshed_statements_are_the_printed_ones(self):
        logs = Path(self.temporary.name) / "logs"
        logs.mkdir()
        for mode in ci.modes():
            (logs / (mode + "-proof.log")).write_text(proof_fixture(mode).replace(
                "\n|- T\n", "\n|- T\n    continued\n"))
        with redirect_stdout(io.StringIO()):
            ci.refresh_statements(logs)
        for mode in ci.modes():
            self.audit(mode, (logs / (mode + "-proof.log")).read_text())
            recorded = ci.read_statements(ci.statement_path(mode))
            self.assertEqual(set(recorded.values()), {"|- T\n    continued"})

    def test_selected_statements_are_refreshed_alone(self):
        logs = Path(self.temporary.name) / "logs"
        logs.mkdir()
        mode = ci.modes()[0]
        (logs / (mode + "-proof.log")).write_text(proof_fixture(mode).replace(
            "\n|- T\n", "\n|- T\n    selected\n"))
        others = {other: ci.statement_path(other).read_text()
                  for other in ci.modes() if other != mode}
        with redirect_stdout(io.StringIO()):
            ci.refresh_statements(logs, (mode,))
        recorded = ci.read_statements(ci.statement_path(mode))
        self.assertEqual(set(recorded.values()), {"|- T\n    selected"})
        for other, text in others.items():
            self.assertEqual(ci.statement_path(other).read_text(), text)
        with self.assertRaisesRegex(ValueError, "unknown proof suites"):
            ci.refresh_statements(logs, ("carry",))

    def audit(self, mode, source):
        self.log.write_text(source)
        ci.audit_proof(mode, self.log)

    def test_all_registered_modes_accept_complete_closed_fixture_logs(self):
        for mode in ci.modes():
            with self.subTest(mode=mode):
                self.audit(mode, proof_fixture(mode))

    def test_all_512_addsub_markers_are_required_even_after_completion(self):
        mode = "arm-addsub"
        source = proof_fixture(mode)
        for name in ci.expected_theorems(mode):
            with self.subTest(marker=name), self.assertRaises(ValueError):
                self.audit(mode, source.replace(name + "\n|- T\n", "", 1))

    def test_all_four_compare_selector_claims_are_required(self):
        mode = "arm-compare"
        source = proof_fixture(mode)
        for name in ci.expected_theorems(mode):
            with self.subTest(marker=name), self.assertRaises(ValueError):
                self.audit(mode, source.replace(name + "\n|- T\n", "", 1))

    def test_each_rv_marker_is_required(self):
        source = proof_fixture("rv32")
        for name in ci.expected_theorems("rv32"):
            with self.subTest(marker=name), self.assertRaises(ValueError):
                self.audit("rv32", source.replace(name + "\n|- T\n", "", 1))

    def test_duplicate_theorem_marker_is_refused(self):
        for mode in ("arm-compare", "arm-addsub", "rv32", "x86-shift"):
            name = ci.expected_theorems(mode)[0]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.audit(mode, name + "\n|- T\n" + proof_fixture(mode))

    def test_unexpected_equivalence_marker_is_refused(self):
        for mode in ("arm-compare", "rv32", "x86-vector"):
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.audit(mode, "SAIL_HL_ARM_UNREGISTERED_EQ\n|- T\n" +
                           proof_fixture(mode))

    def test_missing_or_duplicate_completion_is_refused(self):
        mode = "arm-compare"
        source = proof_fixture(mode)
        for changed in (
                source.replace(completion(mode) + "\n", ""),
                source + completion(mode) + "\n"):
            with self.subTest(log=changed[-100:]), self.assertRaises(ValueError):
                self.audit(mode, changed)

    def test_a_marker_without_a_printed_closed_theorem_is_refused(self):
        mode = "arm-compare"
        source = proof_fixture(mode)
        name = ci.expected_theorems(mode)[0]
        for replacement in ("", "T\n", "assumption |- T\n", "assumption\n|- T\n"):
            changed = source.replace(name + "\n|- T\n", name + "\n" + replacement, 1)
            with self.subTest(theorem=replacement), self.assertRaises(ValueError):
                self.audit(mode, changed)

    def test_a_later_closed_line_cannot_hide_initial_hypotheses(self):
        mode = "arm-compare"
        name = ci.expected_theorems(mode)[0]
        changed = proof_fixture(mode).replace(
            name + "\n|- T\n", name + "\nassumption |- T\n|- T\n", 1)
        with self.assertRaises(ValueError):
            self.audit(mode, changed)

    def test_closed_theorem_without_its_exact_marker_is_refused(self):
        mode = "arm-compare"
        name = ci.expected_theorems(mode)[0]
        changed = proof_fixture(mode).replace(name + "\n", "", 1)
        with self.assertRaises(ValueError):
            self.audit(mode, changed)

    def test_progress_messages_do_not_replace_an_equivalence_marker(self):
        source = "SAIL_HOL_LIGHT_ARM_COMPARE_FIRST_EQ_PROVED\n"
        source += proof_fixture("arm-compare")
        self.audit("arm-compare", source)
        missing = source.replace(
            ci.expected_theorems("arm-compare")[0] + "\n|- T\n", "", 1)
        with self.assertRaises(ValueError):
            self.audit("arm-compare", missing)

    def test_memory_requires_safe_agreement(self):
        mode = "arm-memory-single"
        source = proof_fixture(mode)
        name = next(name for name in ci.expected_theorems(mode)
                    if name.endswith("_SAFE_EQ"))
        with self.assertRaises(ValueError):
            self.audit(mode, source.replace(name + "\n|- T\n", "", 1))

    def test_rems_reports_are_required(self):
        mode = "x86-rems-arithmetic"
        source = proof_fixture(mode)
        self.audit(mode, source)
        for name in ci.expected_theorems(mode):
            with self.subTest(marker=name), self.assertRaises(ValueError):
                self.audit(mode, source.replace(name + "\n|- T\n", "", 1))

    def test_all_205_x86_reports_are_required_after_completion(self):
        for mode in ("x86-arithmetic", "x86-shift", "x86-vector"):
            source = proof_fixture(mode)
            for name in ci.expected_theorems(mode):
                with self.subTest(marker=name), self.assertRaises(ValueError):
                    self.audit(mode, source.replace(name + "\n|- T\n", "", 1))

    def test_known_gap_text_does_not_supply_its_missing_kernel_counterexample(self):
        mode = "x86-shift"
        source = proof_fixture(mode)
        for name in ci.expected_theorems(mode):
            if not name.endswith("_DIFF"):
                continue
            changed = source.replace(name + "\n|- T\n",
                                     "Known documented gap: " + name + "\n", 1)
            with self.subTest(marker=name), self.assertRaises(ValueError):
                self.audit(mode, changed)

    def test_corrected_shifts_refuse_counterexamples_instead_of_agreement(self):
        mode = "x86-shift"
        source = proof_fixture(mode)
        for root in ("SHL8_RI", "SHL8_LEGACY_RI", "SHL16_RI",
                     "SHR8_RI", "SHR8_LEGACY_RI", "SHR16_RI",
                     "SHLD16_RRI", "SHRD16_RRI"):
            name = "SAIL_HL_X86_" + root + "_EQ"
            with self.subTest(marker=name), self.assertRaises(ValueError):
                self.audit(mode, source.replace(name, name.removesuffix("_EQ") + "_DIFF"))

    def test_agreement_and_difference_labels_are_not_interchangeable(self):
        for mode, suffix, other in (
                ("x86-shift", "_DIFF", "_EQ"),
                ("x86-arithmetic", "_EQ", "_DIFF")):
            source = proof_fixture(mode)
            name = next(name for name in ci.expected_theorems(mode)
                        if name.endswith(suffix))
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.audit(mode, source.replace(name, name.removesuffix(suffix) + other))

    def test_inline_and_two_line_closed_reports_are_checked_the_same_way(self):
        for mode in ("arm-compare", "rv32", "x86-shift", "x86-vector"):
            source = proof_fixture(mode).replace("\n|- T\n", ": |- T\n")
            self.audit(mode, source)
            name = ci.expected_theorems(mode)[0]
            for changed in (
                    source.replace(name + ": |- T", name + ": assumed |- T", 1),
                    source.replace(name + ": |- T", name + ": proved", 1),
                    name + "\n|- T\n" + source):
                with self.subTest(mode=mode), self.assertRaises(ValueError):
                    self.audit(mode, changed)


class CiCommandAndGuardTests(unittest.TestCase):
    """Fake subprocess statuses and temporary bytes do not verify native HOL."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.log = self.root / "fake-command.log"

    def fake_process(self, code):
        def result(command, **keywords):
            keywords["stdout"].write(proof_fixture("arm-compare").encode())
            return subprocess.CompletedProcess(command, code)
        return result

    def test_nonzero_or_signalled_native_status_cannot_accept_success_markers(self):
        for code in (1, 17, -11):
            with self.subTest(code=code), patch.object(
                    ci.subprocess, "run", side_effect=self.fake_process(code)), \
                    redirect_stdout(io.StringIO()), self.assertRaises(RuntimeError):
                ci.run(["fake-native"], self.log, cwd=self.root)
            self.assertIn(completion("arm-compare"), self.log.read_text())

    def test_a_live_or_unknown_process_result_is_not_a_terminal_success(self):
        with patch.object(ci.subprocess, "run", side_effect=self.fake_process(None)), \
                redirect_stdout(io.StringIO()), self.assertRaises(RuntimeError):
            ci.run(["fake-native"], self.log, cwd=self.root)

    def test_zero_status_is_required_but_does_not_itself_audit_a_proof(self):
        with patch.object(ci.subprocess, "run", side_effect=self.fake_process(0)), \
                redirect_stdout(io.StringIO()):
            ci.run(["fake-native"], self.log, cwd=self.root)
        self.assertIn(completion("arm-compare"), self.log.read_text())

    def test_source_and_model_mutations_are_refused_by_the_same_guard(self):
        source = self.root / "source.ml"
        model = self.root / "model.ml"
        source.write_text("(* Fake source fixture. *)\n")
        model.write_text("(* Fake model fixture. *)\n")
        snapshot = ci.guard((source, model))
        ci.unchanged(snapshot)
        for path in (source, model):
            original = path.read_bytes()
            path.write_bytes(original + b"changed\n")
            with self.subTest(path=path), self.assertRaises(ValueError):
                ci.unchanged(snapshot)
            path.write_bytes(original)
            ci.unchanged(snapshot)

    def test_missing_guarded_input_is_refused(self):
        source = self.root / "source.ml"
        source.write_text("(* Fake source fixture. *)\n")
        snapshot = ci.guard((source,))
        source.unlink()
        with self.assertRaises(ValueError):
            ci.unchanged(snapshot)


class CiGenerationTests(unittest.TestCase):
    """All subprocesses and model bodies are fake controller fixtures."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        workspace = patch.object(ci, "WORK", self.root / "ci")
        workspace.start()
        self.addCleanup(workspace.stop)
        environment = patch.dict(os.environ, {
            name: "/fake/" + name for name in
            ("SAIL_DIR", "SAIL_EXE", "SAIL_ARM_DIR", "SAIL_RISCV_DIR",
             "SAIL_X86_SHINA_DIR", "SAIL_X86_REMS_DIR")}, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        # The excluded-input check reads the real Arm checkout; it has its
        # own tests below.
        exclusions = patch.object(ci, "check_arm_exclusions")
        exclusions.start()
        self.addCleanup(exclusions.stop)
        self.calls = []

    def fake_generation(self, command, log, env=None, cwd=None):
        self.calls.append((command, env))
        Path(log).write_text("Mocked generation command; no Sail was run.\n")
        if Path(command[1]).name != "run.sh":
            return
        architecture = command[2]
        output = Path(command[command.index("--hol-light-output-dir") + 1])
        for name, constants in model_constants().items():
            if ((architecture == "arm" and name.startswith("arm-")) or
                (architecture == "rv32" and name.startswith("rv32")) or
                (architecture == "x86-rems" and name.startswith("x86-rems-")) or
                (architecture == "x86-shina" and name.startswith("x86-") and
                 not name.startswith("x86-rems-"))):
                (output / name).write_text(model_fixture(name, constants))
                (output / name).with_suffix(".dependencies").write_text(
                    "root " + constants[0] + "\n" if constants else "")

    def generate(self, action=None):
        with patch.object(ci, "run", side_effect=action or self.fake_generation), \
                redirect_stdout(io.StringIO()):
            return ci.generate_models()

    def test_default_generation_builds_once_and_runs_each_architecture_once(self):
        output = self.generate()
        ci.validate_models(output)
        commands = [command for command, _ in self.calls]
        self.assertEqual(sum(Path(command[1]).name == "build.sh"
                             for command in commands), 1)
        self.assertEqual(sum(Path(command[1]).name == "test_ci.py"
                             for command in commands), 1)
        launches = [command for command in commands
                    if Path(command[1]).name == "run.sh"]
        for command in launches:
            self.assertEqual(command[command.index("--hol-light-jobs") + 1], "16")
        for command, environment in self.calls:
            if Path(command[1]).name == "run.sh":
                self.assertEqual(environment.get("SAIL_ARM_EXCLUDED_INPUTS"),
                                 " ".join(ci.ARM_EXCLUDED_INPUTS)
                                 if command[2] == "arm" else None)
                self.assertEqual(environment["OCAMLRUNPARAM"], "o=400")
        # The architectures run concurrently, so their call order is free.
        self.assertEqual(sorted(command[2] for command in launches),
                         ["arm", "rv32", "x86-rems", "x86-shina"])
        self.assertEqual({command[2]: command[3] for command in launches
                          if command[2].startswith("x86-")},
                         {"x86-shina": "all", "x86-rems": "all"})
        # Only Arm families have warm-up workers, and only registered ones.
        for command in launches:
            warmups = [command[index + 1] for index, argument in enumerate(command)
                       if argument == "--hol-light-warmup"]
            if command[2] != "arm":
                self.assertEqual(warmups, [])
                continue
            self.assertEqual(len(warmups), len(ci.ARM_WARMUPS))
            for warmup in warmups:
                stem, count = warmup.split("=")
                self.assertIn(stem.removeprefix("arm-"), ci.ARM_FAMILIES)
                self.assertGreater(int(count), 0)
        # Backend test shards must together cover the whole suite.
        shards = sorted(command[3] for command in commands
                        if Path(command[1]).name == "test_backend.py")
        self.assertGreater(len(shards), 1)
        self.assertEqual(shards, sorted(f"{index}/{len(shards)}"
                                        for index in range(len(shards))))
        memos = [command[command.index("--memo-z3-path") + 1] for command in launches]
        self.assertEqual(len(set(memos)), 4)
        for command, environment in self.calls:
            if Path(command[1]).name == "run.sh":
                for source in ("SHINA", "REMS"):
                    variable = "SAIL_X86_" + source + "_DIR"
                    self.assertEqual(environment[variable], "/fake/" + variable)
        self.assertEqual(len(list(output.glob("*.ml"))), 76)

    def test_arm_model_reaching_an_excluded_decoder_is_refused(self):
        def reaching(command, log, env=None, cwd=None, timeout=None):
            self.fake_generation(command, log, env, cwd)
            if Path(command[1]).name == "run.sh" and command[2] == "arm":
                output = Path(command[command.index("--hol-light-output-dir") + 1])
                (output / "arm-addsub.dependencies").write_text(
                    "inlined __DecodeA64_SVE\n")
        with self.assertRaisesRegex(ValueError, "__DecodeA64_SVE"):
            self.generate(reaching)

    def test_arm_model_without_dependency_record_is_refused(self):
        def unrecorded(command, log, env=None, cwd=None, timeout=None):
            self.fake_generation(command, log, env, cwd)
            if Path(command[1]).name == "run.sh" and command[2] == "arm":
                output = Path(command[command.index("--hol-light-output-dir") + 1])
                (output / "arm-addsub.dependencies").unlink()
        with self.assertRaisesRegex(ValueError, "arm-addsub.dependencies"):
            self.generate(unrecorded)

    def test_generation_job_count_is_checked_before_any_command(self):
        for jobs in ("0", "65"):
            with self.subTest(jobs=jobs), patch.dict(
                    os.environ, {"SAIL_HOL_GENERATION_JOBS": jobs}):
                with self.assertRaises(ValueError):
                    self.generate()
                self.assertEqual(self.calls, [])

    def test_missing_external_x86_checkout_is_refused_before_any_command(self):
        for variable in ("SAIL_X86_SHINA_DIR", "SAIL_X86_REMS_DIR"):
            with self.subTest(variable=variable), patch.dict(os.environ):
                del os.environ[variable]
                with self.assertRaises(ValueError):
                    self.generate()
                self.assertEqual(self.calls, [])

    def test_missing_or_extra_rems_root_is_refused_after_mocked_generation(self):
        absent = next(row for row in x86_forms.required_forms()
                      if x86_forms.export_status(row, "rems") == "absent")
        available = next(row for row in x86_forms.required_forms()
                         if row["family"] == "shift" and
                         x86_forms.export_status(row, "rems") == "available")
        for old, new in ((ci.rems_constant(available), "sail_hl_X86_5fREMS_5fABSENT"),
                         (ci.rems_constant(available), ci.rems_constant(absent))):
            def changed(command, log, env=None, cwd=None, timeout=None):
                self.fake_generation(command, log, env, cwd)
                if Path(command[1]).name == "run.sh" and command[2] == "x86-rems":
                    output = Path(command[command.index("--hol-light-output-dir") + 1])
                    path = output / "x86-rems-shift.ml"
                    path.write_text(path.read_text().replace(old, new))
            with self.subTest(new=new), self.assertRaises(ValueError):
                self.generate(changed)

    def test_missing_known_gap_export_is_refused_after_mocked_generation(self):
        def incomplete(command, log, env=None, cwd=None, timeout=None):
            self.fake_generation(command, log, env, cwd)
            if Path(command[1]).name == "run.sh" and command[2] == "x86-shina":
                output = Path(command[command.index("--hol-light-output-dir") + 1])
                path = output / "x86-shift.ml"
                source = path.read_text()
                missing = next(row["constant"] for row in x86_forms.required_forms()
                               if x86_forms.known_gap(row))
                path.write_text(source.replace(missing, "absent_gap_export"))
        with self.assertRaises(ValueError):
            self.generate(incomplete)

    def test_x86_generation_failure_is_not_replaced_by_mocked_successful_outputs(self):
        def failed(command, log, env=None, cwd=None, timeout=None):
            self.fake_generation(command, log, env, cwd)
            if Path(command[1]).name == "run.sh" and command[2] == "x86-rems":
                raise RuntimeError("mocked x86 generation failure")
        with self.assertRaises(RuntimeError):
            self.generate(failed)


class CiArmExclusionTests(unittest.TestCase):
    """Fake upstream Arm inputs; no Sail is run."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.arm = Path(temporary.name)
        (self.arm / "src").mkdir()
        names = ("src/base.sail", *ci.ARM_EXCLUDED_INPUTS, "src/end.sail")
        (self.arm / "Makefile").write_text("SAIL_SRCS = " + " ".join(names) + "\n")
        (self.arm / "src/base.sail").write_text("val base : unit -> unit\n")
        (self.arm / "src/end.sail").write_text("function base() = ()\n")
        for name in ci.ARM_EXCLUDED_INPUTS:
            (self.arm / name).write_text(
                "/* Instruction file fixture. */\n"
                "val execute_one : unit -> unit\n"
                "function execute_one() = {\n  ()\n}\n"
                "function clause __DecodeA64_SVE(pc, opcode) = execute_one()\n")
        environment = patch.dict(os.environ, {"SAIL_DIR": "/fake/SAIL_DIR"})
        environment.start()
        self.addCleanup(environment.stop)

    def refused(self, name, text, message):
        (self.arm / name).write_text(text)
        with self.assertRaisesRegex(ValueError, message):
            ci.check_arm_exclusions(self.arm)

    def test_self_contained_instruction_files_are_accepted(self):
        ci.check_arm_exclusions(self.arm)

    def test_other_top_level_definitions_are_refused(self):
        self.refused(ci.ARM_EXCLUDED_INPUTS[0], "register SEE2 : int\n",
                     "top-level register")

    def test_clauses_of_other_scattered_functions_are_refused(self):
        self.refused(ci.ARM_EXCLUDED_INPUTS[1],
                     "function clause __DecodeA64_LoadStore(pc, opcode) = ()\n",
                     "clause of __DecodeA64_LoadStore")

    def test_a_body_declared_by_a_remaining_input_is_refused(self):
        self.refused(ci.ARM_EXCLUDED_INPUTS[2], "function base() = ()\n",
                     "declared elsewhere base")

    def test_an_exclusion_absent_upstream_is_refused(self):
        (self.arm / "Makefile").write_text("SAIL_SRCS = src/base.sail src/end.sail\n")
        with self.assertRaisesRegex(ValueError, "not an upstream input"):
            ci.check_arm_exclusions(self.arm)


class CiProofOrchestrationTests(unittest.TestCase):
    """All proof commands are mocked; only workspace and refusal logic run."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        use_fixture_statements(self)
        self.repo = self.root / "repo"
        self.here = self.repo / "tools/sail"
        self.generated = self.here / "generated"
        self.generated.mkdir(parents=True)
        self.tracked = {
            "arm/proofs/base.ml": "(* Fake tracked Arm source. *)\n",
            "tools/sail/check-proof.sh":
                "# Fake tracked launcher; never executed by these tests.\n",
            # A fake driver for every suite: check_proof_sources requires
            # check_axioms before the completion marker.
            **{f"tools/sail/proofs/{mode}.ml":
               "(* Fake tracked proof source. *)\ncheck_axioms ();;\n"
               f'print_endline "{ci.completion_marker(mode)}";;\n'
               for mode in ci.modes()},
            "x86/proofs/x86.ml": "".join(
                f"let x86_{name} = new_definition `x86_{name} = T`;;\n"
                for name in x86_forms.GPR + x86_forms.VECTOR),
        }
        for name, contents in self.tracked.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
        for name, constants in model_constants().items():
            contents = model_fixture(name, constants)
            (self.generated / name).write_text(contents)
            self.tracked[str((self.generated / name).relative_to(self.repo))] = contents
        for name in ("ci/check.py", "ci/setup.sh", "tests/test_ci.py"):
            path = self.here / name
            path.parent.mkdir(parents=True, exist_ok=True)
            contents = "# Fake tracked CI source fixture.\n"
            path.write_text(contents)
            self.tracked[str(path.relative_to(self.repo))] = contents
        bytecode = self.here / "ci/__pycache__/check.cpython-fixture.pyc"
        bytecode.parent.mkdir()
        bytecode.write_bytes(b"fake ignored bytecode")
        paths = patch.multiple(
            ci, HERE=self.here, REPO=self.repo, GENERATED=self.generated,
            WORK=self.here / "_build/ci")
        paths.start()
        self.addCleanup(paths.stop)
        selected = patch.object(ci, "modes", return_value=("arm-compare", "rv32"))
        selected.start()
        self.addCleanup(selected.stop)
        environment = patch.dict(os.environ, {
            "HOLDIR": "/fake/hol",
            "SAIL_DIR": "/fake/sail",
            "SAIL_EXE": "/fake/sail.exe",
            "SAIL_HOL_BUILD_DIR": "/fake/stale-output",
            "SAIL_X86_DIR": "/fake/x86-source",
        }, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        git = patch.object(
            ci.subprocess, "check_output",
            return_value=("\0".join(self.tracked) + "\0").encode())
        git.start()
        self.addCleanup(git.stop)
        self.calls = []

    def fake_proof(self, command, log, env=None, cwd=None, timeout=None):
        self.calls.append((command, log, env, cwd))
        mode = command[2]
        project = Path(command[1]).parent
        Path(log).write_text("Mocked controller command; no native HOL was run.\n")
        if mode != "arm-base":
            (project / "_build" / (mode + "-proof.log")).write_text(
                proof_fixture(mode))

    def check_proofs(self, jobs=2, action=None):
        with patch.object(ci, "run", side_effect=action or self.fake_proof), \
                redirect_stdout(io.StringIO()):
            ci.run_proofs(jobs)

    def test_snapshot_copies_current_sources_and_only_registered_models(self):
        workspace, project, original, copied = ci.snapshot_workspace()
        for name, contents in self.tracked.items():
            self.assertEqual((workspace / name).read_text(), contents)
        for name in ("ci/check.py", "ci/setup.sh", "tests/test_ci.py"):
            self.assertEqual((project / name).read_bytes(),
                             (self.here / name).read_bytes())
        self.assertFalse((project / "ci/__pycache__").exists())
        self.assertFalse((workspace / ".git").exists())
        self.assertEqual({path.name for path in (project / "_build").iterdir()},
                         set(ci.model_names()))
        ci.unchanged(original)
        ci.unchanged(copied)

    def test_snapshot_ignores_untracked_ci_and_generated_files(self):
        for name in ("ci/local.py", "generated/local.txt"):
            path = self.here / name
            path.write_text("Untracked local fixture; not a CI input.\n")
        workspace, project, original, copied = ci.snapshot_workspace()
        self.assertFalse((project / "ci/local.py").exists())
        self.assertFalse((project / "generated/local.txt").exists())
        ci.unchanged(original)
        ci.unchanged(copied)

    def test_proof_fork_count_is_checked_before_any_suite(self):
        for forks in ("0", "65", "four"):
            with self.subTest(forks=forks), patch.dict(
                    os.environ, {"SAIL_HOL_PROOF_FORKS": forks}), \
                    self.assertRaises(ValueError):
                self.check_proofs()
            self.assertEqual(self.calls, [])
        with patch.dict(os.environ, {"SAIL_HOL_PROOF_FORKS": "2"}):
            self.check_proofs()
        self.assertEqual({environment["SAIL_HOL_PROOF_FORKS"]
                          for _, _, environment, _ in self.calls}, {"2"})

    def test_proofs_use_only_the_proof_launcher_and_no_sail_env(self):
        self.check_proofs()
        # The Arm base is compiled once, before any suite.
        self.assertEqual(self.calls[0][0][2], "arm-base")
        self.assertEqual({call[0][2] for call in self.calls[1:]}, {"arm-compare", "rv32"})
        for command, log, environment, workspace in self.calls:
            self.assertEqual(command[0], "bash")
            self.assertEqual(Path(command[1]).name, "check-proof.sh")
            self.assertEqual(command[3:], [])
            self.assertEqual({name for name in environment if name.startswith("SAIL_")},
                             {"SAIL_HOL_PROOF_BACKTRACE", "SAIL_HOL_PROOF_FORKS"})
            self.assertEqual(environment["SAIL_HOL_PROOF_FORKS"], "4")
            self.assertEqual(environment["SAIL_HOL_PROOF_BACKTRACE"], "0")
            self.assertEqual(environment["HOLDIR"], "/fake/hol")
            self.assertEqual(Path(command[1]).relative_to(workspace),
                             Path("tools/sail/check-proof.sh"))

    def test_load_path_and_preload_are_not_passed_to_suites(self):
        with patch.dict(os.environ, {"HOLLIGHT_LOAD_PATH": "/elsewhere",
                                     "LD_PRELOAD": "/fake/preload.so"}):
            self.check_proofs()
        for _, _, environment, _ in self.calls:
            self.assertNotIn("HOLLIGHT_LOAD_PATH", environment)
            self.assertNotIn("LD_PRELOAD", environment)

    def test_selected_suites_are_the_only_ones_run_and_audited(self):
        with patch.object(ci, "run", side_effect=self.fake_proof), \
                redirect_stdout(io.StringIO()) as output:
            ci.run_proofs(2, selected=("rv32",))
        self.assertEqual([call[0][2] for call in self.calls], ["rv32"])
        count = len(ci.expected_theorems("rv32"))
        self.assertIn(f"rv32: {count}/{count} theorems equal statements/rv32.txt\n"
                      f"1 of 2 suites passed: {count}/{count} theorems equal "
                      "statements/.\n", output.getvalue())

    def test_unknown_selected_suite_is_refused_before_any_run(self):
        with patch.object(ci, "run", side_effect=self.fake_proof), \
                self.assertRaisesRegex(ValueError, "unknown proof suites: carry"):
            ci.run_proofs(2, selected=("carry",))
        self.assertEqual(self.calls, [])

    def test_suites_cancelled_after_a_failure_are_named(self):
        # Whether a queued suite starts before the cancellation is a race;
        # either way each suite is reported once, failed or not run.
        suites = ("arm-compare", "rv32", "x86-vector")
        def failing(command, log, env=None, cwd=None, timeout=None):
            if command[2] != "arm-base":
                raise RuntimeError("mocked failure")
        with patch.object(ci, "modes", return_value=suites), \
                self.assertRaises(RuntimeError) as raised:
            self.check_proofs(jobs=1, action=failing)
        lines = str(raised.exception).splitlines()
        self.assertTrue(lines.pop().startswith("Proof artifacts: "))
        failed = [line.split(":")[0] for line in lines if "mocked failure" in line]
        skipped = []
        if lines[-1].startswith("not run after the failure: "):
            skipped = lines.pop().split(": ")[1].split(", ")
        self.assertTrue(failed)
        self.assertEqual(len(lines), len(failed))
        self.assertEqual(sorted(failed + skipped), sorted(suites))

    def test_all_x86_modes_use_checked_in_snapshots_without_sail(self):
        # The x86 modes that ci.modes() selects; CiInventoryTests checks it.
        x86 = ("x86-vector", "x86-rems-arithmetic", "x86-rems-shift")
        with patch.object(ci, "modes", return_value=x86):
            self.check_proofs()
        self.assertEqual({call[0][2] for call in self.calls}, set(x86))
        for _, _, environment, _ in self.calls:
            self.assertNotIn("SAIL_X86_DIR", environment)
            self.assertNotIn("SAIL_EXE", environment)

    def test_proof_order_preserves_inventory_and_starts_larger_models_first(self):
        self.assertEqual(set(ci.proof_order(self.generated)), set(ci.modes()))
        self.assertEqual(len(ci.proof_order(self.generated)), len(ci.modes()))
        path = self.generated / "arm-compare.ml"
        path.write_text(path.read_text() + "\n(* " + "x" * 10000 + " *)\n")
        self.check_proofs(jobs=1)
        self.assertEqual([call[0][2] for call in self.calls],
                         ["arm-base", "arm-compare", "rv32"])

    def test_proof_order_counts_both_rv32_models(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            for name, size in (("arm-compare.ml", 10),
                               ("rv32.ml", 6), ("rv32-control.ml", 6)):
                (directory / name).write_text("x" * size)
            self.assertEqual(ci.proof_order(directory), ["rv32", "arm-compare"])

    def test_proof_order_has_lexical_ties_independent_of_inventory_order(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            for name in ("arm-compare.ml", "x86-vector.ml"):
                (directory / name).write_text("equal size")
            with patch.object(ci, "modes",
                              return_value=("x86-vector", "arm-compare")):
                self.assertEqual(ci.proof_order(directory),
                                 ["arm-compare", "x86-vector"])

    def test_stale_original_logs_cannot_replace_missing_fresh_results(self):
        build = self.here / "_build"
        build.mkdir(exist_ok=True)
        for mode in ci.modes():
            (build / (mode + "-proof.log")).write_text(proof_fixture(mode))
        with self.assertRaises(RuntimeError):
            self.check_proofs(action=lambda *args, **kwargs: None)

    def test_command_failure_is_not_replaced_by_a_complete_mocked_log(self):
        def failed(command, log, env=None, cwd=None, timeout=None):
            self.fake_proof(command, log, env, cwd)
            if command[2] != "arm-base":
                raise RuntimeError("mocked native command exited nonzero")
        with self.assertRaises(RuntimeError):
            self.check_proofs(action=failed)

    def test_missing_theorem_is_refused_after_a_mocked_exit_zero(self):
        def incomplete(command, log, env=None, cwd=None, timeout=None):
            self.fake_proof(command, log, env, cwd)
            project = Path(command[1]).parent
            proof = project / "_build" / (command[2] + "-proof.log")
            proof.write_text(completion(command[2]) + "\n")
        with self.assertRaises(RuntimeError):
            self.check_proofs(action=incomplete)

    def test_original_source_mutation_is_refused_after_mocked_proof_success(self):
        selected = patch.object(ci, "modes", return_value=("arm-compare",))
        def changed(command, log, env=None, cwd=None, timeout=None):
            self.fake_proof(command, log, env, cwd)
            (self.repo / "arm/proofs/base.ml").write_text("changed fake source\n")
        with selected, self.assertRaises((ValueError, RuntimeError)):
            self.check_proofs(jobs=1, action=changed)

    def test_staged_model_mutation_is_refused_after_mocked_proof_success(self):
        selected = patch.object(ci, "modes", return_value=("arm-compare",))
        def changed(command, log, env=None, cwd=None, timeout=None):
            self.fake_proof(command, log, env, cwd)
            path = Path(command[1]).parent / "_build/arm-compare.ml"
            path.write_bytes(path.read_bytes() + b"(* changed fake model *)\n")
        with selected, self.assertRaises((ValueError, RuntimeError)):
            self.check_proofs(jobs=1, action=changed)

    def test_all_started_workers_drain_when_another_worker_fails(self):
        started = threading.Event()
        failed = threading.Event()
        drained = threading.Event()
        def worker(command, log, env=None, cwd=None, timeout=None):
            if command[2] == "arm-base":
                return
            if command[2] == "arm-compare":
                if not started.wait(3):
                    raise RuntimeError("mock second worker did not start")
                failed.set()
                raise RuntimeError("mock first worker failed")
            started.set()
            if not failed.wait(3):
                raise RuntimeError("mock first worker did not fail")
            self.fake_proof(command, log, env, cwd)
            drained.set()
        with self.assertRaises(RuntimeError):
            self.check_proofs(action=worker)
        self.assertTrue(drained.is_set())

    def test_invalid_parallelism_is_refused_before_starting_any_command(self):
        for jobs in (0, -1, 65):
            with self.subTest(jobs=jobs), self.assertRaises(ValueError):
                self.check_proofs(jobs=jobs)
        self.assertEqual(self.calls, [])


if __name__ == "__main__":
    unittest.main()
