#!/usr/bin/env python3
"""Check the AArch64 and RV32IM inventory and the proof-log audit."""
import unittest

import _project
import coverage
from coverage import RV32, inventory, without_comments


def variants(family, instruction):
    return coverage.arm_instruction_variants(family, instruction)


def family_of(instruction):
    return next(family for family, specification in coverage.ARM_FAMILIES.items()
                if instruction in specification["instructions"])


class CommentTests(unittest.TestCase):
    def test_nested_ocaml_comments_do_not_create_instructions(self):
        source = "(* let arm_FAKE = define (* nested *) *)\nlet arm_ADD = define"
        stripped = without_comments(source)
        self.assertNotIn("arm_FAKE", stripped)
        self.assertIn("arm_ADD", stripped)
        self.assertEqual(source.count("\n"), stripped.count("\n"))

    def test_quoted_sail_excerpt_cannot_close_an_ocaml_comment(self):
        source = ('(* "model.sail:9"\n'
                  '{sail_source|function f() = "*) \\" (*"\n|sail_source}\n'
                  '*)\nlet actual = new_definition `actual = T`;;')
        stripped = without_comments(source)
        self.assertNotIn("function f", stripped)
        self.assertIn("let actual = new_definition", stripped)
        self.assertEqual(len(source), len(stripped))
        self.assertEqual(source.count("\n"), stripped.count("\n"))

    def test_quoted_ocaml_strings_outside_comments_are_preserved(self):
        source = 'let data = {source|(* not a comment *)|source};;'
        self.assertEqual(without_comments(source), source)
        with self.assertRaisesRegex(ValueError, "unterminated OCaml quoted"):
            without_comments("(* {source|unfinished *)")


class InventoryTests(unittest.TestCase):
    def test_decoder_helpers_are_not_counted(self):
        names = {x["hol"] for x in inventory()["rv32im"]["instructions"]}
        self.assertNotIn("riscv_gpr", names)
        self.assertNotIn("riscv_mulh", names)
        self.assertIn("riscv_MULH", names)
        self.assertIn("riscv_JALR", names)

    def test_tables_list_every_public_definition_once(self):
        public = {row["hol"] for row in inventory()["aarch64"]["instructions"]}
        registered = [
            "arm_" + name for specification in coverage.ARM_FAMILIES.values()
            for name in specification["instructions"]]
        self.assertEqual(len(registered), len(set(registered)))
        self.assertEqual(set(registered), public)
        self.assertEqual(len(registered), 221)
        rv32 = {row["hol"] for row in inventory()["rv32im"]["instructions"]}
        self.assertEqual({row["definition"] for row in RV32.values()}, rv32)
        self.assertEqual((len(rv32), len(RV32)), (48, 50))

    def test_form_counts(self):
        total = sum(len(variants(family, name))
                    for family, specification in coverage.ARM_FAMILIES.items()
                    for name in specification["instructions"])
        self.assertEqual(total, 1404)
        for family, count in (
                ("vector-doubling", 24), ("vector-saturating-narrow", 12),
                ("memory-single", 100), ("memory-pair", 48),
                ("memory-four", 48), ("memory-structure2", 14),
                ("memory-structure3", 28), ("memory-replicate", 8)):
            specification = coverage.ARM_FAMILIES[family]
            with self.subTest(family=family):
                self.assertEqual(sum(len(variants(family, name))
                                     for name in specification["instructions"]),
                                 count)
                if family.startswith("memory-"):
                    self.assertTrue(specification["safe_domain_proofs"])
                    self.assertTrue(specification["encoded_signatures_only"])

    def test_branch_and_hint_names(self):
        for instruction, theorems, constants in (
                ("Bcond", ["SAIL_HL_ARM_BCOND_EQ"], ["sail_hl_arm_5fBCOND"]),
                ("TBZ", ["SAIL_HL_ARM_TBZ32_EQ", "SAIL_HL_ARM_TBZ64_HI_EQ"], None),
                ("B", ["SAIL_HL_ARM_B_EQ"], ["sail_hl_arm_5fB"]),
                ("BL", ["SAIL_HL_ARM_BL_EQ"], ["sail_hl_arm_5fBL"]),
                ("RET", ["SAIL_HL_ARM_RET_EQ"], ["sail_hl_arm_5fRET"]),
                ("NOP", ["SAIL_HL_ARM_NOP_EQ"], None),
                ("BTI", ["SAIL_HL_ARM_BTI_C_EQ"], ["sail_hl_arm_5fBTI_5fC"])):
            rows = variants(family_of(instruction), instruction)
            with self.subTest(instruction=instruction):
                self.assertEqual([row["theorem"] for row in rows], theorems)
                if constants is not None:
                    self.assertEqual([row["constant"] for row in rows], constants)

    def test_widths_and_forms(self):
        for instruction in ("ADR", "UMADDL"):
            with self.subTest(instruction=instruction):
                self.assertEqual({row["width"] for row in
                                  variants(family_of(instruction), instruction)},
                                 {64})
        self.assertEqual(
            coverage.arm_instruction_forms("compare", "CCMP"),
            ("register", "immediate"))


class ProofOutputTests(unittest.TestCase):
    def test_proof_output_requires_unique_closed_claims_and_completion(self):
        name = "SAIL_HL_ARM_ADC64_EQ"
        completion = "SAIL_HOL_LIGHT_ARM_CARRY_OK"
        valid = [name, "|- T", completion]
        coverage.audit_proof_output(valid, [name], completion, "fixture")
        malformed = (
            [name, completion],
            [name, "p |- T", completion],
            [name, "  |- T", completion],
            [name, "|- T"],
            valid + [completion],
            valid + [name, "|- T"],
            valid + ["SAIL_HL_ARM_SBC64_EQ", "|- T"],
        )
        for lines in malformed:
            with self.subTest(lines=lines), self.assertRaises(ValueError):
                coverage.audit_proof_output(lines, [name], completion, "fixture")

    def test_one_line_reports_are_split(self):
        name = "SAIL_HL_X86_ADD64_RR_EQ"
        completion = "SAIL_HOL_LIGHT_X86_VECTOR_PROOFS_OK"
        lines = [name + ": |- T", completion]
        coverage.audit_proof_output(lines, [name], completion, "fixture")
        self.assertEqual(coverage.theorem_statements(lines, {name}), {name: "|- T"})


if __name__ == "__main__":
    unittest.main()
