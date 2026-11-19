#!/usr/bin/env python3
"""Catalogue checks, not instruction proofs or compiler-correctness claims."""
from collections import Counter
import unittest

import _project
from x86_forms import (
    AES, AES_FORMS, AVX2, AVX2_FORMS, BIT, EXTRA, GPR, SSE, SSE_FORMS,
    VECTOR, absence, comparison_status,
    export_status, known_gap, required_forms, source_body,
    validate_public_scope)


class X86FormTests(unittest.TestCase):
    def test_requested_public_scope_is_exactly_28_scalar_and_40_vector(self):
        self.assertEqual(validate_public_scope(_project.ROOT.parent.parent), (28, 40))
        self.assertEqual(len(set(GPR)), 28)
        self.assertEqual(len(set(VECTOR)), 40)

    def test_complete_catalogue_has_436_distinct_claims(self):
        rows = required_forms()
        self.assertEqual(len(rows), 436)
        # The three two-operand IMUL roots carry a second theorem, against
        # x86_IMUL, so 433 roots have 436 theorems.
        self.assertEqual(len({row["root"] for row in rows}), 433)
        self.assertEqual(len({row["theorem"] for row in rows}), 436)
        self.assertEqual(Counter(row["family"] for row in rows),
                         {"arithmetic": 87, "shift": 41, "vector": 80,
                          "avx2": 55, "move": 18, "select": 92, "bit": 8,
                          "count": 15, "sse": 32, "aes": 5, "pext": 2,
                          "stack": 1})

    def test_further_scalar_instructions_are_all_present(self):
        names = {row["hol"] for row in required_forms()}
        for instruction in EXTRA:
            self.assertIn("x86_" + instruction, names)
        self.assertEqual(len(EXTRA), 26)

    def test_wide_roots_keep_existing_names_and_operand_order(self):
        roots = {row["root"]: row for row in required_forms()}
        for root in ("X86_ADD64_RR", "X86_IMUL164_R", "X86_IMUL64_RR",
                     "X86_MULX64_RRR", "X86_RCL64_RI", "X86_SHLD64_RRI"):
            self.assertIn(root, roots)
        self.assertEqual(roots["X86_MULX64_RRR"]["hol"], "x86_MULX4")
        self.assertEqual(roots["X86_IMUL164_R"]["hol"], "x86_IMUL2")
        self.assertEqual(roots["X86_SHLD64_RRI"]["argument_types"],
                         ["4 word", "4 word", "8 word"])

    def test_byte_register_domains_distinguish_legacy_and_rex(self):
        roots = {row["root"]: row for row in required_forms()}
        self.assertEqual(roots["X86_ADD8_RR"]["argument_types"],
                         ["4 word", "4 word"])
        self.assertEqual(roots["X86_ADD8_LEGACY_RR"]["argument_types"],
                         ["3 word", "3 word"])
        self.assertEqual(roots["X86_RCL8_LEGACY_RI"]["argument_types"],
                         ["3 word", "8 word"])

    def test_nonexistent_byte_and_word_forms_are_not_invented(self):
        for instruction in ("ADCX", "ADOX", "MULX4", "IMUL3", "SHLD", "SHRD"):
            rows = [row for row in required_forms()
                    if row["hol"] == "x86_" + instruction]
            self.assertNotIn(8, {row["width"] for row in rows})
            if instruction in ("ADCX", "ADOX", "MULX4"):
                self.assertNotIn(16, {row["width"] for row in rows})

    def test_every_vector_instruction_requires_both_widths(self):
        for instruction in VECTOR:
            rows = [row for row in required_forms()
                    if row["hol"] == "x86_" + instruction]
            self.assertEqual({row["width"] for row in rows}, {128, 256})
            self.assertEqual(len(rows), 2)

    def test_scalar_vex_encodings_are_marked(self):
        roots = {row["root"]: row for row in required_forms()}
        for root in ("X86_MULX64_RRR", "X86_MULX32_RRR",
                     "X86_PEXT64_RRR", "X86_PEXT32_RRR", "X86_VZEROUPPER"):
            self.assertEqual(roots[root]["encoding"], "VEX", root)

    def test_operandless_and_legacy_byte_encodings_are_marked(self):
        roots = {row["root"]: row for row in required_forms()}
        for name in ("CLC", "STC", "CMC", "CLD", "STD", "NOP", "ENDBR64"):
            self.assertEqual(roots["X86_" + name]["encoding"], "legacy", name)
        for row in roots.values():
            if "_LEGACY_" in row["root"]:
                self.assertEqual(row["encoding"], "legacy-byte", row["root"])

    def test_avx2_forms_are_register_forms_with_named_variants(self):
        rows = [row for row in required_forms() if row["family"] == "avx2"]
        self.assertEqual(len(rows), 55)
        self.assertEqual(len(rows), sum(len(widths) for _, widths, _, _
                                        in AVX2_FORMS))
        roots = {row["root"]: row for row in rows}
        self.assertEqual(roots["X86_VMOVD128_STORE_RR"]["hol"], "x86_VMOVD")
        self.assertEqual(roots["X86_VPBLENDW256_RRRI"]["argument_types"],
                         ["4 word"] * 3 + ["8 word"])
        self.assertEqual(roots["X86_VPEXTRW128_RRI"]["argument_types"],
                         ["4 word", "4 word", "8 word"])
        self.assertEqual({row["hol"] for row in rows},
                         {"x86_" + name for name in AVX2})

    def test_sse_forms_are_register_forms_with_named_variants(self):
        rows = [row for row in required_forms() if row["family"] == "sse"]
        # The 31 forms of SSE_FORMS and the operandless VZEROUPPER.
        self.assertEqual(len(rows), 32)
        self.assertEqual(len(rows), 1 + sum(len(widths) for _, widths, _, _
                                            in SSE_FORMS))
        roots = {row["root"]: row for row in rows}
        self.assertEqual(roots["X86_MOVQ128_F3_RR"]["hol"], "x86_MOVQ")
        self.assertEqual(roots["X86_PSRLW128_RI"]["argument_types"],
                         ["4 word", "8 word"])
        self.assertEqual(roots["X86_PINSRD128_RRI"]["argument_types"],
                         ["4 word", "4 word", "8 word"])
        self.assertEqual(roots["X86_VZEROUPPER"]["argument_types"], [])
        # Legacy encodings keep the upper bits; the VEX ones are marked.
        self.assertEqual({row["hol"] for row in rows if row["encoding"] == "VEX"},
                         {"x86_VPEXTRD", "x86_VPEXTRQ", "x86_VZEROUPPER"})
        self.assertEqual({row["hol"] for row in rows},
                         {"x86_" + name for name in SSE})

    def test_aes_forms_are_register_forms(self):
        rows = [row for row in required_forms() if row["family"] == "aes"]
        self.assertEqual(len(rows), 5)
        self.assertEqual(len(rows), sum(len(widths) for _, widths, _, _
                                        in AES_FORMS))
        roots = {row["root"]: row for row in rows}
        self.assertEqual(roots["X86_AESENC128_RR"]["argument_types"],
                         ["4 word", "4 word"])
        self.assertEqual(roots["X86_AESKEYGENASSIST128_RRI"]["argument_types"],
                         ["4 word", "4 word", "8 word"])
        self.assertEqual({row["encoding"] for row in rows}, {"SSE"})
        self.assertEqual({row["hol"] for row in rows},
                         {"x86_" + name for name in AES})

    def test_known_gaps_remain_required_and_uncredited(self):
        rows = required_forms()
        gaps = [row for row in rows if known_gap(row)]
        self.assertEqual(len(gaps), 20)
        self.assertEqual(Counter(row["hol"] for row in gaps), {
            "x86_RCL": 3, "x86_RCR": 3,
            "x86_BT": 2, "x86_BTC": 2, "x86_BTR": 2, "x86_BTS": 2,
            "x86_BSF": 3, "x86_BSR": 3,
        })
        self.assertFalse(any(known_gap(row) for row in rows
                             if row["width"] in (32, 64, 128, 256) and
                             row["hol"].removeprefix("x86_") not in BIT + ("BSF", "BSR")))
        self.assertEqual(len(required_forms()), 436)

    def test_corrected_shifts_require_agreement_at_every_legal_width(self):
        rows = [row for row in required_forms()
                if row["hol"] in ("x86_SHL", "x86_SHR",
                                  "x86_SHLD", "x86_SHRD")]
        self.assertEqual(len(rows), 16)
        self.assertTrue(all(known_gap(row) is None for row in rows))

    def test_rems_availability_is_independent_of_the_required_inventory(self):
        rows = required_forms()
        present = [row for row in rows
                   if export_status(row, "rems") == "available"]
        self.assertEqual(len(present), 119)
        self.assertEqual(Counter(row["family"] for row in present),
                         {"arithmetic": 78, "shift": 41})
        absent_rows = [row for row in rows
                       if export_status(row, "rems") == "absent"]
        absent = {row["hol"] for row in absent_rows}
        self.assertEqual(absent, {"x86_ADCX", "x86_ADOX", "x86_MULX4"} |
                         {"x86_" + name for name in VECTOR})
        self.assertEqual(len(absent_rows), 86)
        outside = [row for row in rows
                   if export_status(row, "rems") == "out-of-scope"]
        self.assertEqual(len(outside), 231)
        self.assertTrue(all(absence(row, "rems") for row in absent_rows))
        self.assertTrue(all(absence(row, "rems") is None for row in outside))
        self.assertTrue(all(source_body(row, "shina") for row in rows))

    def test_every_form_has_a_result_for_each_comparison(self):
        rows = required_forms()
        self.assertEqual(Counter(comparison_status(row, "shina/s2n") for row in rows),
                         {"agreement": 416, "divergence-proved": 20})
        statuses = [comparison_status(row, "rems/s2n") for row in rows]
        self.assertEqual(Counter(statuses),
                         {"out-of-scope": 231, "absent": 86,
                          "agreement": 100, "divergence-proved": 19})
        # The exported REMS bodies are all arithmetic or shift forms.
        self.assertEqual({row["family"] for row, status in zip(rows, statuses)
                          if status in ("agreement", "divergence-proved")},
                         {"arithmetic", "shift"})
        self.assertEqual({row["family"] for row, status in zip(rows, statuses)
                          if status == "absent"}, {"arithmetic", "vector"})
        with self.assertRaises(ValueError):
            comparison_status(rows[0], "rems/rems")

    def test_every_rems_body_is_exported(self):
        rows = required_forms()
        self.assertEqual(Counter(export_status(row, "rems") for row in rows),
                         {"out-of-scope": 231, "available": 119,
                          "absent": 86})
        self.assertTrue(all((export_status(row, "rems") == "available") ==
                            bool(source_body(row, "rems")) for row in rows))

    def test_divergences_name_the_affected_forms(self):
        rows = {row["root"]: row for row in required_forms()}
        for root, comparison, status in (
                ("X86_ROR64_RI", "rems/s2n", "divergence-proved"),
                ("X86_ROR8_RI", "rems/s2n", "divergence-proved"),
                ("X86_ROL8_LEGACY_RI", "rems/s2n", "divergence-proved"),
                ("X86_SAR16_RI", "rems/s2n", "divergence-proved"),
                ("X86_SAR32_RI", "rems/s2n", "agreement"),
                ("X86_RCL8_RI", "rems/s2n", "divergence-proved"),
                ("X86_RCR16_RI", "shina/s2n", "divergence-proved"),
                ("X86_RCL32_RI", "rems/s2n", "agreement"),
                ("X86_ADD64_RR", "rems/s2n", "agreement"),
                ("X86_SHL64_RI", "rems/s2n", "agreement"),
                ("X86_ADCX64_RR", "rems/s2n", "absent"),
                ("X86_MOV64_RR", "rems/s2n", "out-of-scope")):
            with self.subTest(root=root, comparison=comparison):
                self.assertEqual(comparison_status(rows[root], comparison), status)


if __name__ == "__main__":
    unittest.main()
