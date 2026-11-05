#!/usr/bin/env python3
"""Check source references independently of generated proof artifacts."""
import importlib.util
from pathlib import Path
import re
import shutil
import sys
import tempfile
import unittest

import _project
import coverage

ROOT = _project.ROOT
spec = importlib.util.spec_from_file_location(
    "sail_hol_ci_check_layout", ROOT / "ci" / "check.py")
ci = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = ci
spec.loader.exec_module(ci)

class LayoutTests(unittest.TestCase):
    def test_tooling_uses_the_project_root(self):
        self.assertEqual(coverage.HERE, ROOT)
        self.assertEqual(coverage.BUILD, ROOT / "_build")
        self.assertEqual(coverage.REPO, ROOT.parent.parent)

    def test_root_contains_entry_points_not_family_inputs(self):
        for pattern in ("*.sail", "test_*.py"):
            self.assertEqual(list(ROOT.glob(pattern)), [], pattern)
        self.assertTrue((ROOT / "backend/sail_plugin_hol_light.ml").is_file())

    def test_retained_proof_loads_have_sources(self):
        for source in (ROOT / "proofs").glob("*.ml"):
            for target in re.findall(r'\bload[st]\s+"([^"]+)"', source.read_text()):
                if target.startswith("Library/"):
                    # These are HOL Light library inputs, not repository files.
                    continue
                path = coverage.REPO / target
                if coverage.BUILD not in path.parents:
                    with self.subTest(source=source.name, target=target):
                        self.assertTrue(path.is_file(), str(path))

    def test_no_sail_sources_are_checked_in(self):
        # The launcher reads the pinned external checkouts; test programs
        # are virtual files.
        tools = coverage.REPO / "tools"
        self.assertEqual(sorted(path.relative_to(coverage.REPO)
                                for path in tools.rglob("*.sail")), [])


class AxiomTests(unittest.TestCase):
    """ci/check.py checks the proof sources before every proof run; these
    tests apply that check to the repository and to mutated copies."""

    def test_repository_proof_sources_pass(self):
        ci.check_proof_sources(coverage.REPO)

    def mutated(self, name, change):
        """Check a copy of the proof sources with one file changed."""
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            shutil.copytree(ROOT / "proofs", repo / "tools/sail/proofs")
            path = repo / "tools/sail/proofs" / name
            path.parent.mkdir(exist_ok=True)
            path.write_text(change(path.read_text() if path.exists() else ""))
            ci.check_proof_sources(repo)

    def test_forbidden_calls_and_missing_or_late_axiom_checks_fail(self):
        marker = 'print_endline "SAIL_HOL_LIGHT_ARM_CARRY_PROOFS_OK";;'
        for label, change in (
                ("mk_thm", lambda text: text + "let x = mk_thm([],`T`);;\n"),
                ("interface", lambda text: text + 'override_interface("x",`T`);;\n'),
                ("Obj", lambda text: text + "let y = Obj.magic 0;;\n"),
                ("Obj alias", lambda text: "module O = Obj;;\n" + text),
                ("infix", lambda text: 'parse_as_infix("<=>",(2,"left"));;\n' + text),
                ("unparse infix", lambda text: 'unparse_as_infix "<=>";;\n' + text),
                ("prefix", lambda text: 'parse_as_prefix "~";;\n' + text),
                ("unparse prefix", lambda text: 'unparse_as_prefix "~";;\n' + text),
                ("binder", lambda text: 'parse_as_binder "!";;\n' + text),
                ("unparse binder", lambda text: 'unparse_as_binder "!";;\n' + text),
                ("contents", lambda text: "the_interface.contents <- [];;\n" + text),
                ("ellipsis", lambda text: 'Format.set_ellipsis_text "";;\n' + text),
                ("max boxes", lambda text: "Format.set_max_boxes 1000;;\n" + text),
                ("redefined", lambda text: "let check_axioms () = ();;\n" + text),
                ("printing", lambda text: text + "print_thm TRUTH;;\n"),
                ("not a phrase", lambda text: text.replace(
                    "check_axioms ();;", "let _never () = check_axioms ();;")),
                ("unspaced load", lambda text: text.replace(
                    marker, 'loadt"arm/proofs/base.ml";;\n' + marker)),
                ("missing", lambda text: text.replace("check_axioms ();;", "")),
                ("after marker", lambda text: text.replace("check_axioms ();;\n", "")
                                                  + "check_axioms ();;\n"),
                ("before a load", lambda text: text.replace(
                    marker, 'loadt "arm/proofs/base.ml";;\n' + marker)),
                ("commented", lambda text: text.replace(
                    "check_axioms ();;", "(* check_axioms () *)"))):
            with self.subTest(change=label), self.assertRaises(ValueError):
                self.mutated("arm-carry.ml", change)
        with self.assertRaises(ValueError):
            self.mutated("sub/unloaded.ml", lambda text: "let x = mk_thm([],`T`);;\n")


if __name__ == "__main__":
    unittest.main()
