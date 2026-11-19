#!/usr/bin/env python3
"""Check the translator's binding simplification on random terms.

backend/hol_term.ml's simplify_bindings rewrites every definition before
it is printed. tests/simplify_check.ml compares, for random terms, a
symbolic evaluation before and after the rewrite. This test compiles it
against the plugin build and requires no mismatch.
"""
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
TRIALS = "200000"


class SimplifyTests(unittest.TestCase):
    def test_simplified_terms_evaluate_to_the_same_value(self):
        build = Path(os.environ.get("SAIL_HOL_BUILD_DIR", HERE.parent / "_build"))
        if not (build / "hol_term.cmx").exists():
            self.skipTest("build the plugin first: bash tools/sail/build.sh")
        with tempfile.TemporaryDirectory() as directory:
            # Compile a copy, so that the object files stay in directory.
            source = Path(directory) / "simplify_check.ml"
            source.write_bytes((HERE / "simplify_check.ml").read_bytes())
            executable = Path(directory) / "simplify_check"
            compiled = subprocess.run(
                ["ocamlfind", "ocamlopt", "-package", "libsail", "-linkpkg",
                 "-I", str(build), str(build / "hol_term.cmx"),
                 str(source), "-o", str(executable)],
                cwd=directory, capture_output=True, text=True)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            result = subprocess.run([str(executable), TRIALS], text=True,
                                    capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        # Both kinds of term were generated and checked.
        self.assertRegex(result.stdout, r"constant heads: [1-9]\d* checked")
        self.assertRegex(result.stdout, r"variable heads: [1-9]\d* checked, [1-9]\d* refused, 0 mismatches")


if __name__ == "__main__":
    unittest.main()
