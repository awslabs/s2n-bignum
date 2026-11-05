#!/usr/bin/env python3
"""Check the exporter's dependency selection on a small syntax tree.

Builds tests/typed_ast_selection.ml against the compiled exporter modules
and runs it inside Sail. Run inside the matching OCaml switch, with
SAIL_EXE and SAIL_HOL_BUILD_DIR set; the latter holds the plugin's
compiled OCaml interfaces, native modules and object files.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import _project

ROOT = _project.ROOT
MODULES = ("entry", "arm", "rv32", "x86", "x86_shina", "x86_rems",
           "hol_term", "sail_plugin_hol_light")


def checked_run(command):
    completed = subprocess.run(command, capture_output=True, text=True)
    if completed.returncode:
        raise AssertionError("Command failed: " + " ".join(map(str, command)) +
                             "\n" + completed.stdout + completed.stderr)
    return completed.stdout


class SelectionTests(unittest.TestCase):
    def test_selection_keeps_dependencies_and_drops_cut_bodies(self):
        missing = [name for name in ("SAIL_EXE", "SAIL_HOL_BUILD_DIR")
                   if not os.environ.get(name)]
        if missing:
            raise AssertionError("Set " + ", ".join(missing))
        if not shutil.which("ocamlfind"):
            raise AssertionError("Run inside the matching OCaml switch")
        sail = Path(os.environ["SAIL_EXE"]).resolve()
        build = Path(os.environ["SAIL_HOL_BUILD_DIR"]).resolve()
        modules = [build / (name + ".cmx") for name in MODULES]
        if not sail.is_file() or not all(path.is_file() for path in modules):
            raise AssertionError("The native Sail/exporter build is missing")
        with tempfile.TemporaryDirectory(prefix="sail-selection-") as temporary:
            object_file = Path(temporary) / "typed_ast_selection.cmx"
            plugin = Path(temporary) / "typed_ast_selection.cmxs"
            checked_run(["ocamlfind", "ocamlopt", "-g", "-package", "libsail",
                         "-I", str(build), "-c",
                         str(ROOT / "tests/typed_ast_selection.ml"),
                         "-o", str(object_file)])
            # Sail uses Dynlink.loadfile_private. Link the unchanged exporter
            # modules into this one test image, rather than loading a second
            # image which cannot reference their private symbols.
            checked_run(["ocamlopt", "-shared", "-linkall", *map(str, modules),
                         str(object_file), "-o", str(plugin)])
            output = checked_run([str(sail), "--plugin", str(plugin),
                                  "--hol-light-selection-sanity"])
        self.assertIn("TYPED_AST_SELECTION_SANITY_PASS", output)


if __name__ == "__main__":
    unittest.main()
