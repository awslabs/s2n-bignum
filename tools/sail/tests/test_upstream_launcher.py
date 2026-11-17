#!/usr/bin/env python3
"""Check that the launcher reads the external architecture project inputs."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("sail_hol_ci_check_launcher",
                                              ROOT / "ci" / "check.py")
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)


class UpstreamLauncherTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        required = ("SAIL_DIR", "SAIL_ARM_DIR", "SAIL_RISCV_DIR")
        missing = [name for name in required if not os.environ.get(name)]
        if missing:
            raise AssertionError("Set " + ", ".join(missing) +
                                 " to the external upstream checkouts")
        cls.environment = dict(os.environ)
        cls.arm = Path(os.environ["SAIL_ARM_DIR"]).resolve() / "arm-v9.4-a"
        cls.riscv = Path(os.environ["SAIL_RISCV_DIR"]).resolve()
        if not (cls.arm / "Makefile").is_file():
            raise AssertionError("The external Arm checkout is unavailable")
        if not (cls.riscv / "model/riscv.sail_project").is_file():
            raise AssertionError("The external RISC-V checkout is unavailable")

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="sail-launcher-")
        self.addCleanup(self.directory.cleanup)
        fake = Path(self.directory.name) / "sail"
        fake.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, sys\n"
            "print(json.dumps({'cwd': os.getcwd(), 'args': sys.argv[1:]}))\n")
        fake.chmod(0o700)
        self.environment = dict(type(self).environment,
                                SAIL_EXE=str(fake), SAIL_HOL_PLUGIN=str(fake))

    def run_launcher(self, architecture, family):
        completed = subprocess.run(
            ["bash", str(ROOT / "run.sh"), architecture, family],
            env=self.environment, check=True, capture_output=True, text=True)
        return json.loads(completed.stdout)

    def test_arm_input_order_and_external_paths(self):
        result = self.run_launcher("arm", "carry")
        args = result["args"]
        self.assertEqual(Path(result["cwd"]), self.arm)
        self.assertEqual(args[args.index("--hol-light-architecture") + 1],
                         "aarch64")
        self.assertEqual(args[args.index("--hol-light-family") + 1], "carry")
        # check.py reads the same list from upstream's Makefile to check the
        # excluded inputs.
        inputs = [arg for arg in args if arg.endswith(".sail")]
        self.assertEqual(inputs, ci.arm_inputs(self.arm))
        self.assertTrue(inputs)
        for source in inputs:
            path = (Path(result["cwd"]) / source).resolve()
            self.assertTrue(path.is_relative_to(self.arm), source)
            self.assertTrue(path.is_file(), source)
            self.assertFalse(path.is_relative_to(ROOT), source)
        self.assertFalse(any(arg.endswith(".holslice") for arg in args))

    def test_arm_excluded_inputs_leave_the_rest_in_upstream_order(self):
        upstream = [arg for arg in self.run_launcher("arm", "carry")["args"]
                    if arg.endswith(".sail")]
        excluded = upstream[1:3]
        self.environment["SAIL_ARM_EXCLUDED_INPUTS"] = " ".join(excluded)
        inputs = [arg for arg in self.run_launcher("arm", "carry")["args"]
                  if arg.endswith(".sail")]
        self.assertEqual(inputs, [name for name in upstream if name not in excluded])
        self.environment["SAIL_ARM_EXCLUDED_INPUTS"] = "src/absent.sail"
        result = subprocess.run(
            ["bash", str(ROOT / "run.sh"), "arm", "carry"],
            env=self.environment, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Excluded Arm input is not an upstream input: src/absent.sail",
                      result.stderr)

    def test_all_omits_family_selection(self):
        result = self.run_launcher("arm", "all")
        args = result["args"]
        self.assertNotIn("--hol-light-family", args)
        self.assertTrue(args[args.index("-o") + 1].endswith("/arm-all"))

    def test_rv32_uses_project_and_native_configuration(self):
        result = self.run_launcher("rv32", "arithmetic")
        args = result["args"]
        self.assertEqual(Path(result["cwd"]), self.riscv / "model")
        self.assertEqual(args[-4:],
                         ["riscv.sail_project", "I_insts", "M_insts", "Zihintpause"])
        self.assertFalse(any(arg.endswith(".holslice") for arg in args))
        self.assertFalse(any(arg.endswith(".sail") for arg in args))
        required_version = (
            self.riscv / "cmake/sail_required_version.txt").read_text().strip()
        self.assertEqual(args[args.index("--require-version") + 1],
                         required_version)
        for flag in ("--strict-var", "--strict-bitvector",
                     "--strict-exponentials"):
            self.assertIn(flag, args)
        config = Path(args[args.index("--config") + 1])
        self.assertEqual(config, ROOT / "backend/rv32.json")
        self.assertEqual(json.loads(config.read_text()),
                         {"base": {"xlen": 32, "E": False}})

    def test_x86_shina_uses_only_the_external_project(self):
        checkout = Path(self.directory.name) / "external-x86"
        model = checkout / "model"
        model.mkdir(parents=True)
        (model / "x86.sail_project").write_text("")
        self.environment["SAIL_X86_SHINA_DIR"] = str(checkout)
        result = self.run_launcher("x86-shina", "arithmetic")
        args = result["args"]
        self.assertEqual(Path(result["cwd"]), model)
        self.assertEqual(args[args.index("--hol-light-architecture") + 1],
                         "x86")
        self.assertEqual(args[args.index("--hol-light-x86-source") + 1],
                         "shina")
        self.assertEqual(args[args.index("--hol-light-family") + 1],
                         "arithmetic")
        self.assertEqual(args[args.index("--require-version") + 1], "0.20")
        self.assertIn("--all-modules", args)
        self.assertEqual(args[-1], "x86.sail_project")
        self.assertFalse(any(arg.endswith((".sail", ".holslice"))
                             for arg in args))

    def test_x86_shina_requires_the_external_project(self):
        checkout = Path(self.directory.name) / "missing-x86"
        (checkout / "model").mkdir(parents=True)
        self.environment["SAIL_X86_SHINA_DIR"] = str(checkout)
        result = subprocess.run(
            ["bash", str(ROOT / "run.sh"), "x86-shina", "arithmetic"],
            env=self.environment, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Missing upstream x86 project", result.stderr)

    def test_x86_rems_takes_upstream_make_input_order(self):
        checkout = Path(self.directory.name) / "external-rems"
        model = checkout / "model"
        model.mkdir(parents=True)
        (model / "Makefile").write_text("ALL_SAILS = second.sail first.sail\n")
        for name in ("first.sail", "second.sail"):
            (model / name).write_text("")
        self.environment["SAIL_X86_REMS_DIR"] = str(checkout)
        result = self.run_launcher("x86-rems", "shift")
        args = result["args"]
        self.assertEqual(Path(result["cwd"]), model)
        self.assertEqual(args[args.index("--hol-light-x86-source") + 1],
                         "rems")
        self.assertEqual(args[args.index("--hol-light-family") + 1], "shift")
        self.assertEqual(args[-2:], ["second.sail", "first.sail"])
        self.assertFalse(any(arg.endswith(".sail_project") for arg in args))

    def test_x86_rems_refuses_missing_inputs_and_the_old_launcher_name(self):
        checkout = Path(self.directory.name) / "broken-rems"
        model = checkout / "model"
        model.mkdir(parents=True)
        (model / "Makefile").write_text("ALL_SAILS = absent.sail\n")
        self.environment["SAIL_X86_REMS_DIR"] = str(checkout)
        for architecture, message in (
                ("x86-rems", "Missing upstream REMS x86 input: absent.sail"),
                ("x86", "Unknown architecture: x86")):
            result = subprocess.run(
                ["bash", str(ROOT / "run.sh"), architecture, "arithmetic"],
                env=self.environment, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(message, result.stderr)


if __name__ == "__main__":
    unittest.main()
