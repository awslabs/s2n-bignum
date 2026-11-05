#!/usr/bin/env python3
"""Check the two stages of the Sail/HOL connection independently.

Generation runs Sail and compares its output with checked-in HOL models.
Proof checking uses those models in fresh HOL Light processes without Sail.
The separate refresh command updates snapshots after explicit
regeneration.

This file defines, in order: the required suites, theorems and models and
the checks of a model set; running commands; generation; proof checking;
the command line.
"""
import argparse
from concurrent.futures import CancelledError, ThreadPoolExecutor, as_completed
import hashlib
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent.parent
REPO = HERE.parent.parent
GENERATED = HERE / "generated"
# The checked-in statement of every required theorem, one file per suite.
STATEMENTS = HERE / "statements"
WORK = HERE / "_build" / "ci"
sys.path.insert(0, str(HERE / "scripts"))
from coverage import (
    ARM_FAMILIES, RV32, arm_instruction_variants,
    arm_success_marker, audit_proof_output, inventory, theorem_statements,
    without_comments)
from x86_forms import (
    comparison_status, export_status, known_gap, required_forms,
    validate_public_scope)

X86_FAMILIES = ("arithmetic", "shift", "vector")
# The theorems a known x86 gap requires instead of _EQ (x86-shift.ml): a
# closed counterexample and the exact relation between the two models.
GAP_THEOREMS = ("_DIFF", "_EXACT")
# The families with REMS bodies, each with its own source-qualified model
# and suite. REMS has no vector bodies at its pin.
X86_REMS_FAMILIES = tuple(sorted({row["family"] for row in required_forms()
                                  if export_status(row, "rems") == "available"}))


def public_scope():
    """Require full Arm/RV scope and the requested x86 GPR/AVX2 subset."""
    required = inventory()
    registered = {
        "aarch64": {"arm_" + name
                    for family in ARM_FAMILIES.values()
                    for name in family["instructions"]},
        "rv32im": {row["definition"] for row in RV32.values()},
    }
    for architecture, actual in registered.items():
        expected = {row["hol"] for row in required[architecture]["instructions"]}
        if actual != expected:
            raise ValueError(
                f"{architecture} public instruction inventory differs; "
                f"missing {sorted(expected - actual)}, "
                f"unexpected {sorted(actual - expected)}")
    # X86 covers the requested GPR/AVX2 subset, not every public x86 mnemonic.
    validate_public_scope(REPO)
    return len(registered["aarch64"]), len(registered["rv32im"])


def model_names():
    return tuple(sorted(
        ["arm-" + family + ".ml" for family in ARM_FAMILIES] +
        ["rv32.ml", "rv32-control.ml"] +
        ["x86-" + family + ".ml" for family in X86_FAMILIES] +
        ["x86-rems-" + family + ".ml" for family in X86_REMS_FAMILIES]))


def context_names():
    """The context file of each generation run."""
    return ("arm.context", "rv32.context", "x86-rems.context", "x86-shina.context")


def modes():
    """Proof suites to run."""
    return tuple(["arm-" + family for family in sorted(ARM_FAMILIES)] + ["rv32"] +
                 ["x86-" + family for family in X86_FAMILIES] +
                 ["x86-rems-" + family for family in X86_REMS_FAMILIES])


def rems_theorems(family):
    """A family's REMS theorems: agreement with s2n-bignum, or a closed
    counterexample where REMS differs."""
    return tuple(
        "SAIL_HL_X86_REMS_" +
        row["theorem"].removeprefix("SAIL_HL_X86_").removesuffix("_EQ") +
        ("_EQ" if comparison_status(row, "rems/s2n") == "agreement" else "_DIFF")
        for row in required_forms()
        if row["family"] == family and export_status(row, "rems") == "available")


def expected_theorems(mode):
    if mode == "rv32":
        return tuple("SAIL_HL_RV32_" + form + row["kind"] for form, row in RV32.items())
    if mode.startswith("x86-rems-") and mode[9:] in X86_REMS_FAMILIES:
        return rems_theorems(mode[9:])
    if mode.startswith("x86-") and mode[4:] in X86_FAMILIES:
        # A closed counterexample is evidence of a gap, never agreement.
        # Every listed gap requires kernel evidence just like an EQ claim,
        # and a theorem stating shina's relation exactly in terms of
        # s2n-bignum's.
        return tuple(
            row["theorem"].removesuffix("_EQ") + suffix
            for row in required_forms() if row["family"] == mode[4:]
            for suffix in (GAP_THEOREMS if known_gap(row) else ("_EQ",)))
    family = mode.removeprefix("arm-")
    if mode != "arm-" + family or family not in ARM_FAMILIES:
        raise ValueError("unknown conformance proof mode: " + mode)
    return tuple(
        variant["theorem"].removesuffix("_EQ") + "_SAFE_EQ"
        if ARM_FAMILIES[family].get("safe_domain_proofs")
        else variant["theorem"]
        for instruction in ARM_FAMILIES[family]["instructions"]
        for variant in arm_instruction_variants(family, instruction))


def completion_marker(mode):
    if mode == "rv32":
        return "SAIL_HOL_LIGHT_RV32_PROOFS_OK"
    if mode.startswith("x86-rems-") and mode[9:] in X86_REMS_FAMILIES:
        return "SAIL_HOL_LIGHT_X86_REMS_" + mode[9:].upper() + "_PROOFS_OK"
    if mode.startswith("x86-") and mode[4:] in X86_FAMILIES:
        return "SAIL_HOL_LIGHT_X86_" + mode[4:].upper() + "_PROOFS_OK"
    return arm_success_marker(mode.removeprefix("arm-"))


def theorem_roots():
    """The generated roots that each required theorem's statement is about."""
    roots = {}
    for family, specification in ARM_FAMILIES.items():
        for instruction in specification["instructions"]:
            for variant in arm_instruction_variants(family, instruction):
                for theorem in (variant["theorem"],
                                variant["theorem"].removesuffix("_EQ") + "_SAFE_EQ"):
                    roots[theorem] = {variant["constant"]}
    for form, row in RV32.items():
        roots["SAIL_HL_RV32_" + form + row["kind"]] = {rv32_constant(row)}
    for row in required_forms():
        root = row["theorem"].removeprefix("SAIL_HL_X86_").removesuffix("_EQ")
        shina, rems = row["constant"], rems_constant(row)
        for suffix in ("_EQ", "_DIFF", "_EXACT"):
            roots["SAIL_HL_X86_" + root + suffix] = {shina}
        for suffix in ("_EQ", "_DIFF"):
            roots["SAIL_HL_X86_REMS_" + root + suffix] = {rems}
    return roots


def theorem_definitions():
    """The s2n-bignum definition that each required theorem relates its
    root to: arm_<instruction>, riscv_<instruction> or x86_<instruction>."""
    definitions = {}
    for family, specification in ARM_FAMILIES.items():
        for instruction in specification["instructions"]:
            for variant in arm_instruction_variants(family, instruction):
                for theorem in (variant["theorem"],
                                variant["theorem"].removesuffix("_EQ") + "_SAFE_EQ"):
                    definitions[theorem] = "arm_" + instruction
    for form, row in RV32.items():
        definitions["SAIL_HL_RV32_" + form + row["kind"]] = row["definition"]
    for row in required_forms():
        root = row["theorem"].removeprefix("SAIL_HL_X86_").removesuffix("_EQ")
        for prefix, suffixes in (("SAIL_HL_X86_", ("_EQ", "_DIFF", "_EXACT")),
                                 ("SAIL_HL_X86_REMS_", ("_EQ", "_DIFF"))):
            for suffix in suffixes:
                definitions[prefix + root + suffix] = row["hol"]
    return definitions


def validate_models(directory):
    """Require the entire registered model set, not a selected passing
    subset, and in each model exactly the roots of model_roots."""
    public_scope()
    directory = Path(directory)
    actual = {path.name for path in directory.glob("*.ml")}
    expected = set(model_names())
    if actual != expected:
        missing = ", ".join(sorted(expected - actual)) or "none"
        extra = ", ".join(sorted(actual - expected)) or "none"
        raise ValueError(f"model inventory differs: missing {missing}; extra {extra}")
    for name in model_names():
        path = directory / name
        if not path.is_file() or path.is_symlink():
            raise ValueError("model must be a regular file: " + str(path))
        validate_roots(name, without_comments(path.read_text()))


def model_roots(name):
    """The roots that a model must define, each with its argument types in
    order, as coverage.py and x86_forms.py list them. A REMS root takes the
    HOL components standing for REMS's rflags and rip registers before its
    operands; a form without a REMS body is not exported."""
    stem = name.removesuffix(".ml")
    if stem.startswith("arm-"):
        family = stem.removeprefix("arm-")
        return {variant["constant"]: variant["argument_types"]
                for instruction in ARM_FAMILIES[family]["instructions"]
                for variant in arm_instruction_variants(family, instruction)}
    if stem.startswith("rv32"):
        return {rv32_constant(row): list(row["argument_types"])
                for row in RV32.values() if row["model"] == stem}
    if stem.startswith("x86-rems-"):
        return {rems_constant(row): ["(x86state,(32 word))component",
                                     "(x86state,64 word)component",
                                     *row["argument_types"]]
                for row in required_forms()
                if row["family"] == stem.removeprefix("x86-rems-") and
                export_status(row, "rems") == "available"}
    return {row["constant"]: row["argument_types"] for row in required_forms()
            if row["family"] == stem.removeprefix("x86-")}


def validate_roots(name, text):
    """Require exactly the roots of model_roots(name) in a model's text, each
    a relation between two states with the listed argument types.

    Memory profiles list only the encoded fields, so their reg_
    configuration components are left out of the comparison. Meaning is
    established by the reviewed proof statements, not inferred from these
    names or signatures.
    """
    expected = model_roots(name)
    stem = name.removesuffix(".ml")
    encoded_only = stem.startswith("arm-") and ARM_FAMILIES[
        stem.removeprefix("arm-")].get("encoded_signatures_only", False)
    state = ("armstate" if stem.startswith("arm-") else
             "riscvstate" if stem.startswith("rv32") else "x86state")
    actual = {}
    for constant, parameters in re.findall(
            r"^let (sail_hl_(?!shared_)\w+) = new_definition\n `\1([^\n]*) =\n"
            r"\s*\\\(s:" + state + r"\) \(t:" + state + r"\)\.", text, re.MULTILINE):
        if constant in actual:
            raise ValueError(f"duplicate root: {name}: {constant}")
        actual[constant] = [typ for parameter, typ in parameter_types(parameters)
                            if not (encoded_only and parameter.startswith("reg_"))]
    declared = re.findall(r"^let (sail_hl_(?!shared_)\w+) = new_definition\b",
                          text, re.MULTILINE)
    if actual != expected or sorted(declared) != sorted(expected):
        changed = sorted(constant for constant in actual.keys() & expected.keys()
                         if actual[constant] != expected[constant])
        raise ValueError(
            f"root signatures differ from the inventory: {name}; "
            f"missing {sorted(expected.keys() - actual.keys())}; "
            f"extra {sorted(set(declared) - expected.keys())}; "
            f"changed types {changed}; "
            f"{len(declared)} declarations, expected {len(expected)}")


def parameter_types(text):
    """The types of the top-level "(name:type)" groups in text, in order."""
    types, depth, start = [], 0, None
    for index, char in enumerate(text):
        if char == "(":
            if depth == 0:
                start = index + 1
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced root parameters")
            if depth == 0:
                name, colon, typ = text[start:index].partition(":")
                if not colon or not re.fullmatch(r"[A-Za-z0-9_]+", name):
                    raise ValueError("unexpected root parameter: " + text[start:index])
                types.append((name, typ))
        elif depth == 0 and not char.isspace():
            raise ValueError("unexpected text between root parameters")
    if depth:
        raise ValueError("unbalanced root parameters")
    return types


def rv32_constant(row):
    return "sail_hl_" + row["root"].replace("_", "_5f")


def rems_constant(row):
    return row["constant"].replace("sail_hl_X86_5f", "sail_hl_X86_5fREMS_5f", 1)


def validate_contexts(directory):
    """Require every run's context file, as a regular file."""
    directory = Path(directory)
    actual = {path.name for path in directory.glob("*.context")}
    if actual != set(context_names()):
        raise ValueError(
            "context file inventory differs: missing "
            f"{', '.join(sorted(set(context_names()) - actual)) or 'none'}; "
            f"extra {', '.join(sorted(actual - set(context_names()))) or 'none'}")
    for name in context_names():
        path = directory / name
        if not path.is_file() or path.is_symlink():
            raise ValueError("context file must be a regular file: " + str(path))


def compare_models(actual, expected=GENERATED):
    for directory in (expected, actual):
        validate_models(directory)
        validate_contexts(directory)
    changed = [
        name for name in model_names() + context_names()
        if (Path(actual) / name).read_bytes() != (Path(expected) / name).read_bytes()]
    if changed:
        raise ValueError("generated HOL files differ: " + ", ".join(changed) +
                         f"; the fresh files are in {actual}")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def guard(paths):
    return {str(path): digest(path) for path in paths}


def unchanged(snapshot):
    for filename, expected in snapshot.items():
        path = Path(filename)
        if not path.is_file() or digest(path) != expected:
            raise ValueError("CI input changed during checking: " + filename)


def run(command, log, env=None, cwd=REPO, timeout=None):
    """Run command with its output in log. With a timeout, the command runs
    in its own process group, and all of that group is killed when the
    time is up."""
    print("+ " + " ".join(map(str, command)), flush=True)
    with Path(log).open("wb") as stream:
        if timeout is None:
            returncode = subprocess.run(command, cwd=cwd, env=env, stdout=stream,
                                        stderr=subprocess.STDOUT).returncode
        else:
            process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                returncode = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                raise RuntimeError(f"command did not finish in {timeout} s; inspect {log}")
    if returncode != 0:
        # Show the end of the log too: a CI console may be all there is.
        tail = Path(log).read_text(errors="replace").splitlines()[-40:]
        raise RuntimeError(
            f"command exited {returncode}; inspect {log}; it ends:\n" +
            "\n".join("    " + line for line in tail))


def work_directory(prefix):
    WORK.mkdir(parents=True, exist_ok=True)
    return Path(tempfile.mkdtemp(prefix=prefix + "-", dir=WORK))


# The backend unit tests run as this many processes, at most one per core
# (test_backend.py). Each test has a 60-second limit.
BACKEND_TEST_SHARDS = max(1, min(24, len(os.sched_getaffinity(0))))
# Test files that need Sail but not HOL Light; generation runs them all.
UNIT_TESTS = ("test_ci", "test_x86_forms", "test_coverage", "test_layout",
              "test_entry_catalogue", "test_upstream_launcher", "test_selection",
              "test_simplify")
# The registered A64 base and Advanced SIMD instructions need none of these
# upstream Arm inputs, which hold the A32, T32, SVE and SME instructions.
# Dropping them roughly halves Sail's type check of the Arm model. They may
# only define their own functions and add clauses to the decoders below;
# check_arm_exclusions and check_arm_outputs enforce that.
ARM_EXCLUDED_INPUTS = ("src/instrs32.sail", "src/instrs64_sve.sail",
                       "src/instrs64_sme.sail")
ARM_EXCLUDED_DECODERS = frozenset(
    ["__DecodeT32", "__DecodeT16", "__DecodeA64_SVE", "__DecodeA64_SME"] +
    ["__DecodeA32_" + part for part in (
        "Unconditional", "DataProMisc", "LoadStoreImmLit", "LoadStoreReg",
        "Media", "BranchBlock", "SysASIMDFP")])


def arm_inputs(arm_directory):
    """Upstream's ordered Arm input list, as run.sh reads it."""
    return subprocess.run(
        ["make", "--no-print-directory", "-C", str(arm_directory),
         "--eval=hol-light-inputs: ; @printf '%s\\n' $(SAIL_SRCS)",
         "hol-light-inputs", "SAIL_DIR=" + os.environ["SAIL_DIR"]],
        check=True, capture_output=True, text=True).stdout.split()


def check_arm_exclusions(arm_directory):
    """Require that each excluded Arm input is self-contained.

    An excluded file may hold only val declarations, functions declared in
    that same file, and clauses of ARM_EXCLUDED_DECODERS. No remaining input
    may declare one of its functions: that declaration would lose its body
    silently. A remaining call into an excluded file fails Sail's check.
    """
    arm_directory = Path(arm_directory)
    inputs = arm_inputs(arm_directory)
    remaining = set()
    for name in inputs:
        if name not in ARM_EXCLUDED_INPUTS:
            remaining |= set(re.findall(r"^val\s+(\w+)",
                                        (arm_directory / name).read_text(), re.M))
    for name in ARM_EXCLUDED_INPUTS:
        if name not in inputs:
            raise ValueError("excluded Arm input is not an upstream input: " + name)
        text = (arm_directory / name).read_text()
        top_level = re.findall(r"^([A-Za-z$]\S*)(?:\s+(\S+))?", text, re.M)
        unexpected = sorted({word for word, _ in top_level} - {"val", "function"})
        clauses = set(re.findall(r"^function\s+clause\s+(\w+)", text, re.M))
        declared = set(re.findall(r"^val\s+(\w+)", text, re.M))
        defined = set(re.findall(r"^function\s+(?!clause\b)(\w+)", text, re.M))
        problems = (
            [f"top-level {word}" for word in unexpected] +
            [f"clause of {clause}" for clause in sorted(clauses - ARM_EXCLUDED_DECODERS)] +
            [f"undeclared {function}" for function in sorted(defined - declared)] +
            [f"declared elsewhere {function}" for function in sorted(defined & remaining)])
        if problems:
            raise ValueError(f"excluded Arm input {name} is not self-contained: " +
                             ", ".join(problems))


def check_arm_outputs(directory):
    """No Arm model may depend on a decoder whose clauses were excluded."""
    for model in sorted(Path(directory).glob("arm-*.ml")):
        record = model.with_suffix(".translation-log")
        if not record.is_file():
            raise ValueError("missing Arm translation log: " + record.name)
        reached = ARM_EXCLUDED_DECODERS & set(re.findall(r"\w+", record.read_text()))
        if reached:
            raise ValueError(f"{model.name} reaches decoders without their excluded "
                             f"clauses: {', '.join(sorted(reached))}")


def run_concurrently(commands):
    """Run independent commands at once and wait for every one of them.

    Each entry is (command, log, env). A failure does not stop the other
    commands, so no process outlives the check. All failures are reported
    after the last command has ended.
    """
    failures = []
    with ThreadPoolExecutor(max_workers=len(commands)) as workers:
        started = [workers.submit(run, command, log, env=env)
                   for command, log, env in commands]
        for future in started:
            try:
                future.result()
            except Exception as error:
                failures.append(error)
    if len(failures) == 1:
        raise failures[0]
    if failures:
        raise RuntimeError("\n".join(map(str, failures)))


def generate_models():
    """Use the real compiler once per architecture, with private output paths.

    After the plugin build, the controller tests, the backend test shards
    and the four compiler processes are independent and run at the same
    time. Each compiler process writes only its own models and inventory
    into the output directory. Within a process, Sail parses and checks
    the model once; its families are then translated by up to
    SAIL_HOL_GENERATION_JOBS forked workers (default 16). Each compiler
    process starts with an empty private z3 memo file; without one,
    run.sh would reuse its local memo from earlier runs.
    """
    for variable in ("SAIL_DIR", "SAIL_EXE", "SAIL_ARM_DIR", "SAIL_RISCV_DIR",
                     "SAIL_X86_SHINA_DIR", "SAIL_X86_REMS_DIR"):
        if not os.environ.get(variable):
            raise ValueError("set " + variable + " to the pinned external toolchain")
    jobs = int(os.environ.get("SAIL_HOL_GENERATION_JOBS", "16"))
    if not 1 <= jobs <= 64:
        raise ValueError("generation jobs must be between 1 and 64")
    check_arm_exclusions(Path(os.environ["SAIL_ARM_DIR"]) / "arm-v9.4-a")
    directory = work_directory("generation")
    outputs = directory / "models"
    outputs.mkdir()
    run(["bash", str(HERE / "build.sh")], directory / "backend-build.log")
    env = dict(os.environ, SAIL_HOL_PLUGIN=str(
        HERE / "_build" / "sail_plugin_hol_light.cmxs"))
    # This variable selects compiled plugin modules, not test output.
    env["SAIL_HOL_BUILD_DIR"] = str(HERE / "_build")
    common = ["--hol-light-output-dir", str(outputs), "--hol-light-jobs", str(jobs)]
    families = sorted(ARM_FAMILIES)
    selections = [
        argument for family in families[1:]
        for argument in ("--hol-light-family", family)]
    commands = [(["python3", str(HERE / "tests" / (name + ".py"))],
                 directory / (name + ".log"), env)
                for name in UNIT_TESTS]
    # One compiler process per architecture; each x86 model is a separate
    # process through the same plugin.
    selection = {"arm": [families[0], *selections], "rv32": ["all"],
                 "x86-shina": ["all"], "x86-rems": ["all"]}
    for architecture in selection:
        # A larger OCaml space_overhead makes the major GC run less often:
        # about a fifth less Sail CPU for 1.7 times the peak memory. Each
        # forked worker would otherwise mark its inherited heap repeatedly.
        launch = dict(env, OCAMLRUNPARAM=",".join(
            filter(None, (env.get("OCAMLRUNPARAM"), "o=400"))))
        if architecture == "arm":
            launch["SAIL_ARM_EXCLUDED_INPUTS"] = " ".join(ARM_EXCLUDED_INPUTS)
        commands.append(
            (["bash", str(HERE / "run.sh"), architecture, *selection[architecture],
              *common, "--memo-z3-path", str(directory / (architecture + "-smt-memo"))],
             directory / (architecture + "-generation.log"), launch))
    commands += [
        (["python3", str(HERE / "tests" / "test_backend.py"), "--shard",
          f"{index}/{BACKEND_TEST_SHARDS}"],
         directory / f"backend-tests-{index:02d}.log", env)
        for index in range(BACKEND_TEST_SHARDS)]
    run_concurrently(commands)
    validate_models(outputs)
    check_arm_outputs(outputs)
    return outputs


def check_generation():
    # Sail's answers depend on z3; record which one so CI logs show it.
    z3 = subprocess.run(["z3", "--version"], check=True, capture_output=True,
                        text=True).stdout.strip()
    print(f"z3 used by generation: {z3}")
    before = guard(GENERATED / name for name in model_names() + context_names())
    actual = generate_models()
    compare_models(actual)
    unchanged(before)
    print(f"All {len(model_names())} regenerated HOL files and the "
          f"{len(context_names())} context files match byte-for-byte.")
    print(f"Fresh models and context files: {actual}")


def refresh_models(source=None):
    """Explicit maintainer operation; CI never updates its expected results."""
    source = Path(source) if source else generate_models()
    # --from-directory also accepts a retained build directory with unrelated
    # logs and helper models. Only the exact registered filenames are imported.
    selected = work_directory("snapshot")
    names = model_names() + context_names()
    for name in names:
        shutil.copyfile(source / name, selected / name)
    validate_models(selected)
    validate_contexts(selected)
    if GENERATED.exists():
        extra = ({path.name for path in GENERATED.glob("*.ml")} |
                 {path.name for path in GENERATED.glob("*.context")}) - set(names)
        if extra:
            raise ValueError("refusing to remove unexpected checked-in models: " +
                             ", ".join(sorted(extra)))
    GENERATED.mkdir(parents=True, exist_ok=True)
    for name in names:
        (GENERATED / name).write_bytes((selected / name).read_bytes())
    validate_models(GENERATED)
    validate_contexts(GENERATED)
    print(f"Updated {len(model_names())} checked-in HOL models and the "
          f"{len(context_names())} context files in {GENERATED}")


# A proof suite takes minutes; one that runs an hour is stuck.
PROOF_TIMEOUT = 3600


def statement_path(mode):
    return STATEMENTS / (mode + ".txt")


def read_statements(path):
    """Checked-in statements: a name line, its statement lines, a blank line."""
    statements = {}
    for block in Path(path).read_text().split("\n\n"):
        if block.strip("\n"):
            name, _, statement = block.strip("\n").partition("\n")
            if name in statements:
                raise ValueError(f"{Path(path).name} records {name} twice")
            statements[name] = statement
    return statements


# HOL Light prints a subterm nested more than 100 boxes deep as ".". A
# binder's dot follows its last variable or a closing parenthesis.
PRINTER_ELISION = re.compile(r"(?<![\w')])\.")


def audit_statements(mode, lines):
    """Each theorem must state exactly what statements/<mode>.txt records.

    The name audit alone would accept a weakened statement, or one form's
    theorem printed under another form's name.
    """
    expected = expected_theorems(mode)
    path = statement_path(mode)
    if not path.is_file():
        raise ValueError(f"{mode}: no checked-in theorem statements in {path}")
    recorded = read_statements(path)
    if set(recorded) != set(expected):
        raise ValueError(f"{mode}: {path.name} does not list exactly the required theorems")
    printed = theorem_statements(lines, set(expected))
    changed = [name for name in expected if printed.get(name) != recorded[name]]
    if changed:
        raise ValueError(f"{mode}: {len(changed)} theorem statements differ from "
                         f"{path.name}, for example " + ", ".join(changed[:3]))
    # The name says which root a theorem is about; so must its statement.
    roots = theorem_roots()
    every_root = set().union(*roots.values())
    definitions = theorem_definitions()
    for name in expected:
        mentioned = set(re.findall(r"\bsail_hl_\w+", recorded[name])) & every_root
        if mentioned != roots[name]:
            raise ValueError(f"{mode}: {name} is about {sorted(mentioned)}, "
                             f"not {sorted(roots[name])}")
        # Likewise it must mention the s2n-bignum definition it is compared with.
        definition = definitions[name]
        if not re.search(rf"(?<![\w']){definition}(?![\w'])", recorded[name]):
            raise ValueError(f"{mode}: {name} does not mention {definition}")
        if PRINTER_ELISION.search(recorded[name]):
            raise ValueError(f"{mode}: the printer elided part of {name}")


def audit_proof(mode, log):
    """A suite passes only if its log passes the audit; a zero exit status
    of the driver is not enough."""
    lines = Path(log).read_text().splitlines()
    audit_proof_output(lines, expected_theorems(mode), completion_marker(mode), mode)
    audit_statements(mode, lines)


# HOL Light's loaders, as inline_load.ml and scripts/inline-proof.ml read them.
LOAD = re.compile(r'^[ \t]*(loadt|loads|needs)[ \t]*"([^"]+)"[ \t]*;;', re.MULTILINE)
# Text that creates a theorem without proof, or that changes what the
# printed statements mean: the parsing and printing interface, printers,
# the printer's depth and elision, overload priorities, OCaml's unchecked
# casts and unmarshalling, external (C) declarations, assignments to
# the_interface or through .contents, and a definition of check_axioms.
FORBIDDEN_PROOF_TEXT = re.compile(
    r"\b(?:new_axiom|mk_thm|CHEAT_TAC|override_interface|overload_interface|"
    r"reduce_interface|remove_interface|install_user_printer|delete_user_printer|"
    r"prioritize_\w+|(?:un)?parse_as_(?:infix|prefix|binder)|"
    r"(?:pp_)?set_ellipsis_text|(?:pp_)?set_max_boxes|Obj|Marshal|input_value|"
    r"external)\b|"
    r"\bthe_interface\s*:=|\.contents\s*<-|"
    r"\b(?:let|and)\s+(?:rec\s+)?check_axioms\b")
# Theorems reach the log only through sail_hl_report in proofs/report.ml.
PRINTING = re.compile(r"\b(?:(?:pp_)?print_thm|string_of_thm)\b")


def proof_closure(path, repo, loaded):
    """The comment-free text of a driver with the tools/sail proof files it
    loads spliced in at their load directives. Other loads become
    "LOAD <file>" lines. needs loads a file once; loaded collects the
    spliced files."""
    text = without_comments(Path(path).read_text())
    pieces, position = [], 0
    for directive in LOAD.finditer(text):
        pieces.append(text[position:directive.start()])
        position = directive.end()
        kind, target = directive.groups()
        if not target.startswith("tools/sail/proofs/"):
            pieces.append(f"LOAD {target}\n")
        elif not (kind == "needs" and target in loaded):
            loaded.add(target)
            pieces.append(proof_closure(Path(repo) / target, repo, loaded))
    pieces.append(text[position:])
    return "".join(pieces)


def check_proof_sources(repo):
    """Check the proof sources and models that a proof run will compile.

    This is a text check against accidents and lazy subversion, not a
    guarantee. No file under proofs/ or generated/, other than a README.md,
    may contain FORBIDDEN_PROOF_TEXT outside comments, and only
    proofs/report.ml may print a theorem. Each suite's driver,
    with the proof files it loads, must have a line that starts with
    "check_axioms ();;" after its last other load and before it prints its
    completion marker."""
    project = Path(repo) / HERE.relative_to(REPO)
    for source in sorted([*(project / "proofs").rglob("*"),
                          *(project / "generated").rglob("*")]):
        if source.is_file() and source.name != "README.md":
            text = without_comments(source.read_text())
            found = FORBIDDEN_PROOF_TEXT.findall(text)
            if source != project / "proofs" / "report.ml":
                found += PRINTING.findall(text)
            if found:
                raise ValueError(f"{source.relative_to(project)} uses "
                                 f"{', '.join(sorted(set(found)))}")
    for mode in modes():
        text = proof_closure(project / "proofs" / (mode + ".ml"), repo, set())
        marker = text.rfind('"' + completion_marker(mode) + '"')
        calls = list(re.finditer(r"^check_axioms\s*\(\s*\)\s*;;", text, re.MULTILINE))
        last_load = text.rfind("\nLOAD ")
        if marker < 0 or not calls or not last_load < calls[-1].start() < marker:
            raise ValueError(f"{mode}: the driver must start a line with "
                             "check_axioms ();; after its last load and before "
                             "printing its completion marker")


def snapshot_workspace():
    """Copy current sources, never ignored proof outputs or a theorem heap."""
    workspace = work_directory("proofs")
    names = subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=REPO).decode().split("\0")
    sources = {REPO / name for name in names if name}
    original = guard(sources)
    for source in sorted(sources):
        if source.is_symlink():
            raise ValueError("proof workspace source must not be a symlink: " + str(source))
        relative = source.relative_to(REPO)
        if "_build" in relative.parts or ".git" in relative.parts:
            raise ValueError("ignored build or Git metadata in proof sources: " + str(relative))
        target = workspace / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    unchanged(original)
    project = workspace / HERE.relative_to(REPO)
    staged = project / "_build"
    staged.mkdir()
    for name in model_names():
        shutil.copyfile(GENERATED / name, staged / name)
    validate_models(staged)
    copied = guard(workspace / Path(filename).relative_to(REPO)
                   for filename in original)
    copied.update(guard(staged / name for name in model_names()))
    return workspace, project, original, copied


def proof_order(directory):
    """Start larger models first; file size estimates cost, not proof time."""
    def weight(mode):
        names = (("rv32.ml", "rv32-control.ml") if mode == "rv32"
                 else (mode + ".ml",))
        return -sum((directory / name).stat().st_size for name in names), mode
    return sorted(modes(), key=weight)


def run_proofs(jobs, selected=()):
    """Run the selected proof suites, or all of them, and audit each."""
    if not 1 <= jobs <= 64:
        raise ValueError("proof jobs must be between 1 and 64")
    unknown = sorted(set(selected) - set(modes()))
    if unknown:
        raise ValueError("unknown proof suites: " + ", ".join(unknown) +
                         "; the suites are the files in statements/")
    if not os.environ.get("HOLDIR"):
        raise ValueError("set HOLDIR to the pinned native HOL Light build")
    validate_models(GENERATED)
    workspace, project, original, copied = snapshot_workspace()
    check_proof_sources(workspace)
    # HOLLIGHT_LOAD_PATH could resolve a load outside the snapshot, and
    # LD_PRELOAD would change the toolchain under every suite.
    env = {
        key: value for key, value in os.environ.items()
        if not key.startswith("SAIL_") and
        key not in ("HOLLIGHT_LOAD_PATH", "LD_PRELOAD")}
    # Recording a backtrace at every HOL Failure costs about a tenth of
    # proof time. Rerun a failing mode with check-proof.sh for one.
    env["SAIL_HOL_PROOF_BACKTRACE"] = "0"
    def prove(mode):
        log = project / "_build" / (mode + "-ci-run.log")
        output = project / "_build" / (mode + "-proof.log")
        try:
            run(["bash", str(project / "check-proof.sh"), mode],
                log, env=env, cwd=workspace,
                timeout=PROOF_TIMEOUT)
        except RuntimeError as error:
            raise RuntimeError(f"{error}; the kernel's output is in {output}")
        audit_proof(mode, output)
        count = len(expected_theorems(mode))
        print(f"{mode}: {count}/{count} theorems equal statements/{mode}.txt",
              flush=True)

    suites = [mode for mode in proof_order(project / "_build")
              if not selected or mode in selected]
    # Compile arm/proofs/base.ml once, in this snapshot. Each Arm suite
    # links the compiled code; every executable still initializes a fresh
    # kernel and runs the base anew.
    if any(mode.startswith("arm-") for mode in suites):
        run(["bash", str(project / "check-proof.sh"), "arm-base"],
            project / "_build" / "arm-base-ci-run.log", env=env, cwd=workspace,
            timeout=PROOF_TIMEOUT)
    failures = []
    skipped = []
    with ThreadPoolExecutor(max_workers=jobs) as workers:
        pending = {workers.submit(prove, mode): mode for mode in suites}
        for future in as_completed(pending):
            try:
                future.result()
            except CancelledError:
                skipped.append(pending[future])
            except Exception as error:
                failures.append(f"{pending[future]}: {error}")
                # Suites not yet started are not run after a failure.
                for other in pending:
                    other.cancel()
    # Drain every started worker before returning, including after a failure.
    unchanged(original)
    unchanged(copied)
    if failures:
        if skipped:
            failures.append("not run after the failure: " + ", ".join(sorted(skipped)))
        failures.append("Proof artifacts: " + str(project / "_build"))
        raise RuntimeError("\n".join(failures))
    total = sum(len(expected_theorems(mode)) for mode in suites)
    print(f"{len(suites)} of {len(modes())} suites passed: {total}/{total} "
          "theorems equal statements/.")
    print("Proof artifacts: " + str(project / "_build"))


def refresh_statements(directory, selected=()):
    """Explicit maintainer operation: record the statements of the selected
    suites, or of all, from the proof logs in directory, after auditing each
    log."""
    directory = Path(directory)
    unknown = sorted(set(selected) - set(modes()))
    if unknown:
        raise ValueError("unknown proof suites: " + ", ".join(unknown))
    chosen = [mode for mode in modes() if not selected or mode in selected]
    STATEMENTS.mkdir(parents=True, exist_ok=True)
    for mode in chosen:
        lines = (directory / (mode + "-proof.log")).read_text().splitlines()
        audit_proof_output(lines, expected_theorems(mode), completion_marker(mode), mode)
        printed = theorem_statements(lines, set(expected_theorems(mode)))
        statement_path(mode).write_text("".join(
            f"{name}\n{printed[name]}\n\n" for name in expected_theorems(mode)))
    print(f"Updated the theorem statements of {len(chosen)} proof suites in {STATEMENTS}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)
    subcommands.add_parser(
        "generate", help="regenerate every model and compare it with generated/")
    jobs = {"type": int, "default": os.environ.get("SAIL_HOL_PROOF_JOBS", "4"),
            "help": "parallel suites, 1-64 (default $SAIL_HOL_PROOF_JOBS or 4)"}
    proof = subcommands.add_parser(
        "proofs", help="prove and audit the suites on the models in generated/")
    proof.add_argument("--jobs", **jobs)
    proof.add_argument("suites", nargs="*", metavar="SUITE",
                       help="suites to check, as named in statements/ (default: all)")
    statements = subcommands.add_parser(
        "refresh-statements",
        help="record statements/ from the logs of a proof run")
    statements.add_argument("--from-directory", type=Path, required=True,
                            help="the proof artifacts directory that proofs printed")
    statements.add_argument("suites", nargs="*", metavar="SUITE",
                            help="suites to record (default: all)")
    refresh = subcommands.add_parser(
        "refresh", help="regenerate the models and replace generated/")
    refresh.add_argument("--from-directory", type=Path,
                         help="install models from this directory instead")
    args = parser.parse_args()
    if args.command == "generate":
        check_generation()
    elif args.command == "proofs":
        run_proofs(args.jobs, selected=tuple(args.suites))
    elif args.command == "refresh-statements":
        refresh_statements(args.from_directory, tuple(args.suites))
    else:
        refresh_models(args.from_directory)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
