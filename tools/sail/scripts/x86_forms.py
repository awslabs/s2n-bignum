"""Required register forms for the requested GPR/AVX2 instruction scope.

This catalogue is independent of the OCaml selection table and proof
drivers. It states what must be generated and checked; listing a form
proves nothing by itself. Byte operands distinguish REX low bytes from
legacy AL/CL/DL/BL/AH/CH/DH/BH. Other register and memory encodings, and
instructions outside the requested list, are not claimed here.
"""
from pathlib import Path
import re

GPR = (
    "ADD", "ADC", "ADCX", "ADOX", "SUB", "SBB", "CMP", "INC", "DEC", "NEG",
    "MUL2", "IMUL2", "IMUL3", "MULX4", "AND", "OR", "XOR", "NOT", "TEST",
    "SHL", "SHR", "SAR", "SHLD", "SHRD", "ROL", "ROR", "RCL", "RCR",
)
VECTOR_BINARY = (
    "VPADDB", "VPADDW", "VPADDD", "VPADDQ",
    "VPSUBB", "VPSUBW", "VPSUBD", "VPSUBQ",
    "VPMULLW", "VPMULLD", "VPMULHW", "VPMULHUW", "VPMULHRSW", "VPMULDQ",
    "VPMADDWD", "VPMADDUBSW", "VPAND", "VPANDN", "VPOR", "VPXOR",
    "VPSLLVD", "VPSRLVD", "VPSRLVQ", "VPCMPGTW", "VPCMPGTD", "VPACKUSWB",
)
VECTOR_UNARY = ("VPABSD", "VPTEST", "VPMOVSXBD", "VPMOVZXBD", "VPMOVZXBW")
VECTOR_IMMEDIATE = (
    "VPSLLW", "VPSLLD", "VPSLLQ", "VPSRLW", "VPSRLD", "VPSRLQ",
    "VPSRAW", "VPSRAD", "VPSRLDQ",
)
VECTOR = VECTOR_BINARY + VECTOR_UNARY + VECTOR_IMMEDIATE
SHIFT = ("SHL", "SHR", "SAR", "SHLD", "SHRD", "ROL", "ROR", "RCL", "RCR")


def scalar_shape(instruction):
    """Widths and operands that have genuine architectural register forms."""
    if instruction in ("ADCX", "ADOX", "MULX4"):
        widths = (32, 64)
    elif instruction in ("IMUL3", "SHLD", "SHRD"):
        widths = (16, 32, 64)
    else:
        widths = (8, 16, 32, 64)
    if instruction == "MULX4":
        operands = "RRR"
    elif instruction in ("SHLD", "SHRD"):
        operands = "RRI"
    elif instruction in SHIFT:
        operands = "RI"
    elif instruction in ("INC", "DEC", "NEG", "NOT", "MUL2", "IMUL2"):
        operands = "R"
    else:
        operands = "RR"
    return widths, operands


def form(instruction, family, width, operands, legacy=False):
    exported = {"MUL2": "MUL", "IMUL2": "IMUL1",
                "IMUL3": "IMUL", "MULX4": "MULX"}.get(instruction, instruction)
    suffix = f"{width}" + ("_LEGACY" if legacy else "") + "_" + operands
    root = "X86_" + exported + suffix
    register_bits = 3 if legacy else 4
    arguments = [f"{register_bits} word"] * operands.count("R")
    if "I" in operands:
        arguments.append("8 word")
    return {
        "hol": "x86_" + instruction,
        "family": family,
        "width": width,
        "encoding": "legacy-byte" if legacy else
                    "VEX" if family == "vector" else "REX",
        "operands": operands,
        "root": root,
        "constant": "sail_hl_" + root.replace("_", "_5f"),
        "theorem": "SAIL_HL_" + root + "_EQ",
        "argument_types": arguments,
    }


def required_forms():
    rows = []
    for instruction in GPR:
        widths, operands = scalar_shape(instruction)
        family = "shift" if instruction in SHIFT else "arithmetic"
        for width in widths:
            rows.append(form(instruction, family, width, operands))
            if width == 8:
                rows.append(form(instruction, family, width, operands, legacy=True))
    for names, operands in (
            (VECTOR_BINARY, "RRR"), (VECTOR_UNARY, "RR"),
            (VECTOR_IMMEDIATE, "RRI")):
        for instruction in names:
            for width in (128, 256):
                rows.append(form(instruction, "vector", width, operands))
    return tuple(rows)


def known_gap(row):
    """Document a discrepancy without dropping the form or accepting a proof.

    A caller must still report these rows as unmatched unless it supplies
    actual agreement evidence. In particular this function is not a list
    of allowed omissions from the generation or theorem inventory.
    """
    instruction = row["hol"].removeprefix("x86_")
    width = row["width"]
    if instruction in ("RCL", "RCR") and width in (8, 16):
        return "effective-zero OF difference; architectural classification unresolved"
    return None


# Execution bodies found by reading the pinned REMS sources. A listed body
# is an export candidate, not an export or a proof. The vector forms and
# the ADX/BMI2 instructions have no body at this revision; record them as
# absent rather than implementing them locally.
REMS_BODIES = {
    **{instruction: "x86_add_adc_sub_sbb_or_and_xor_cmp_g_e"
       for instruction in ("ADD", "ADC", "SUB", "SBB", "CMP",
                           "AND", "OR", "XOR")},
    "TEST": "x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g",
    "INC": "x86_inc_dec_fe_ff", "DEC": "x86_inc_dec_fe_ff",
    "NOT": "x86_not_neg_f6_f7", "NEG": "x86_not_neg_f6_f7",
    "MUL2": "x86_mul", "IMUL2": "x86_imul_op_en_m",
    "IMUL3": "x86_imul_op_en_rm",
    **{instruction: "x86_sal_sar_shl_shr_rcl_rcr_rol_ror"
       for instruction in ("SHL", "SHR", "SAR", "ROL", "ROR", "RCL", "RCR")},
    "SHLD": "x86_shld_shrd", "SHRD": "x86_shld_shrd",
}
# Why the pinned REMS model (0c6c023) has no body, as read in its
# model/ directory. Every branch of vex_opcodes_dispatch.sail ends in
# x86_model_error("Opcode Unimplemented in x86isa!") or a fault, and the
# ext_vex_* hooks in opcode_ext.sail return false; MULX is VEX 0F 38 F6.
# ADCX and ADOX are in the non-VEX 0F 38 map, whose escape, two-byte
# opcode 0x38, throws "Translation error: two-byte opcode 56 not
# translated" in two_byte_opcodes_dispatch.sail.
REMS_ABSENT = {
    "ADCX": "REMS's 0F 38 opcode map is untranslated (66 0F 38 F6)",
    "ADOX": "REMS's 0F 38 opcode map is untranslated (F3 0F 38 F6)",
    "MULX4": "REMS's VEX F2 0F 38 F6 branch ends in x86_model_error",
    **{instruction: "every VEX branch of REMS's dispatch ends in x86_model_error"
       for instruction in VECTOR},
}

# Exported REMS forms whose suite proves a counterexample against
# s2n-bignum instead of agreement: instruction -> widths. ROL/ROR leave OF
# undefined at masked count zero and ROR takes CF from the wrong end
# (rems-rotate-zero-of, rems-ror-cf); 8/16-bit SAR leaves CF undefined at
# counts of at least the width (rems-sar-cf); 8/16-bit rotates shift by a
# negative amount at counts above the rotated width, whose result is
# unknown (rems-rotate-wide-count). docs/X86-DIVERGENCES.md describes each
# named divergence.
REMS_S2N_GAPS = {"ROL": (8, 16, 32, 64), "ROR": (8, 16, 32, 64),
                 "RCL": (8, 16), "RCR": (8, 16), "SAR": (8, 16)}


def source_body(row, source):
    """Return the source execution body for a form, or None when absent."""
    instruction = row["hol"].removeprefix("x86_")
    if source == "shina":
        return "present"
    if source != "rems":
        raise ValueError("unknown x86 source: " + source)
    return REMS_BODIES.get(instruction)


def export_status(row, source):
    """"available" or "absent" (no body)."""
    return "absent" if source_body(row, source) is None else "available"


def absence(row, source):
    """Why a source has no body for a required form, or None."""
    instruction = row["hol"].removeprefix("x86_")
    if source_body(row, source) is not None:
        return None
    return REMS_ABSENT[instruction]


def comparison_status(row, comparison):
    """The result that a suite must prove for one comparison of one
    required form: "agreement", "divergence-proved" (a closed
    counterexample) or "absent" (REMS has no body).

    The two comparisons, shina/s2n and rems/s2n, are independent. This
    records evidence; ci/check.py requires the corresponding theorems.
    """
    if comparison == "shina/s2n":
        return "divergence-proved" if known_gap(row) else "agreement"
    if comparison != "rems/s2n":
        raise ValueError("unknown x86 comparison: " + comparison)
    if source_body(row, "rems") is None:
        return "absent"
    instruction = row["hol"].removeprefix("x86_")
    return ("divergence-proved" if row["width"] in REMS_S2N_GAPS.get(instruction, ())
            else "agreement")


def validate_public_scope(repo):
    """Check the requested symbols against the independently read HOL model."""
    # Import here so the data module has no dependency on a compiler/toolchain.
    from coverage import without_comments
    source = Path(repo) / "x86/proofs/x86.ml"
    names = set(re.findall(
        r"^(?:let|and)\s+(x86_[A-Z][A-Za-z0-9_]*)\s*=\s*new_definition\b",
        without_comments(source.read_text()), flags=re.MULTILINE))
    expected = {"x86_" + instruction for instruction in GPR + VECTOR}
    missing = expected - names
    if missing:
        raise ValueError("requested x86 HOL definitions missing: " +
                         ", ".join(sorted(missing)))
    return len(GPR), len(VECTOR)
