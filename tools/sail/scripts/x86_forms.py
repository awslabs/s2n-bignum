"""Required instruction forms for the x86 Sail comparisons.

This catalogue is independent of the OCaml selection table and proof
drivers. It states what must be generated and checked; listing a form
proves nothing by itself. Byte operands distinguish REX low bytes from
legacy AL/CL/DL/BL/AH/CH/DH/BH. LEAVE adds an implicit eight-byte stack
load under a declared total flat-memory interpretation. Other encodings and
instructions outside the listed scopes, are not claimed here.
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
# Further scalar instructions, compared in register-direct forms only.
# MOVE: flags, no-operation forms, MOV and XCHG. SELECT: condition-code,
# extension and byte-swap forms, one root per condition code or register.
# BIT: bit test and modify. Two-operand IMUL is also compared with
# x86_IMUL, which is x86_IMUL3 dest (dest,src), in the arithmetic suite.
MOVE = ("CLC", "STC", "CMC", "CLD", "STD", "NOP", "ENDBR64", "NOP_N",
        "MOV", "XCHG")
SELECT = ("CMOV", "SET", "MOVZX", "MOVSX", "BSWAP")
BIT = ("BT", "BTC", "BTR", "BTS")
# COUNT: bit scans and counts.
COUNT = ("BSF", "BSR", "TZCNT", "LZCNT", "POPCNT")
# PEXT: parallel bit extract (BMI2), its own suite because the proof has
# an induction over the 32 or 64 steps of the loop.
PEXT = ("PEXT",)
EXTRA = MOVE + SELECT + BIT + COUNT + PEXT + ("IMUL",)
# s2n-bignum's condition names in the order of decode_condition.
CONDITIONS = ("O", "NO", "B", "NB", "Z", "NZ", "BE", "NBE",
              "S", "NS", "P", "NP", "L", "NL", "LE", "NLE")

# AVX2 data movement, shuffles, blends, inserts, extracts and mask
# extracts in register-direct form: (instruction, widths, variant,
# operands). A variant names an encoding of the same s2n-bignum definition
# that has its own opcode in the Sail model: STORE has the general or
# destination register in ModR/M.r/m (and the vector register in
# ModR/M.reg), F3 and D6 are the other VMOVQ encodings. R is a four-bit
# register number and I an imm8. Mask extracts exist at 256 bits only,
# because s2n-bignum's definitions read a 256-bit source.
AVX2_FORMS = (
    ("VPSHUFB", (128, 256), "", "RRR"),
    ("VPCMPEQW", (128, 256), "", "RRR"),
    ("VPSHUFD", (128, 256), "", "RRI"),
    ("VPUNPCKLQDQ", (128, 256), "", "RRR"),
    ("VPUNPCKHQDQ", (128, 256), "", "RRR"),
    ("VPBROADCASTD", (128, 256), "", "RR"),
    ("VPBROADCASTQ", (128, 256), "", "RR"),
    ("VPBROADCASTW", (128, 256), "", "RR"),
    ("VPBLENDD", (128, 256), "", "RRRI"),
    ("VPBLENDW", (128, 256), "", "RRRI"),
    ("VPERMQ", (256,), "", "RRI"),
    ("VPERMD", (256,), "", "RRR"),
    ("VINSERTI128", (256,), "", "RRRI"),
    ("VEXTRACTI128", (256,), "", "RRI"),
    ("VMOVSLDUP", (128, 256), "", "RR"),
    ("VMOVSHDUP", (128, 256), "", "RR"),
    ("VMOVDQA", (128, 256), "", "RR"),
    ("VMOVDQA", (128, 256), "_STORE", "RR"),
    ("VMOVDQU", (128, 256), "", "RR"),
    ("VMOVDQU", (128, 256), "_STORE", "RR"),
    ("VMOVD", (128,), "", "RR"),
    ("VMOVD", (128,), "_STORE", "RR"),
    ("VMOVQ", (128,), "", "RR"),
    ("VMOVQ", (128,), "_STORE", "RR"),
    ("VMOVQ", (128,), "_F3", "RR"),
    ("VMOVQ", (128,), "_D6", "RR"),
    ("VPEXTRW", (128,), "", "RRI"),
    ("VPINSRW", (128,), "", "RRRI"),
    ("VPINSRD", (128,), "", "RRRI"),
    ("VPINSRQ", (128,), "", "RRRI"),
    ("VPERM2I128", (256,), "", "RRRI"),
    ("VPBLENDVB", (128, 256), "", "RRRR"),
    ("VPCLMULQDQ", (128, 256), "", "RRRI"),
    ("VMOVMSKPS", (256,), "", "RR"),
    ("VPMOVMSKB", (256,), "", "RR"),
    # The width of PMOVMSKB is that of the destination register.
    ("PMOVMSKB", (32, 64), "", "RR"),
)
AVX2 = tuple(sorted({row[0] for row in AVX2_FORMS}))

# Legacy-encoded SSE integer instructions, VPEXTRD and VPEXTRQ, and
# VZEROUPPER: the instructions whose Sail bodies assign slices of the raw
# ZMM register (legacy SSE keeps bits 128 to 511, VZEROUPPER clears
# them) or read it directly. Same layout as AVX2_FORMS, at 128 bits;
# STORE puts the destination in ModR/M.r/m, F3 is MOVQ xmm, xmm/m64.
# VPEXTRD and VPEXTRQ write r/m, so their first operand is the general
# register.
SSE_FORMS = (
    ("PADDD", (128,), "", "RR"),
    ("PADDQ", (128,), "", "RR"),
    ("PAND", (128,), "", "RR"),
    ("PXOR", (128,), "", "RR"),
    ("PCMPGTW", (128,), "", "RR"),
    ("PCMPGTD", (128,), "", "RR"),
    ("PSHUFB", (128,), "", "RR"),
    ("PSHUFD", (128,), "", "RRI"),
    ("PBLENDW", (128,), "", "RRI"),
    ("PCLMULQDQ", (128,), "", "RRI"),
    ("PINSRD", (128,), "", "RRI"),
    ("PINSRQ", (128,), "", "RRI"),
    ("PSRLW", (128,), "", "RI"),
    ("PSRAD", (128,), "", "RI"),
    ("PSLLDQ", (128,), "", "RI"),
    ("PSRLDQ", (128,), "", "RI"),
    ("MOVAPS", (128,), "", "RR"),
    ("MOVAPS", (128,), "_STORE", "RR"),
    ("MOVUPS", (128,), "", "RR"),
    ("MOVUPS", (128,), "_STORE", "RR"),
    ("MOVDQA", (128,), "", "RR"),
    ("MOVDQA", (128,), "_STORE", "RR"),
    ("MOVDQU", (128,), "", "RR"),
    ("MOVDQU", (128,), "_STORE", "RR"),
    ("MOVD", (128,), "", "RR"),
    ("MOVD", (128,), "_STORE", "RR"),
    ("MOVQ", (128,), "", "RR"),
    ("MOVQ", (128,), "_STORE", "RR"),
    ("MOVQ", (128,), "_F3", "RR"),
    ("VPEXTRD", (128,), "", "RRI"),
    ("VPEXTRQ", (128,), "", "RRI"),
)
# AES-NI, also legacy-encoded (keeps bits 128 to 511); AESKEYGENASSIST has
# an imm8 round constant.
AES_FORMS = (
    ("AESENC", (128,), "", "RR"),
    ("AESENCLAST", (128,), "", "RR"),
    ("AESDEC", (128,), "", "RR"),
    ("AESDECLAST", (128,), "", "RR"),
    ("AESKEYGENASSIST", (128,), "", "RRI"),
)
AES = tuple(sorted({row[0] for row in AES_FORMS}))
# VZEROUPPER has no operand; its one root is X86_VZEROUPPER.
SSE = tuple(sorted({row[0] for row in SSE_FORMS} | {"VZEROUPPER"}))
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


def form(instruction, family, width, operands, legacy=False, variant=""):
    exported = {"MUL2": "MUL", "IMUL2": "IMUL1",
                "IMUL3": "IMUL", "MULX4": "MULX"}.get(instruction, instruction)
    suffix = f"{width}" + ("_LEGACY" if legacy else "") + variant + \
        "_" + operands
    root = "X86_" + exported + suffix
    register_bits = 3 if legacy else 4
    arguments = [f"{register_bits} word"] * operands.count("R")
    if "I" in operands:
        arguments.append("8 word")
    # Operand letters in the order of the arguments: R then I, or for the
    # AVX2 forms exactly as written.
    if family in ("avx2", "sse", "aes"):
        arguments = ["8 word" if letter == "I" else "4 word"
                     for letter in operands]
    return {
        "hol": "x86_" + instruction,
        "family": family,
        "width": width,
        "encoding": "legacy-byte" if legacy else
                    "SSE" if instruction == "PMOVMSKB" or
                    (family in ("sse", "aes") and
                     not instruction.startswith("V"))
                    else
                    "VEX" if instruction == "MULX4" or
                    family in ("vector", "avx2", "sse") else "REX",
        "operands": operands,
        "root": root,
        "constant": "sail_hl_" + root.replace("_", "_5f"),
        "theorem": "SAIL_HL_" + root + "_EQ",
        "argument_types": arguments,
    }


def extra_row(instruction, family, root, arguments, width=None, theorem=None,
              encoding="REX"):
    return {
        "hol": "x86_" + instruction,
        "family": family,
        "width": width,
        "encoding": encoding,
        "operands": "",
        "root": root,
        "constant": "sail_hl_" + root.replace("_", "_5f"),
        "theorem": theorem or "SAIL_HL_" + root + "_EQ",
        "argument_types": list(arguments),
    }


def extra_forms():
    """The register-direct forms of the further scalar instructions."""
    rows = []
    for name in ("CLC", "STC", "CMC", "CLD", "STD", "NOP", "ENDBR64"):
        rows.append(extra_row(name, "move", "X86_" + name, [],
                              encoding="legacy"))
    rows.append(extra_row("NOP_N", "move", "X86_NOP_N", ["4 word"]))
    for instruction in ("MOV", "XCHG"):
        for width in (64, 32, 16, 8):
            for legacy in ((False, True) if width == 8 else (False,)):
                rows.append(form(instruction, "move", width, "RR", legacy))
    for condition in CONDITIONS:
        for width in (64, 32):
            rows.append(extra_row("CMOV", "select",
                f"X86_CMOV{condition}{width}_RR", ["4 word"] * 2, width))
    for condition in CONDITIONS:
        rows.append(extra_row("SET", "select", f"X86_SET{condition}8_R",
                              ["4 word"], 8))
        rows.append(extra_row("SET", "select", f"X86_SET{condition}8_LEGACY_R",
                              ["3 word"], 8, encoding="legacy-byte"))
    for instruction in ("MOVZX", "MOVSX"):
        for source, legacy, widths in ((8, False, (64, 32)),
                                       (8, True, (32,)), (16, False, (64, 32))):
            for width in widths:
                bits = "3 word" if legacy else "4 word"
                rows.append(extra_row(
                    instruction, "select",
                    f"X86_{instruction}{width}_{source}"
                    + ("_LEGACY" if legacy else "") + "_RR", [bits] * 2, width,
                    encoding="legacy-byte" if legacy else "REX"))
    for width in (64, 32):
        for register in range(8):
            rows.append(extra_row("BSWAP", "select",
                f"X86_BSWAP{width}_R{register}", ["1 word"], width))
    for instruction in BIT:
        for width in (64, 32):
            rows.append(extra_row(instruction, "bit",
                f"X86_{instruction}{width}_RR", ["4 word"] * 2, width))
    for instruction in COUNT:
        for width in (64, 32, 16):
            rows.append(extra_row(instruction, "count",
                f"X86_{instruction}{width}_RR", ["4 word"] * 2, width))
    for width in (64, 32):
        rows.append(extra_row("PEXT", "pext", f"X86_PEXT{width}_RRR",
                              ["4 word"] * 3, width, encoding="VEX"))
    # MOVSXD is x86_MOVSX with a 32-bit source; it has its own opcode and
    # roots, next to the MOVSX forms.
    for width in (64, 32):
        rows.append(extra_row("MOVSX", "select", f"X86_MOVSXD{width}_32_RR",
                              ["4 word"] * 2, width))
    # Two-operand IMUL has one root, compared in the arithmetic suite with
    # x86_IMUL3 and, here, with x86_IMUL.
    for width in (64, 32, 16):
        row = extra_row("IMUL", "arithmetic", f"X86_IMUL{width}_RR",
                        ["4 word"] * 2, width,
                        f"SAIL_HL_X86_IMUL{width}_RR_IMUL_EQ")
        rows.append(row)
    return rows


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
    rows.extend(extra_forms())
    for instruction, widths, variant, operands in AVX2_FORMS:
        for width in widths:
            rows.append(form(instruction, "avx2", width, operands,
                             variant=variant))
    for instruction, widths, variant, operands in SSE_FORMS:
        for width in widths:
            rows.append(form(instruction, "sse", width, operands,
                             variant=variant))
    rows.append(extra_row("VZEROUPPER", "sse", "X86_VZEROUPPER", [],
                          encoding="VEX"))
    for instruction, widths, variant, operands in AES_FORMS:
        for width in widths:
            rows.append(form(instruction, "aes", width, operands,
                             variant=variant))
    # C9, without an operand-size override, in long mode. Its implicit
    # eight-byte load is interpreted at a total flat-memory boundary.
    rows.append(extra_row("LEAVE", "stack", "X86_LEAVE64", [], 64,
                          encoding="legacy"))
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
    if instruction in BIT:
        return "shina keeps ZF, s2n-bignum leaves it undefined"
    if instruction in ("BSF", "BSR"):
        return ("shina keeps the destination for a zero source, "
                "s2n-bignum leaves it undefined")
    return None


# Execution bodies selected after reading the pinned REMS sources. A listed
# body is an export candidate, not an export or a proof. The REMS comparison
# covers the original GPR and VECTOR scope only. Later shina-only additions
# are out of scope rather than claims that REMS lacks an instruction body.
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
    """Return the selected source body, or None when none is exported."""
    instruction = row["hol"].removeprefix("x86_")
    if source == "shina":
        return "present"
    if source != "rems":
        raise ValueError("unknown x86 source: " + source)
    return REMS_BODIES.get(instruction)


def rems_comparison_scope(row):
    """Whether a form belongs to the original REMS comparison scope."""
    instruction = row["hol"].removeprefix("x86_")
    return instruction in GPR + VECTOR


def export_status(row, source):
    """Classify a form as available, absent or out of scope."""
    if source == "rems" and not rems_comparison_scope(row):
        return "out-of-scope"
    return "absent" if source_body(row, source) is None else "available"


def absence(row, source):
    """Why an in-scope source has no body for a required form, or None."""
    instruction = row["hol"].removeprefix("x86_")
    if export_status(row, source) != "absent":
        return None
    return REMS_ABSENT[instruction]


def comparison_status(row, comparison):
    """The result that a suite must prove for one comparison of one
    required form: "agreement", "divergence-proved" (a closed
    counterexample), "absent" (REMS has no body) or "out-of-scope".

    The two comparisons, shina/s2n and rems/s2n, are independent. This
    records evidence; ci/check.py requires the corresponding theorems.
    """
    if comparison == "shina/s2n":
        return "divergence-proved" if known_gap(row) else "agreement"
    if comparison != "rems/s2n":
        raise ValueError("unknown x86 comparison: " + comparison)
    status = export_status(row, "rems")
    if status != "available":
        return status
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
    expected = {"x86_" + instruction
                for instruction in GPR + VECTOR + AVX2 + SSE + AES + EXTRA +
                ("LEAVE",)}
    missing = expected - names
    if missing:
        raise ValueError("requested x86 HOL definitions missing: " +
                         ", ".join(sorted(missing)))
    return len(GPR), len(VECTOR)
