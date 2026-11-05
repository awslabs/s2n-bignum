#!/usr/bin/env python3
"""The AArch64 and RV32IM forms that CI requires, and the proof-log audit.

`ARM_FAMILIES` lists, for each AArch64 family, its public instructions and
the forms (widths, lanes, addressing modes) that each needs a theorem for;
`RV32` lists the RV32IM forms. Each form has the
argument types that its generated root must take. `ci/check.py` derives
the required theorem names from these tables and audits the proof logs
with `audit_proof_output` and `theorem_statements`. `inventory` lists the
public definitions of s2n-bignum's instruction files, against which the
tables are checked.
"""
from collections import Counter
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent.parent
REPO = HERE.parent.parent
BUILD = HERE / "_build"


def _rv32(forms, prefix, argument_types, kind="_EQ", model="rv32",
          definition=None):
    return {form: {"definition": definition or "riscv_" + form,
                   "root": prefix + form, "kind": kind, "model": model,
                   "argument_types": argument_types}
            for form in forms}


# Each RV32IM form: the s2n-bignum definition it is compared with, the Sail
# entry name of its root (backend/rv32.ml), the kind of its theorem
# SAIL_HL_RV32_<form><kind>, the model that defines the root and the root's
# argument types in order. A component argument is a quantified source
# register or configuration value. s2n-bignum guards the _SAFE_EQ forms
# with an alignment condition and permits every final state outside it.
# ECALL and EBREAK always trap in Sail, so their retirement relations hold
# for no final state, while s2n-bignum permits every one: _DIFF.
_R = ("5 word", "5 word", "5 word")
_I = ("12 word", "5 word", "5 word")
RV32 = {
    **_rv32(("LUI", "AUIPC"), "rv_UTYPE_", ("20 word", "5 word")),
    **_rv32(("ADDI", "SLTI", "SLTIU", "XORI", "ORI", "ANDI"), "rv_ITYPE_", _I),
    **_rv32(("SLLI", "SRLI", "SRAI"), "rv_SHIFTIOP_", ("6 word", "5 word", "5 word")),
    **_rv32(("ADD", "SUB", "SLL", "SLT", "SLTU", "XOR", "SRL", "SRA", "OR", "AND"),
            "rv_RTYPE_", _R),
    **_rv32(("MUL", "MULH", "MULHSU", "MULHU"), "rv_MUL_", _R),
    **_rv32(("DIV", "DIVU"), "rv_DIV_", _R),
    **_rv32(("REM", "REMU"), "rv_REM_", _R),
    **_rv32(("LB", "LBU"), "rv_LOAD_", _I),
    **_rv32(("LH", "LHU", "LW"), "rv_LOAD_", _I, "_SAFE_EQ"),
    **_rv32(("SB",), "rv_STORE_", _I),
    **_rv32(("SH", "SW"), "rv_STORE_", _I, "_SAFE_EQ"),
    **_rv32(("FENCE",), "rv_", ("(riscvstate,bool)component", "4 word", "4 word",
                                "4 word", "5 word", "5 word")),
    **_rv32(("FENCE_TSO", "PAUSE"), "rv_", (), definition="riscv_FENCE"),
    **_rv32(("BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU"), "rv_BTYPE_",
            ("13 word", "5 word", "5 word"), "_SAFE_EQ", "rv32-control"),
    **_rv32(("JAL",), "rv_", ("21 word", "5 word"), "_SAFE_EQ", "rv32-control"),
    **_rv32(("JALR",), "rv_", _I, "_SAFE_EQ", "rv32-control"),
    **_rv32(("ECALL",), "rv_", ("(riscvstate,sail_hl_type_Privilege)component",),
            "_DIFF", "rv32-control"),
    **_rv32(("EBREAK",), "rv_", (), "_DIFF", "rv32-control"),
}
ARM_ADDSUB_OPERATIONS = ("ADD", "ADDS", "SUB", "SUBS", "CMN", "CMP")
ARM_EXTEND_KINDS = ("UXTB", "UXTH", "UXTW", "UXTX", "SXTB", "SXTH", "SXTW", "SXTX")
ARM_ADDSUB_FORMS = (
    "IMM", "SHIFT",
    *(f"EXT_{kind}_{shift}" for kind in ARM_EXTEND_KINDS for shift in range(5)),
)
ARM_VECTOR_ELEMENT_FORMS = ("E8", "E16", "E32", "E64")
ARM_VECTOR_DUPLICATE_ELEMENT_FORMS = tuple(
    element + "_" + half
    for element in ARM_VECTOR_ELEMENT_FORMS for half in ("LO", "HI"))
ARM_VECTOR_WIDENING_FORMS = ("E8", "E16", "E32")
# QC range updates read the original packed FPSR value before the final
# write is excluded. Keep that declared read component in each signature.
ARM_FPSR_READ_COMPONENT = "(armstate,(64 word))component"
ARM_FPCR_READ_COMPONENT = "(armstate,(64 word))component"
ARM_VECTOR_WIDENING_INDEXED_FORMS = ("E16_LO", "E16_HI", "E32_LO", "E32_HI")
ARM_VECTOR_WIDENING_ACCUMULATES = (
    "SMLAL_VEC", "SMLAL2_VEC", "SMLSL_VEC", "SMLSL2_VEC",
    "UMLAL_VEC", "UMLAL2_VEC", "UMLSL_VEC", "UMLSL2_VEC",
)
ARM_VECTOR_WIDENING_ACCUMULATE_INDEXED = (
    "SMLAL_VEC", "SMLAL2_VEC", "UMLSL_VEC", "UMLSL2_VEC",
)
ARM_CONDITIONAL_BRANCH_ALIASES = (
    "BEQ", "BNE", "BCS", "BHS", "BCC", "BLO", "BMI", "BPL",
    "BVS", "BVC", "BHI", "BLS", "BGE", "BLT", "BGT", "BLE", "BAL", "BNV",
)
ARM_BRANCH_PC_TYPE = "(armstate,64 word)component"
ARM_PSTATE_COMPONENT_TYPE = (
    "(armstate,(1 word#1 word#1 word#1 word#2 word#2 word#1 word))component")
ARM_CONDITIONAL_BRANCH_PROFILES = {
    "Bcond": (
        {"width": 64, "form": "condition-offset", "suffix": "",
         "argument_types": (ARM_BRANCH_PC_TYPE, "4 word", "19 word")},),
    **{name: (
        {"width": 64, "form": "condition-alias-offset", "suffix": "",
         "argument_types": (ARM_BRANCH_PC_TYPE, "19 word")},)
       for name in ARM_CONDITIONAL_BRANCH_ALIASES},
    **{name: tuple(
        {"width": width, "form": "register-offset", "suffix": str(width),
         "argument_types": (ARM_BRANCH_PC_TYPE, "5 word", "19 word")}
        for width in (32, 64))
       for name in ("CBZ", "CBNZ")},
    **{name: (
        {"width": 32, "form": "bits0..31", "suffix": "32",
         "argument_types": (ARM_BRANCH_PC_TYPE, "5 word", "5 word", "14 word")},
        {"width": 64, "form": "bits32..63", "suffix": "64_HI",
         "argument_types": (ARM_BRANCH_PC_TYPE, "5 word", "5 word", "14 word")})
       for name in ("TBZ", "TBNZ")},
}
ARM_BRANCH_BASIC_PROFILES = {
    "B": (
        {"width": 64, "form": "encoded-imm26", "suffix": "",
         "argument_types": (ARM_BRANCH_PC_TYPE, "26 word")},),
    "BL": (
        {"width": 64, "form": "encoded-imm26", "suffix": "",
         "argument_types": (ARM_BRANCH_PC_TYPE, "26 word")},),
    "RET": (
        {"width": 64, "form": "encoded-register5", "suffix": "",
         "argument_types": (ARM_BRANCH_PC_TYPE, "5 word")},),
}
ARM_VECTOR_SHIFT_SIGNATURES = {
    "*": {
        str(width) + element:
        (f"{ {'E8': 3, 'E16': 4, 'E32': 5, 'E64': 6}[element]} word",
         "5 word", "5 word")
        for width in (64, 128)
        for element in ARM_VECTOR_ELEMENT_FORMS
    }}

ARM_FAMILIES = {
    "vector-add-reduce": {
        "instructions": ("ADDV",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("E8", "E16", "E32"),
        "forms_by_width": {
            "64": ("E8", "E16"), "128": ("E8", "E16", "E32")},
        "form_root_suffixes": {form: form for form in ("E8", "E16", "E32")},
        "separate_form_exports": True,
        "signatures": {
            "*": {str(width) + element:
                  (ARM_FPCR_READ_COMPONENT, "5 word", "5 word")
                  for width, elements in (
                      (64, ("E8", "E16")), (128, ("E8", "E16", "E32")))
                  for element in elements}},
    },
    "vector-fpbits": {
        "instructions": ("FMOV_FtoI", "FMOV_ItoF"),
        "root_prefix": "arm_",
        "profiles_by_instruction": {
            "FMOV_FtoI": tuple(
                {"width": width, "form": part, "suffix": f"{width}_{part}",
                 "argument_types": (ARM_FPCR_READ_COMPONENT, "5 word", "5 word")}
                for width, part in ((32, "LO"), (64, "LO"), (64, "HI"))),
            "FMOV_ItoF": tuple(
                {"width": 64, "form": part, "suffix": "64_" + part,
                 "argument_types": (ARM_FPCR_READ_COMPONENT, "5 word", "5 word")}
                for part in ("LO", "HI")),
        },
    },
    "vector-poly": {
        "instructions": ("PMULL_VEC", "PMULL2_VEC"),
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ("E8", "E64"),
        "form_root_suffixes": {"E8": "E8", "E64": "E64"},
        "separate_form_exports": True,
        "signatures": {
            "*": {"128" + form: ("5 word", "5 word", "5 word")
                  for form in ("E8", "E64")}},
    },
    "vector-doubling": {
        "instructions": ("SQDMULH_VEC", "SQRDMULH_VEC"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": (
            "E16", "E32", "E16_LO", "E16_HI", "E32_LO", "E32_HI"),
        "form_root_suffixes": {
            form: form for form in
            ("E16", "E32", "E16_LO", "E16_HI", "E32_LO", "E32_HI")},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + form: (ARM_FPSR_READ_COMPONENT,) + (
                    ("5 word", "5 word", "4 word", "2 word") if form.startswith("E16_")
                    else ("5 word", "5 word", "5 word", "1 word") if form.startswith("E32_")
                    else ("5 word", "5 word", "5 word"))
                for width in (64, 128) for form in
                ("E16", "E32", "E16_LO", "E16_HI", "E32_LO", "E32_HI")}},
    },
    "vector-saturating-narrow": {
        "instructions": ("SQSHRUN", "SQSHRUN2", "SQRSHRUN", "SQRSHRUN2"),
        "root_prefix": "arm_",
        "required_widths": (64,),
        "required_forms": ARM_VECTOR_WIDENING_FORMS,
        "form_root_suffixes": {form: form for form in ARM_VECTOR_WIDENING_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                "64" + form: (
                    ARM_FPSR_READ_COMPONENT, str(width) + " word", "5 word", "5 word")
                for form, width in (("E8", 3), ("E16", 4), ("E32", 5))}},
    },
    "vector-table": {
        "instructions": ("TBL", "TBL2", "TBL3"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("complete-byte-indices-consecutive-q-tables",),
        "signatures": {
            "*": {
                str(width): ("5 word", "5 word", "5 word")
                for width in (64, 128)}},
    },
    "bitfield": {
        "instructions": ("BFM", "SBFM", "UBFM", "ASR", "LSR", "LSL"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("complete-decoded-immediates",),
        "signatures": {
            operation: {
                str(width): ("5 word", "5 word") + (
                    (f"{5 if width == 32 else 6} word",) *
                    (2 if operation in ("BFM", "SBFM", "UBFM") else 1))
                for width in (32, 64)}
            for operation in ("BFM", "SBFM", "UBFM", "ASR", "LSR", "LSL")},
    },
    "vector-left-shift": {
        "instructions": ("SHL_VEC",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        # 64E64 is the scalar SHL Dd, Dn, #amount.
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS,
            "128": ARM_VECTOR_ELEMENT_FORMS,
        },
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": ARM_VECTOR_SHIFT_SIGNATURES,
    },
    "vector-variable-shift": {
        "instructions": ("USHL_VEC",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS[:-1],
            "128": ARM_VECTOR_ELEMENT_FORMS},
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + element: ("5 word", "5 word", "5 word")
                for width in (64, 128) for element in ARM_VECTOR_ELEMENT_FORMS
                if width == 128 or element != "E64"}},
    },
    "fp-select": {
        "instructions": ("FCSEL",),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("complete-condition-fields",),
        "signatures": {
            "*": {
                str(width): ("4 word", "5 word", "5 word", "5 word")
                for width in (32, 64)}},
    },
    "vector-polynomial-multiply": {
        "instructions": ("PMUL_VEC",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("E8",),
        "form_root_suffixes": {"E8": "E8"},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + "E8": ("5 word", "5 word", "5 word")
                for width in (64, 128)}},
    },
    "vector-shift-narrow": {
        "instructions": ("SHRN", "SHRN2", "RSHRN", "RSHRN2"),
        "root_prefix": "arm_",
        "required_widths": (64,),
        "required_forms": ARM_VECTOR_WIDENING_FORMS,
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_WIDENING_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                "64" + form: (
                    f"{ {'E8': 3, 'E16': 4, 'E32': 5}[form]} word",
                    "5 word", "5 word")
                for form in ARM_VECTOR_WIDENING_FORMS}},
    },
    "hints": {
        "instructions": ("NOP", "BTI"),
        "root_prefix": "arm_",
        "export_names": {"BTI": "BTI_C"},
        "profiles_by_instruction": {
            "NOP": (
                {"width": 64, "form": "exact-nop-encoding", "suffix": "",
                 "argument_types": ()},),
            "BTI": (
                {"width": 64, "form": "exact-bti-c-encoding", "suffix": "",
                 "argument_types": (ARM_PSTATE_COMPONENT_TYPE,)},),
        },
    },
    "branch-absolute-execute": {
        "instructions": ("BL_ABSOLUTE",),
        "root_prefix": "arm_",
        "export_names": {"BL_ABSOLUTE": "BL_ABSOLUTE_EXECUTE"},
        "profiles_by_instruction": {
            "BL_ABSOLUTE": (
                {"width": 64, "form": "unrestricted-offset64-execute-helper",
                 "suffix": "", "argument_types": (
                     ARM_BRANCH_PC_TYPE, "64 word")},),
        },
    },
    "branch-basic": {
        "instructions": ("B", "BL", "RET"),
        "root_prefix": "arm_",
        "profiles_by_instruction": ARM_BRANCH_BASIC_PROFILES,
    },
    "vector-right-shift": {
        "instructions": ("USHR_VEC", "SSHR_VEC", "SRSHR_VEC", "USRA_VEC"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS[:-1],
            "128": ARM_VECTOR_ELEMENT_FORMS,
        },
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": ARM_VECTOR_SHIFT_SIGNATURES,
    },
    "vector-shift-insert": {
        "instructions": ("SLI_VEC", "SRI_VEC"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS[:-1],
            "128": ARM_VECTOR_ELEMENT_FORMS,
        },
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": ARM_VECTOR_SHIFT_SIGNATURES,
    },
    "branch-conditional": {
        "instructions": (
            "Bcond", *ARM_CONDITIONAL_BRANCH_ALIASES, "CBZ", "CBNZ", "TBZ", "TBNZ"),
        "root_prefix": "arm_",
        "export_names": {"Bcond": "BCOND"},
        "profiles_by_instruction": ARM_CONDITIONAL_BRANCH_PROFILES,
    },
    "carry": {
        "instructions": ("ADC", "ADCS", "SBC", "SBCS", "NGC", "NGCS"),
        "root_prefix": "ARM_",
        "required_widths": (32, 64),
        "required_forms": ("register",),
        "signatures": {
            name: {str(width): ("5 word",) * (2 if name.startswith("NGC") else 3)
                   for width in (32, 64)}
            for name in ("ADC", "ADCS", "SBC", "SBCS", "NGC", "NGCS")},
    },
    "select": {
        "instructions": (
            "CSEL", "CSINC", "CSINV", "CSNEG", "CINC", "CINV", "CNEG",
            "CSET", "CSETM"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("register",),
        "signatures": {
            name: {str(width): ("4 word",) + ("5 word",) * operands
                   for width in (32, 64)}
            for names, operands in ((("CSEL", "CSINC", "CSINV", "CSNEG"), 3),
                                    (("CINC", "CINV", "CNEG"), 2),
                                    (("CSET", "CSETM"), 1))
            for name in names},
    },
    "multiply": {
        "instructions": ("MADD", "MSUB", "MUL", "MNEG"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("register",),
        "signatures": {
            name: {str(width): ("5 word",) * (4 if name in ("MADD", "MSUB") else 3)
                   for width in (32, 64)}
            for name in ("MADD", "MSUB", "MUL", "MNEG")},
    },
    "multiply-long": {
        "instructions": ("UMADDL", "UMSUBL", "UMULL", "UMNEGL"),
        "root_prefix": "arm_",
        "required_widths": (64,),
        "required_forms": ("w32-multiplicands-x64-accumulator",),
        "signatures": {
            name: {"64": ("5 word",) * (4 if name in ("UMADDL", "UMSUBL") else 3)}
            for name in ("UMADDL", "UMSUBL", "UMULL", "UMNEGL")},
    },
    "compare": {
        "instructions": ("CCMN", "CCMP"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("register", "immediate"),
        # The first, 1-bit argument, use_immediate, selects the form.
        "signatures": {"*": {
            str(width): ("1 word", "5 word", "5 word", "4 word", "4 word")
            for width in (32, 64)}},
    },
    "address": {
        "instructions": ("ADR", "ADRP"),
        "root_prefix": "arm_",
        "required_widths": (64,),
        "required_forms": ("decoded-imm21",),
        "signatures": {"*": {"64": (ARM_BRANCH_PC_TYPE, "5 word", "21 word")}},
    },
    "multiply-high": {
        "instructions": ("SMULH", "UMULH"),
        "root_prefix": "arm_",
        "required_widths": (64,),
        "required_forms": ("x64-high-product",),
        "signatures": {"*": {"64": ("5 word", "5 word", "5 word")}},
    },
    "shift": {
        "instructions": ("LSLV", "LSRV", "ASRV", "RORV"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("register-masked-amount",),
        "signatures": {
            "*": {str(width): ("5 word", "5 word", "5 word")
                  for width in (32, 64)}},
    },
    "move": {
        "instructions": ("MOVK", "MOVN", "MOVZ"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("all-legal-halfword-positions",),
        "signatures": {
            "*": {str(width): ("5 word", "16 word", f"{width // 32} word")
                  for width in (32, 64)}},
    },
    "logical": {
        "instructions": (
            "AND", "ANDS", "BIC", "BICS", "ORR", "ORN", "EOR", "EON",
            "MOV", "MVN", "TST"),
        "root_prefix": "ARM_",
        "required_widths": (32, 64),
        "required_forms": ("SHIFT",),
        "forms_by_instruction": {
            name: ("IMM", "SHIFT")
            for name in ("AND", "ANDS", "ORR", "EOR", "MOV", "TST")},
        "separate_form_exports": True,
        "signatures": {
            name: {
                str(width) + "_" + form: (
                    (("5 word",) if name in ("MOV", "TST") else
                     ("5 word", "5 word")) + (f"{width} word",)
                    if form == "IMM" else
                    (("5 word", "5 word") if name in ("MOV", "MVN", "TST")
                     else ("5 word", "5 word", "5 word")) +
                    (f"{5 if width == 32 else 6} word", "sail_hl_type_ShiftType"))
                for width in (32, 64)
                for form in (
                    ("IMM", "SHIFT") if name in
                    ("AND", "ANDS", "ORR", "EOR", "MOV", "TST") else ("SHIFT",))
            } for name in (
                "AND", "ANDS", "BIC", "BICS", "ORR", "ORN", "EOR", "EON",
                "MOV", "MVN", "TST")},
    },
    "extract": {
        "instructions": ("EXTR", "ROR"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("register-all-legal-positions",),
        "signatures": {
            instruction: {
                str(width): (("5 word", "5 word", "5 word")
                             if instruction == "EXTR" else ("5 word", "5 word")) +
                (f"{5 if width == 32 else 6} word",)
                for width in (32, 64)}
            for instruction in ("EXTR", "ROR")},
    },
    "addsub": {
        "instructions": (*ARM_ADDSUB_OPERATIONS, "NEG", "NEGS"),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ARM_ADDSUB_FORMS,
        "forms_by_instruction": {
            "NEG": ("plain", "SHIFT"), "NEGS": ("plain", "SHIFT")},
        "form_root_suffixes": {"plain": ""},
        "separate_form_exports": True,
        "signatures": {
            **{
                name: {
                    str(width) + "_" + form: (
                        (("5 word",) if name in ("CMN", "CMP") else
                         ("5 word", "5 word")) + (f"{width} word",)
                        if form == "IMM" else
                        (("5 word", "5 word") if name in ("CMN", "CMP") else
                         ("5 word", "5 word", "5 word")) +
                        ((f"{5 if width == 32 else 6} word",
                          "sail_hl_type_ShiftType") if form == "SHIFT" else ())
                    )
                    for width in (32, 64) for form in ARM_ADDSUB_FORMS
                } for name in ARM_ADDSUB_OPERATIONS
            },
            **{
                name: {
                    **{str(width): ("5 word", "5 word") for width in (32, 64)},
                    **{
                        str(width) + "_SHIFT": (
                            "5 word", "5 word", f"{5 if width == 32 else 6} word",
                            "sail_hl_type_ShiftType")
                        for width in (32, 64)},
                }
                for name in ("NEG", "NEGS")
            },
        },
    },
    "vector-logical": {
        "instructions": (
            "AND_VEC", "BIC_VEC", "ORR_VEC", "EOR_VEC", "BIT", "BIF", "MOV_VEC"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("REG",),
        "forms_by_instruction": {
            name: ("REG", "IMM") for name in ("BIC_VEC", "ORR_VEC")},
        "separate_form_exports": True,
        "signatures": {
            name: {
                str(width) + "_" + form: (
                    ("5 word", f"{width} word") if form == "IMM" else
                    ("5 word", "5 word") if name == "MOV_VEC" else
                    ("5 word", "5 word", "5 word"))
                for width in (64, 128)
                for form in (
                    ("REG", "IMM") if name in ("BIC_VEC", "ORR_VEC") else ("REG",))
            } for name in (
                "AND_VEC", "BIC_VEC", "ORR_VEC", "EOR_VEC", "BIT", "BIF", "MOV_VEC")},
    },
    "vector-multiply-long": {
        "instructions": ("SMULL_VEC", "SMULL2_VEC", "UMULL_VEC", "UMULL2_VEC"),
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ARM_VECTOR_WIDENING_FORMS,
        "forms_by_instruction": {
            instruction: (*ARM_VECTOR_WIDENING_FORMS,
                          *ARM_VECTOR_WIDENING_INDEXED_FORMS)
            for instruction in ("UMULL_VEC", "UMULL2_VEC")},
        "form_root_suffixes": {
            form: form for form in
            (*ARM_VECTOR_WIDENING_FORMS, *ARM_VECTOR_WIDENING_INDEXED_FORMS)},
        "separate_form_exports": True,
        "signatures": {
            instruction: {
                "128" + form: (
                    ("5 word", "5 word", "4 word", "2 word") if form.startswith("E16_")
                    else ("5 word", "5 word", "5 word", "1 word") if form.startswith("E32_")
                    else ("5 word", "5 word", "5 word"))
                for form in (
                    (*ARM_VECTOR_WIDENING_FORMS, *ARM_VECTOR_WIDENING_INDEXED_FORMS)
                    if instruction.startswith("U") else ARM_VECTOR_WIDENING_FORMS)
            } for instruction in ("SMULL_VEC", "SMULL2_VEC", "UMULL_VEC", "UMULL2_VEC")},
    },
    "vector-multiply-accumulate-long": {
        "instructions": ARM_VECTOR_WIDENING_ACCUMULATES,
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ARM_VECTOR_WIDENING_FORMS,
        "forms_by_instruction": {
            instruction: (*ARM_VECTOR_WIDENING_FORMS,
                          *ARM_VECTOR_WIDENING_INDEXED_FORMS)
            for instruction in ARM_VECTOR_WIDENING_ACCUMULATE_INDEXED},
        "form_root_suffixes": {
            form: form for form in
            (*ARM_VECTOR_WIDENING_FORMS, *ARM_VECTOR_WIDENING_INDEXED_FORMS)},
        "separate_form_exports": True,
        "signatures": {
            instruction: {
                "128" + form: (
                    ("5 word", "5 word", "4 word", "2 word") if form.startswith("E16_")
                    else ("5 word", "5 word", "5 word", "1 word") if form.startswith("E32_")
                    else ("5 word", "5 word", "5 word"))
                for form in (
                    (*ARM_VECTOR_WIDENING_FORMS, *ARM_VECTOR_WIDENING_INDEXED_FORMS)
                    if instruction in ARM_VECTOR_WIDENING_ACCUMULATE_INDEXED
                    else ARM_VECTOR_WIDENING_FORMS)
            } for instruction in ARM_VECTOR_WIDENING_ACCUMULATES},
    },
    "vector-extract": {
        "instructions": ("EXT",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("all-legal-byte-offsets",),
        "signatures": {
            "*": {str(width): ("5 word", "5 word", "5 word",
                              "3 word" if width == 64 else "4 word")
                  for width in (64, 128)}},
    },
    "vector-addsub": {
        "instructions": ("ADD_VEC", "SUB_VEC"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS[:-1], "128": ARM_VECTOR_ELEMENT_FORMS},
        "form_root_suffixes": {form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + element: ("5 word", "5 word", "5 word")
                for width in (64, 128) for element in ARM_VECTOR_ELEMENT_FORMS
                if width == 128 or element != "E64"}},
    },
    "vector-addsub-widen": {
        "instructions": (
            "SSUBL", "SSUBL2", "USUBL", "USUBL2", "SADDW", "SADDW2",
            "SSUBW", "SSUBW2", "USUBW", "USUBW2"),
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ARM_VECTOR_WIDENING_FORMS,
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_WIDENING_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                "128" + form: ("5 word", "5 word", "5 word")
                for form in ARM_VECTOR_WIDENING_FORMS}},
    },
    "vector-insert": {
        "instructions": ("INS", "INS_GEN"),
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ARM_VECTOR_DUPLICATE_ELEMENT_FORMS,
        "forms_by_instruction": {"INS_GEN": ARM_VECTOR_ELEMENT_FORMS},
        "form_root_suffixes": {
            form: form for form in (
                *ARM_VECTOR_DUPLICATE_ELEMENT_FORMS, *ARM_VECTOR_ELEMENT_FORMS)},
        "separate_form_exports": True,
        "signatures": {
            "INS": {
                "128" + element + "_" + half: (
                    "5 word", "5 word",
                    f"{ {'E8': 4, 'E16': 3, 'E32': 2, 'E64': 1}[element]} word"
                ) + (() if element == "E64" else (
                    f"{ {'E8': 3, 'E16': 2, 'E32': 1}[element]} word",))
                for element in ARM_VECTOR_ELEMENT_FORMS for half in ("LO", "HI")},
            "INS_GEN": {
                "128" + element: (
                    "5 word", "5 word",
                    f"{ {'E8': 4, 'E16': 3, 'E32': 2, 'E64': 1}[element]} word")
                for element in ARM_VECTOR_ELEMENT_FORMS}},
    },
    "vector-round-halving": {
        "instructions": ("URHADD_VEC",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_WIDENING_FORMS,
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_WIDENING_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + form: ("5 word", "5 word", "5 word")
                for width in (64, 128)
                for form in ARM_VECTOR_WIDENING_FORMS}},
    },
    "vector-compare": {
        "instructions": ("CMGT_VEC", "CMHI_VEC", "CMGE_VEC", "CMLE_VEC_ZERO"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS[:-1], "128": ARM_VECTOR_ELEMENT_FORMS},
        "form_root_suffixes": {form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": {
            instruction: {
                str(width) + element: (
                    ("5 word", "5 word") if instruction == "CMLE_VEC_ZERO"
                    else ("5 word", "5 word", "5 word"))
                for width in (64, 128) for element in ARM_VECTOR_ELEMENT_FORMS
                if width == 128 or element != "E64"}
            for instruction in ("CMGT_VEC", "CMHI_VEC", "CMGE_VEC", "CMLE_VEC_ZERO")},
    },
    "vector-multiply": {
        "instructions": ("MUL_VEC", "MLA_VEC", "MLS_VEC"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": (
            *ARM_VECTOR_WIDENING_FORMS, *ARM_VECTOR_WIDENING_INDEXED_FORMS),
        "form_root_suffixes": {
            form: form for form in
            (*ARM_VECTOR_WIDENING_FORMS, *ARM_VECTOR_WIDENING_INDEXED_FORMS)},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + form: (
                    ("5 word", "5 word", "4 word", "2 word") if form.startswith("E16_")
                    else ("5 word", "5 word", "5 word", "1 word") if form.startswith("E32_")
                    else ("5 word", "5 word", "5 word"))
                for width in (64, 128) for form in
                (*ARM_VECTOR_WIDENING_FORMS, *ARM_VECTOR_WIDENING_INDEXED_FORMS)}},
    },
    "vector-minmax": {
        "instructions": ("SMAX_VEC", "UMAX_VEC", "UMIN_VEC"),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("E8", "E16", "E32"),
        "form_root_suffixes": {form: form for form in ("E8", "E16", "E32")},
        "separate_form_exports": True,
        "signatures": {
            "*": {str(width) + element: ("5 word", "5 word", "5 word")
                  for width in (64, 128) for element in ("E8", "E16", "E32")}},
    },
    "vector-max-reduce": {
        "instructions": ("UMAXV",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("E8", "E16", "E32"),
        "forms_by_width": {
            "64": ("E8", "E16"), "128": ("E8", "E16", "E32")},
        "form_root_suffixes": {form: form for form in ("E8", "E16", "E32")},
        "separate_form_exports": True,
        "signatures": {
            "*": {str(width) + element: ("5 word", "5 word")
                  for width, elements in (
                      (64, ("E8", "E16")), (128, ("E8", "E16", "E32")))
                  for element in elements}},
    },
    "vector-add-long-reduce": {
        "instructions": ("UADDLV",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("E8", "E16", "E32"),
        "forms_by_width": {
            "64": ("E8", "E16"), "128": ("E8", "E16", "E32")},
        "form_root_suffixes": {form: form for form in ("E8", "E16", "E32")},
        "separate_form_exports": True,
        "signatures": {
            "*": {str(width) + element: ("5 word", "5 word")
                  for width, elements in (
                      (64, ("E8", "E16")), (128, ("E8", "E16", "E32")))
                  for element in elements}},
    },
    "vector-pair-add-long": {
        "instructions": ("UADDLP",),
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ("E8", "E16", "E32"),
        "form_root_suffixes": {form: form for form in ("E8", "E16", "E32")},
        "separate_form_exports": True,
        "signatures": {
            "*": {"128" + element: ("5 word", "5 word")
                  for element in ("E8", "E16", "E32")}},
    },
    "vector-pair-add-accumulate-long": {
        "instructions": ("UADALP",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("E8", "E16", "E32"),
        "form_root_suffixes": {form: form for form in ("E8", "E16", "E32")},
        "separate_form_exports": True,
        "signatures": {
            "*": {str(width) + element: ("5 word", "5 word")
                  for width in (64, 128) for element in ("E8", "E16", "E32")}},
    },
    "vector-widen-shift": {
        "instructions": ("USHLL_VEC", "USHLL2_VEC", "SSHLL_VEC", "SSHLL2_VEC"),
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ("E8", "E16", "E32"),
        "form_root_suffixes": {form: form for form in ("E8", "E16", "E32")},
        "separate_form_exports": True,
        "signatures": {
            "*": {"128E" + str(element): (str(bits) + " word", "5 word", "5 word")
                  for element, bits in ((8, 3), (16, 4), (32, 5))}},
    },
    "aes": {
        "instructions": ("AESE", "AESD", "AESMC", "AESIMC"),
        "root_prefix": "ARM_",
        "required_widths": (128,),
        "required_forms": ("q128-effect",),
        "signatures": {"*": {"128": ("5 word", "5 word")}},
    },
    "sha2": {
        "instructions": (
            "SHA256H", "SHA256H2", "SHA256SU0", "SHA256SU1",
            "SHA512H", "SHA512H2", "SHA512SU0", "SHA512SU1"),
        "root_prefix": "ARM_",
        "required_widths": (128,),
        "required_forms": ("q128-effect",),
        "signatures": {
            "*": {"128": ("5 word", "5 word", "5 word")},
            "SHA256SU0": {"128": ("5 word", "5 word")},
            "SHA512SU0": {"128": ("5 word", "5 word")}},
    },
    "vector-abs": {
        "instructions": ("ABS_VEC",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS[:-1], "128": ARM_VECTOR_ELEMENT_FORMS},
        "form_root_suffixes": {form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + element: ("5 word", "5 word")
                for width in (64, 128) for element in ARM_VECTOR_ELEMENT_FORMS
                if width == 128 or element != "E64"}},
    },
    "vector-umov": {
        "instructions": ("UMOV",),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("E32", "E64"),
        "forms_by_width": {"32": ("E32",), "64": ("E64",)},
        "form_root_suffixes": {"E32": "E32", "E64": "E64"},
        "separate_form_exports": True,
        "signatures": {
            "*": {"32E32": ("5 word", "5 word", "2 word"),
                  "64E64": ("5 word", "5 word", "1 word")}},
    },
    "reverse": {
        "instructions": ("REV",),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("full-word-container",),
        "signatures": {
            "*": {str(width): ("5 word", "5 word") for width in (32, 64)}},
    },
    "count": {
        "instructions": ("CLZ",),
        "root_prefix": "arm_",
        "required_widths": (32, 64),
        "required_forms": ("full-word-leading-zero-count",),
        "signatures": {
            "*": {str(width): ("5 word", "5 word") for width in (32, 64)}},
    },
    "vector-count": {
        "instructions": ("CNT",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("byte-lanes",),
        "signatures": {
            "*": {str(width): ("5 word", "5 word") for width in (64, 128)}},
    },
    "vector-reverse": {
        "instructions": ("REV32_VEC", "REV64_VEC"),
        "root_prefix": "arm_",
        "required_widths": (128,),
        "required_forms": ("E8", "E16"),
        "forms_by_instruction": {"REV64_VEC": ("E8", "E16", "E32")},
        "form_root_suffixes": {"E8": "E8", "E16": "E16", "E32": "E32"},
        "separate_form_exports": True,
        "signatures": {
            name: {
                "128E" + str(element_width): ("5 word", "5 word")
                for element_width in ((8, 16) if name == "REV32_VEC" else (8, 16, 32))
            } for name in ("REV32_VEC", "REV64_VEC")},
    },
    "vector-move": {
        "instructions": ("MOVI",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ("predecoded-imm64",),
        "signatures": {
            "*": {str(width): ("5 word", "64 word") for width in (64, 128)}},
    },
    "vector-narrow": {
        "instructions": ("XTN", "XTN2"),
        "root_prefix": "arm_",
        # 64 denotes the computed narrow result, not the Q128 source/state.
        "required_widths": (64,),
        "required_forms": ("E8", "E16", "E32"),
        "form_root_suffixes": {"E8": "E8", "E16": "E16", "E32": "E32"},
        "separate_form_exports": True,
        "signatures": {
            "*": {"64E" + str(element): ("5 word", "5 word")
                  for element in (8, 16, 32)}},
    },
    "vector-duplicate-element": {
        "instructions": ("DUP_ELEM",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_DUPLICATE_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_DUPLICATE_ELEMENT_FORMS[:-2],
            "128": ARM_VECTOR_DUPLICATE_ELEMENT_FORMS,
        },
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_DUPLICATE_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + element + "_" + half:
                ("5 word", "5 word") +
                (() if element == "E64" else
                 (f"{ {'E8': 3, 'E16': 2, 'E32': 1}[element]} word",))
                for width in (64, 128)
                for element in ARM_VECTOR_ELEMENT_FORMS
                if width == 128 or element != "E64"
                for half in ("LO", "HI")
            }},
    },
    "vector-duplicate-element-scalar": {
        "instructions": ("DUP_ELEM_SCALAR",),
        "root_prefix": "arm_",
        "profiles_by_instruction": {
            "DUP_ELEM_SCALAR": tuple(
                {"width": element, "form": half,
                 "suffix": f"_E{element}_{half}",
                 "argument_types": ("5 word", "5 word") + (
                     () if element == 64 else
                     (f"{ {8: 3, 16: 2, 32: 1}[element]} word",))}
                for element in (8, 16, 32, 64) for half in ("LO", "HI")),
        },
    },
    "vector-duplicate-general": {
        "instructions": ("DUP_GEN",),
        "root_prefix": "arm_",
        "required_widths": (64, 128),
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            "64": ARM_VECTOR_ELEMENT_FORMS[:-1],
            "128": ARM_VECTOR_ELEMENT_FORMS,
        },
        "form_root_suffixes": {
            form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + element: ("5 word", "5 word")
                for width in (64, 128)
                for element in ARM_VECTOR_ELEMENT_FORMS
                if width == 128 or element != "E64"
            }},
    },
    "crypto-bitwise": {
        "instructions": ("EOR3", "BCAX", "RAX1", "XAR"),
        "root_prefix": "ARM_",
        "required_widths": (128,),
        "required_forms": ("q128-effect",),
        "signatures": {
            "EOR3": {"128": ("5 word", "5 word", "5 word", "5 word")},
            "BCAX": {"128": ("5 word", "5 word", "5 word", "5 word")},
            "RAX1": {"128": ("5 word", "5 word", "5 word")},
            "XAR": {"128": ("5 word", "5 word", "5 word", "6 word")},
        },
    },
}

for _permutation, _execute in (
    ("uzp", "unzip"), ("zip", "zip"), ("trn", "transpose")
):
    _instructions = (_permutation.upper() + "1", _permutation.upper() + "2")
    _widths = (128,) if _permutation == "uzp" else (64, 128)
    ARM_FAMILIES["vector-" + _permutation] = {
        "instructions": _instructions,
        "root_prefix": "arm_",
        "required_widths": _widths,
        "required_forms": ARM_VECTOR_ELEMENT_FORMS,
        "forms_by_width": {
            str(width): ARM_VECTOR_ELEMENT_FORMS if width == 128 else
            ARM_VECTOR_ELEMENT_FORMS[:-1] for width in _widths},
        "form_root_suffixes": {form: form for form in ARM_VECTOR_ELEMENT_FORMS},
        "separate_form_exports": True,
        "signatures": {
            "*": {
                str(width) + element: ("5 word", "5 word", "5 word")
                for width in _widths
                for element in ARM_VECTOR_ELEMENT_FORMS
                if width == 128 or element != "E64"}},
    }


# Memory profiles describe the decoded forms. Their signatures fix every
# encoded field; the checker separately permits only preceding typed
# source-configuration components. Exact sparse rows avoid inventing W32 SIMD,
# D64/E64 interleaving, or writeback modes not admitted by the HOL decoder.
_ARM_MEMORY_MODES = ("NO", "POSTI", "POSTR")
_ARM_MEMORY_SINGLE_ROWS = (
    *((width, "GPR", form,
       ("5 word", "5 word", "12 word" if form == "UIMM" else "9 word")
       if form in ("POST", "PRE", "UIMM", "UNSCALED")
       else ("5 word", "5 word", "5 word"))
      for width in (32, 64)
      for form in ("POST", "PRE", "UIMM", "REG0", "REGS", "UNSCALED")),
    *((width, "SIMD", form,
       ("5 word", "5 word", "12 word" if form == "UIMM" else "9 word")
       if form in ("POST", "PRE", "UIMM", "UNSCALED")
       else ("5 word", "5 word", "5 word"))
      for width, forms in (
          (64, ("POST", "PRE", "UIMM")),
          (128, ("POST", "PRE", "UIMM", "REG0", "REGS", "UNSCALED")))
      for form in forms),
    *((width, "SIMD", f"LD1_E{element}_{mode}",
       ("5 word", "5 word", "5 word") if mode == "POSTR" else ("5 word", "5 word"))
      for width in (64, 128) for element in (8, 16, 32, 64)
      for mode in _ARM_MEMORY_MODES),
)
_ARM_MEMORY_BYTE_ROWS = tuple(
    row for row in _ARM_MEMORY_SINGLE_ROWS
    if row[0] == 32 and row[1] == "GPR" and row[2] != "REGS")
_ARM_MEMORY_PAIR_ROWS = (
    *((width, view, mode, ("5 word", "5 word", "5 word", "7 word"))
      for width, view in ((32, "GPR"), (64, "GPR"), (64, "SIMD"), (128, "SIMD"))
      for mode in ("POST", "PRE", "OFFSET")),
    *((128, "SIMD", f"LD1_E{element}_{mode}",
       ("5 word", "5 word", "5 word") if mode == "POSTR" else ("5 word", "5 word"))
      for element in (8, 16, 32, 64) for mode in _ARM_MEMORY_MODES),
)
for _family, _instructions, _rows in (
    ("memory-single", ("LDR", "STR", "LDRB", "STRB"),
     {name: _ARM_MEMORY_SINGLE_ROWS for name in ("LDR", "STR")} |
     {name: _ARM_MEMORY_BYTE_ROWS for name in ("LDRB", "STRB")}),
    ("memory-pair", ("LDP", "STP"),
     {name: _ARM_MEMORY_PAIR_ROWS for name in ("LDP", "STP")}),
    ("memory-four", ("LDP4", "STP4"),
     {name: tuple(
         (width, "SIMD", f"LD1_E{element}_{mode}",
          ("5 word", "5 word", "5 word") if mode == "POSTR" else ("5 word", "5 word"))
         for width in (64, 128) for element in (8, 16, 32, 64)
         for mode in _ARM_MEMORY_MODES)
      for name in ("LDP4", "STP4")}),
    ("memory-structure2", ("LD2", "ST2"),
     {name: tuple(
         (width, "SIMD", f"LD2_E{element}_POSTI", ("5 word", "5 word"))
         for width in (64, 128)
         for element in ((8, 16, 32) if width == 64 else (8, 16, 32, 64)))
      for name in ("LD2", "ST2")}),
    ("memory-structure3", ("LD3", "ST3"),
     {name: tuple(
         (width, "SIMD", f"LD3_E{element}_{mode}",
          ("5 word", "5 word", "5 word") if mode == "POSTR" else ("5 word", "5 word"))
         for width in (64, 128)
         for element in ((8, 16, 32) if width == 64 else (8, 16, 32, 64))
         for mode in ("POSTI", "POSTR"))
      for name in ("LD3", "ST3")}),
    ("memory-replicate", ("LD1R",),
     {"LD1R": tuple(
         (width, "SIMD", f"LD1R_E{element}_POSTI", ("5 word", "5 word"))
         for width in (64, 128) for element in (8, 16, 32, 64))}),
):
    ARM_FAMILIES[_family] = {
        "instructions": _instructions,
        "root_prefix": "arm_",
        "safe_domain_proofs": True,
        "encoded_signatures_only": True,
        "profiles_by_instruction": {
            name: tuple({
                "width": width, "form": view + "_" + form,
                "suffix": f"{width}_{view}_{form}", "argument_types": arguments,
            } for width, view, form, arguments in _rows[name])
            for name in _instructions},
    }


_OCAML_RAW_START = re.compile(r"\{([a-z_]*)\|")
_OCAML_CODE_STOP = re.compile(r"""[{("']""")
_OCAML_COMMENT_STOP = re.compile(r"""[{("*']""")
# A character literal such as '"' or '\''. A quote after an identifier
# character is a prime, as in XREG', not the start of a literal.
_OCAML_CHAR = re.compile(r"""'(?:[^\\'\n]|\\(?:[\\'"ntbr ]|[0-9]{3}|x[0-9a-fA-F]{2}|o[0-3][0-7]{2}))'""")
_OCAML_STRING_STOP = re.compile(r'[\\"]')
_NOT_NEWLINE = re.compile(r"[^\n]")


def without_comments(source):
    """Remove OCaml comments, respecting strings and quoted source excerpts."""
    # Copy or blank each run of characters that cannot change the scanner
    # state at once. The result is the same as a character-by-character
    # scan, keeps every offset and newline, and is several times faster on
    # the generated models, whose comments quote whole Sail functions.
    result = []
    depth = 0
    quoted = False
    i = 0
    n = len(source)
    while i < n:
        stop = (_OCAML_STRING_STOP if quoted else
                _OCAML_COMMENT_STOP if depth else _OCAML_CODE_STOP).search(source, i)
        j = stop.start() if stop else n
        if j > i:
            text = source[i:j]
            result.append(_NOT_NEWLINE.sub(" ", text) if depth else text)
            i = j
            if i == n:
                break
        char = source[i]
        if quoted:
            if char == "\\" and i + 1 < n:
                result.append("  " if depth else source[i:i + 2])
                i += 2
                continue
            if char == '"':
                quoted = False
        elif char == "{":
            raw = _OCAML_RAW_START.match(source, i)
            if raw:
                delimiter = "|" + raw.group(1) + "}"
                end = source.find(delimiter, raw.end())
                if end < 0:
                    raise ValueError("unterminated OCaml quoted string")
                end += len(delimiter)
                text = source[i:end]
                result.append(_NOT_NEWLINE.sub(" ", text) if depth else text)
                i = end
                continue
        elif char == "'":
            literal = _OCAML_CHAR.match(source, i)
            if literal and not (i and (source[i - 1].isalnum() or source[i - 1] in "_'")):
                text = literal.group(0)
                result.append(_NOT_NEWLINE.sub(" ", text) if depth else text)
                i = literal.end()
                continue
        elif char == "(" and source.startswith("(*", i):
            depth += 1
            result.append("  ")
            i += 2
            continue
        elif char == "*" and source.startswith("*)", i):
            depth -= 1
            result.append("  ")
            i += 2
            continue
        elif char == '"':
            quoted = True
        result.append(" " if depth else char)
        i += 1
    if depth:
        raise ValueError("unterminated OCaml comment")
    return "".join(result)


def inventory(repo=REPO):
    result = {}
    for arch, prefix, directory in (
        ("aarch64", "arm", "arm"), ("rv32im", "riscv", "riscv")
    ):
        source = repo / directory / "proofs/instruction.ml"
        code = without_comments(source.read_text())
        names = sorted(set(re.findall(
            rf"^(?:let|and)\s+({prefix}_[A-Z][A-Za-z0-9_]*)\s*=\s*"
            r"(?:define|new_definition)\b", code, flags=re.MULTILINE)))
        if not names:
            raise ValueError(f"no instruction definitions found in {source}")
        result[arch] = {"instructions": [{"hol": name} for name in names]}
    return result


# The name of an instruction theorem report.
THEOREM_LABEL = r"SAIL_HL_(?:RV32|ARM|X86)_[A-Za-z0-9_]+_(?:EQ|DIFF|EXACT)"


def normalized_proof_output(lines):
    """Drivers print NAME then "|- ...", or "NAME: |- ..." on one line.
    Split the second form; progress messages are left alone."""
    normalized = []
    for line in lines:
        inline = re.fullmatch("(" + THEOREM_LABEL + r"): (.*)", line)
        normalized.extend(inline.groups() if inline else (line,))
    return normalized


def theorem_statements(lines, names):
    """The printed statement of each named theorem in proof output: the
    "|- " line after its name and the indented lines that continue it."""
    lines = normalized_proof_output(lines)
    statements = {}
    for index, line in enumerate(lines):
        if line in names and index + 1 < len(lines):
            end = index + 2
            while end < len(lines) and lines[end][:1] in (" ", "\t"):
                end += 1
            statements[line] = "\n".join(lines[index + 1:end])
    return statements


def audit_proof_output(lines, expected_theorems, completion, context):
    """Check reported proof output: every expected theorem exactly once,
    printed closed, and the completion marker once.

    The caller must also require a successful native process and unchanged
    inputs, and compare the printed statements with the checked-in ones.
    HOL's kernel establishes the claims; this check rejects missing,
    duplicate or open theorem reports.
    """
    label = THEOREM_LABEL
    lines = normalized_proof_output(lines)
    counts = Counter(lines)
    if counts[completion] != 1:
        raise ValueError(f"{context}: missing or duplicate proof completion marker")
    expected = set(expected_theorems)
    actual = {
        line for line in lines
        if re.fullmatch(label, line)}
    if actual != expected:
        raise ValueError(
            f"{context}: instruction theorem inventory differs; "
            f"missing {sorted(expected - actual)}, unexpected {sorted(actual - expected)}")
    for theorem in expected:
        if counts[theorem] != 1:
            raise ValueError(f"{context}: duplicate instruction theorem: {theorem}")
        index = lines.index(theorem) + 1
        if index >= len(lines) or not lines[index].startswith("|- "):
            raise ValueError(f"{context}: instruction theorem is not printed closed: {theorem}")


def arm_instruction_forms(family, instruction, width=None):
    specification = ARM_FAMILIES[family]
    explicit = specification.get("profiles_by_instruction")
    if explicit is not None:
        if instruction not in explicit:
            raise ValueError("public instruction is required for an explicit profile")
        return tuple(dict.fromkeys(
            row["form"] for row in explicit[instruction]
            if width is None or row["width"] == width))
    if width is not None and "forms_by_width" in specification:
        return specification["forms_by_width"].get(
            str(width), arm_instruction_forms(family, instruction))
    return specification.get("forms_by_instruction", {}).get(
        instruction, specification["required_forms"])


def arm_instruction_variants(family, instruction):
    """Export/theorem names and checked signatures for one public definition."""
    specification = ARM_FAMILIES[family]
    explicit = specification.get("profiles_by_instruction")
    if explicit is not None:
        if instruction not in explicit:
            raise ValueError("public instruction is required for an explicit profile")
        exported = specification.get("export_names", {}).get(instruction, instruction)
        return [
            dict(row, argument_types=list(row["argument_types"]),
                 root=specification["root_prefix"] + exported + row["suffix"],
                 constant="sail_hl_" + (
                     specification["root_prefix"] + exported +
                     row["suffix"]).replace("_", "_5f"),
                 theorem=f"SAIL_HL_ARM_{exported}{row['suffix']}_EQ")
            for row in explicit[instruction]]
    signatures = specification.get("signatures", {})
    signature = signatures.get(instruction, signatures.get("*", {}))
    variants = []
    for width in specification["required_widths"]:
        forms = arm_instruction_forms(family, instruction, width) if (
            specification.get("separate_form_exports")
        ) else (None,)
        for form in forms:
            form_suffix = specification.get("form_root_suffixes", {}).get(
                form, "_" + form if form is not None else "")
            suffix = str(width) + form_suffix
            root = specification["root_prefix"] + instruction + suffix
            variant = {
                "width": width, "form": form, "suffix": suffix, "root": root,
                "constant": "sail_hl_" + root.replace("_", "_5f"),
                "theorem": f"SAIL_HL_ARM_{instruction}{suffix}_EQ",
            }
            variant["argument_types"] = list(signature[suffix])
            variants.append(variant)
    return variants


def arm_success_marker(family):
    return "SAIL_HOL_LIGHT_ARM_" + family.replace("-", "_").upper() + "_PROOFS_OK"


