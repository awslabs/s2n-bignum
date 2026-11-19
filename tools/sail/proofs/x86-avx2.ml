(* AVX2 data movement, shuffles, blends, inserts, extracts, mask extracts
   and carry-less multiplication: register forms of VEX-encoded
   instructions (and of the legacy-encoded PMOVMSKB) under the documented
   supplied-byte and LongMode boundary. Each theorem compares complete states: the
   destination, zeroing above the written width, and the rest of the state.
   Instruction fetch and feature checks are not compared. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;
needs "tools/sail/proofs/x86-avx2-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_avx2_standard_new_definition = new_definition;;
(* Declare the generated bodies with fresh-model.ml's new_definition, as
   x86-vector.ml does. *)
module Sail_hl_x86_avx2_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-avx2.ml";;
end;;
open Sail_hl_x86_avx2_model;;
let new_definition = sail_hl_avx2_standard_new_definition;;

(* Extra definitions for general-register operands and masked blends. *)
let SAIL_HL_X86_AVX2_DEFINITIONS =
  [GPR32_Z; GPR64; msimd2; msimd4; msimd8; msimd16];;

(* Rewrites before, and a tactic after, the shared vector tactic, by root
   prefix. *)
let SAIL_HL_X86_AVX2_EXTRA = [
  "X86_VPCMPEQW", ([SAIL_HL_X86_EQUAL16], REWRITE_TAC[EQ_SYM_EQ]);
  "X86_VPSHUFB", ([], SAIL_HL_X86_AVX2_PSHUFB_TAC);
  "X86_VPBROADCAST", ([], SAIL_HL_X86_AVX2_DUPLICATE_TAC);
  "X86_VMOVSLDUP", ([], SAIL_HL_X86_AVX2_DUPLICATE_TAC);
  "X86_VMOVSHDUP", ([], SAIL_HL_X86_AVX2_DUPLICATE_TAC);
  "X86_VMOVD", ([], SAIL_HL_X86_AVX2_ZEROTOP_TAC);
  "X86_VPEXTRW", ([SAIL_HL_X86_AVX2_VAL_SUBWORD3], SAIL_HL_X86_AVX2_ZEROTOP_TAC);
  "X86_VPINSRW", ([SAIL_HL_X86_AVX2_VAL_SUBWORD3],
    SAIL_HL_X86_AVX2_ZEROTOP_TAC THEN SAIL_HL_X86_AVX2_INSERT_TAC);
  "X86_VPINSRD", ([], SAIL_HL_X86_AVX2_ZEROTOP_TAC THEN
                      SAIL_HL_X86_AVX2_PINSRD_TAC);
  "X86_VPERMD", ([], SAIL_HL_X86_AVX2_PERMD_TAC);
  "X86_VPBLENDD", ([], SAIL_HL_X86_AVX2_BLEND_TAC);
  "X86_VPBLENDW", ([], SAIL_HL_X86_AVX2_BLEND_TAC);
  "X86_VINSERTI128", (SAIL_HL_X86_AVX2_LANE_REWRITES, SAIL_HL_X86_AVX2_LANE_TAC);
  "X86_VEXTRACTI128", (SAIL_HL_X86_AVX2_LANE_REWRITES, SAIL_HL_X86_AVX2_LANE_TAC);
  (* VPINSRQ: the immediate's low bit chooses the quadword. *)
  "X86_VPINSRQ", (SAIL_HL_X86_AVX2_LANE_REWRITES,
    SAIL_HL_X86_AVX2_LANE_TAC THEN
    REWRITE_TAC[VAL_WORD_0; VAL_WORD_1; INT_OF_NUM_EQ; ARITH]);
  "X86_VPERM2I128", ([SAIL_HL_X86_AVX2_FLAG_MASK;
                      SAIL_HL_X86_AVX2_PERM2_NIBBLE_FACTS;
                      INT_OF_NUM_EQ; EQ_SYM_EQ],
    REPEAT CONJ_TAC THEN SAIL_HL_X86_AVX2_PERM2_BIT_TAC);
  "X86_VPBLENDVB", ([], SAIL_HL_X86_AVX2_BLENDV_TAC);
  "X86_VPCLMULQDQ", (SAIL_HL_X86_AVX2_PMUL_CHAINS,
    REWRITE_TAC[SAIL_HL_X86_AVX2_QWORD_BLEND]);
  "X86_VMOVMSKPS", ([],
    REWRITE_TAC(SAIL_HL_X86_AVX2_BYTE_SUM_BITS @
                [SAIL_HL_X86_AVX2_BIT0_BITVAL]) THEN
    SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8; ARITH]);
  "X86_VPMOVMSKB", ([],
    REWRITE_TAC[SAIL_HL_X86_AVX2_BIT0_BITVAL] THEN
    SIMP_TAC[SAIL_HL_X86_AVX2_NSUM_BIT; BIT_TRIVIAL; DIMINDEX_32; ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV);
  "X86_PMOVMSKB", ([],
    REWRITE_TAC[SAIL_HL_X86_AVX2_BIT0_BITVAL; BIT_LSB_WORD; ODD; ARITH] THEN
    TRY(CONV_TAC TAUT));
];;

(* The statement of one form: the generated root applied to its fields is
   s2n-bignum's relation applied to the operand components. A vector
   operand is the SIMD component of its register at its width, a general
   register operand is the 32- or 64-bit view with the architectural
   upper-half clearing, and an immediate is a read-only value. *)
let SAIL_HL_X86_AVX2_CLAIM
    (root, source, instruction, target, parameters, operands) =
  let component (kind, width, argument) =
    match kind with
    | "X" -> Printf.sprintf
        "(SIMD%d (Simdreg (word_zx %s:5 word) Lower_%d))" width argument width
    | "G" when width = 32 ->
        Printf.sprintf "(GPR32_Z (Gpr %s Lower_32))" argument
    | "G" -> Printf.sprintf "(GPR64 (Gpr %s Full_64))" argument
    | _ -> Printf.sprintf "(rvalue %s)" argument in
  let quantified = String.concat ""
    (map (fun (name, bits) -> Printf.sprintf "!%s:%d word. " name bits)
         parameters) in
  let statement = parse_term
    (quantified ^ "!s t:x86state. " ^ fst(dest_const(fst(strip_comb
       (lhand(snd(strip_forall(concl source))))))) ^ " " ^
     String.concat " " (map fst parameters) ^ " s t <=> x86_" ^
     instruction ^ " " ^ String.concat " " (map component operands) ^
     " s t") in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  let started = Sys.time() in
  print_endline("Starting complete-state proof: " ^ name);
  let extra =
    match filter (fun (prefix, _) ->
            String.length root >= String.length prefix &&
            String.sub root 0 (String.length prefix) = prefix)
          SAIL_HL_X86_AVX2_EXTRA with
    | (_, entry) :: _ -> entry
    | [] -> ([], ALL_TAC) in
  let rewrites, extra = extra in
  let theorem = prove(statement,
    SAIL_HL_X86_VECTOR_TAC_WITH
      ([COMPONENT_COMPOSE_ASSOC; READ_ZEROTOP_32; WRITE_ZEROTOP_32] @
       rewrites)
      (source :: target :: SAIL_HL_X86_AVX2_DEFINITIONS) THEN
    extra) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name, theorem;;

let SAIL_HL_X86_AVX2_CLAIMS = map SAIL_HL_X86_AVX2_CLAIM [
  "X86_VPCMPEQW128_RRR",sail_hl_X86_5fVPCMPEQW128_5fRRR,"VPCMPEQW",x86_VPCMPEQW,["d",4;"n",4;"m",4],["X",128,"d";"X",128,"n";"X",128,"m"];
  "X86_VPCMPEQW256_RRR",sail_hl_X86_5fVPCMPEQW256_5fRRR,"VPCMPEQW",x86_VPCMPEQW,["d",4;"n",4;"m",4],["X",256,"d";"X",256,"n";"X",256,"m"];
  "X86_VPSHUFD128_RRI",sail_hl_X86_5fVPSHUFD128_5fRRI,"VPSHUFD",x86_VPSHUFD,["d",4;"m",4;"imm",8],["X",128,"d";"X",128,"m";"I",0,"imm"];
  "X86_VPSHUFD256_RRI",sail_hl_X86_5fVPSHUFD256_5fRRI,"VPSHUFD",x86_VPSHUFD,["d",4;"m",4;"imm",8],["X",256,"d";"X",256,"m";"I",0,"imm"];
  "X86_VPSHUFB128_RRR",sail_hl_X86_5fVPSHUFB128_5fRRR,"VPSHUFB",x86_VPSHUFB,["d",4;"n",4;"m",4],["X",128,"d";"X",128,"n";"X",128,"m"];
  "X86_VPUNPCKLQDQ128_RRR",sail_hl_X86_5fVPUNPCKLQDQ128_5fRRR,"VPUNPCKLQDQ",x86_VPUNPCKLQDQ,["d",4;"n",4;"m",4],["X",128,"d";"X",128,"n";"X",128,"m"];
  "X86_VPUNPCKHQDQ128_RRR",sail_hl_X86_5fVPUNPCKHQDQ128_5fRRR,"VPUNPCKHQDQ",x86_VPUNPCKHQDQ,["d",4;"n",4;"m",4],["X",128,"d";"X",128,"n";"X",128,"m"];
  "X86_VPBROADCASTD128_RR",sail_hl_X86_5fVPBROADCASTD128_5fRR,"VPBROADCASTD",x86_VPBROADCASTD,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VPBROADCASTQ128_RR",sail_hl_X86_5fVPBROADCASTQ128_5fRR,"VPBROADCASTQ",x86_VPBROADCASTQ,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VPBROADCASTW128_RR",sail_hl_X86_5fVPBROADCASTW128_5fRR,"VPBROADCASTW",x86_VPBROADCASTW,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VPBLENDD128_RRRI",sail_hl_X86_5fVPBLENDD128_5fRRRI,"VPBLENDD",x86_VPBLENDD,["d",4;"n",4;"m",4;"imm",8],["X",128,"d";"X",128,"n";"X",128,"m";"I",0,"imm"];
  "X86_VPBLENDW128_RRRI",sail_hl_X86_5fVPBLENDW128_5fRRRI,"VPBLENDW",x86_VPBLENDW,["d",4;"n",4;"m",4;"imm",8],["X",128,"d";"X",128,"n";"X",128,"m";"I",0,"imm"];
  "X86_VMOVSLDUP128_RR",sail_hl_X86_5fVMOVSLDUP128_5fRR,"VMOVSLDUP",x86_VMOVSLDUP,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VMOVSHDUP128_RR",sail_hl_X86_5fVMOVSHDUP128_5fRR,"VMOVSHDUP",x86_VMOVSHDUP,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VMOVDQA128_RR",sail_hl_X86_5fVMOVDQA128_5fRR,"VMOVDQA",x86_VMOVDQA,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VMOVDQA128_STORE_RR",sail_hl_X86_5fVMOVDQA128_5fSTORE_5fRR,"VMOVDQA",x86_VMOVDQA,["m",4;"x",4],["X",128,"m";"X",128,"x"];
  "X86_VMOVDQU128_RR",sail_hl_X86_5fVMOVDQU128_5fRR,"VMOVDQU",x86_VMOVDQU,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VMOVDQU128_STORE_RR",sail_hl_X86_5fVMOVDQU128_5fSTORE_5fRR,"VMOVDQU",x86_VMOVDQU,["m",4;"x",4],["X",128,"m";"X",128,"x"];
  "X86_VPSHUFB256_RRR",sail_hl_X86_5fVPSHUFB256_5fRRR,"VPSHUFB",x86_VPSHUFB,["d",4;"n",4;"m",4],["X",256,"d";"X",256,"n";"X",256,"m"];
  "X86_VPUNPCKLQDQ256_RRR",sail_hl_X86_5fVPUNPCKLQDQ256_5fRRR,"VPUNPCKLQDQ",x86_VPUNPCKLQDQ,["d",4;"n",4;"m",4],["X",256,"d";"X",256,"n";"X",256,"m"];
  "X86_VPUNPCKHQDQ256_RRR",sail_hl_X86_5fVPUNPCKHQDQ256_5fRRR,"VPUNPCKHQDQ",x86_VPUNPCKHQDQ,["d",4;"n",4;"m",4],["X",256,"d";"X",256,"n";"X",256,"m"];
  "X86_VPBROADCASTD256_RR",sail_hl_X86_5fVPBROADCASTD256_5fRR,"VPBROADCASTD",x86_VPBROADCASTD,["d",4;"m",4],["X",256,"d";"X",128,"m"];
  "X86_VPBROADCASTQ256_RR",sail_hl_X86_5fVPBROADCASTQ256_5fRR,"VPBROADCASTQ",x86_VPBROADCASTQ,["d",4;"m",4],["X",256,"d";"X",128,"m"];
  "X86_VPBROADCASTW256_RR",sail_hl_X86_5fVPBROADCASTW256_5fRR,"VPBROADCASTW",x86_VPBROADCASTW,["d",4;"m",4],["X",256,"d";"X",128,"m"];
  "X86_VPBLENDD256_RRRI",sail_hl_X86_5fVPBLENDD256_5fRRRI,"VPBLENDD",x86_VPBLENDD,["d",4;"n",4;"m",4;"imm",8],["X",256,"d";"X",256,"n";"X",256,"m";"I",0,"imm"];
  "X86_VPBLENDW256_RRRI",sail_hl_X86_5fVPBLENDW256_5fRRRI,"VPBLENDW",x86_VPBLENDW,["d",4;"n",4;"m",4;"imm",8],["X",256,"d";"X",256,"n";"X",256,"m";"I",0,"imm"];
  "X86_VMOVSLDUP256_RR",sail_hl_X86_5fVMOVSLDUP256_5fRR,"VMOVSLDUP",x86_VMOVSLDUP,["d",4;"m",4],["X",256,"d";"X",256,"m"];
  "X86_VMOVSHDUP256_RR",sail_hl_X86_5fVMOVSHDUP256_5fRR,"VMOVSHDUP",x86_VMOVSHDUP,["d",4;"m",4],["X",256,"d";"X",256,"m"];
  "X86_VMOVDQA256_RR",sail_hl_X86_5fVMOVDQA256_5fRR,"VMOVDQA",x86_VMOVDQA,["d",4;"m",4],["X",256,"d";"X",256,"m"];
  "X86_VMOVDQA256_STORE_RR",sail_hl_X86_5fVMOVDQA256_5fSTORE_5fRR,"VMOVDQA",x86_VMOVDQA,["m",4;"x",4],["X",256,"m";"X",256,"x"];
  "X86_VMOVDQU256_RR",sail_hl_X86_5fVMOVDQU256_5fRR,"VMOVDQU",x86_VMOVDQU,["d",4;"m",4],["X",256,"d";"X",256,"m"];
  "X86_VMOVDQU256_STORE_RR",sail_hl_X86_5fVMOVDQU256_5fSTORE_5fRR,"VMOVDQU",x86_VMOVDQU,["m",4;"x",4],["X",256,"m";"X",256,"x"];
  "X86_VPERMQ256_RRI",sail_hl_X86_5fVPERMQ256_5fRRI,"VPERMQ",x86_VPERMQ,["d",4;"m",4;"imm",8],["X",256,"d";"X",256,"m";"I",0,"imm"];
  "X86_VPERMD256_RRR",sail_hl_X86_5fVPERMD256_5fRRR,"VPERMD",x86_VPERMD,["d",4;"n",4;"m",4],["X",256,"d";"X",256,"n";"X",256,"m"];
  "X86_VINSERTI128256_RRRI",sail_hl_X86_5fVINSERTI128256_5fRRRI,"VINSERTI128",x86_VINSERTI128,["d",4;"n",4;"m",4;"imm",8],["X",256,"d";"X",256,"n";"X",128,"m";"I",0,"imm"];
  "X86_VEXTRACTI128256_RRI",sail_hl_X86_5fVEXTRACTI128256_5fRRI,"VEXTRACTI128",x86_VEXTRACTI128,["m",4;"x",4;"imm",8],["X",128,"m";"X",256,"x";"I",0,"imm"];
  "X86_VMOVQ128_F3_RR",sail_hl_X86_5fVMOVQ128_5fF3_5fRR,"VMOVQ",x86_VMOVQ,["d",4;"m",4],["X",128,"d";"X",128,"m"];
  "X86_VMOVQ128_D6_RR",sail_hl_X86_5fVMOVQ128_5fD6_5fRR,"VMOVQ",x86_VMOVQ,["m",4;"x",4],["X",128,"m";"X",128,"x"];
  "X86_VMOVD128_RR",sail_hl_X86_5fVMOVD128_5fRR,"VMOVD",x86_VMOVD,["d",4;"m",4],["X",128,"d";"G",32,"m"];
  "X86_VMOVD128_STORE_RR",sail_hl_X86_5fVMOVD128_5fSTORE_5fRR,"VMOVD",x86_VMOVD,["m",4;"x",4],["G",32,"m";"X",128,"x"];
  "X86_VMOVQ128_RR",sail_hl_X86_5fVMOVQ128_5fRR,"VMOVQ",x86_VMOVQ,["d",4;"m",4],["X",128,"d";"G",64,"m"];
  "X86_VMOVQ128_STORE_RR",sail_hl_X86_5fVMOVQ128_5fSTORE_5fRR,"VMOVQ",x86_VMOVQ,["m",4;"x",4],["G",64,"m";"X",128,"x"];
  "X86_VPEXTRW128_RRI",sail_hl_X86_5fVPEXTRW128_5fRRI,"VPEXTRW",x86_VPEXTRW,["d",4;"m",4;"imm",8],["G",32,"d";"X",128,"m";"I",0,"imm"];
  "X86_VPINSRW128_RRRI",sail_hl_X86_5fVPINSRW128_5fRRRI,"VPINSRW",x86_VPINSRW,["d",4;"n",4;"m",4;"imm",8],["X",128,"d";"X",128,"n";"G",32,"m";"I",0,"imm"];
  "X86_VPINSRD128_RRRI",sail_hl_X86_5fVPINSRD128_5fRRRI,"VPINSRD",x86_VPINSRD,["d",4;"n",4;"m",4;"imm",8],["X",128,"d";"X",128,"n";"G",32,"m";"I",0,"imm"];
  "X86_VPINSRQ128_RRRI",sail_hl_X86_5fVPINSRQ128_5fRRRI,"VPINSRQ",x86_VPINSRQ,["d",4;"n",4;"m",4;"imm",8],["X",128,"d";"X",128,"n";"G",64,"m";"I",0,"imm"];
  "X86_VPERM2I128256_RRRI",sail_hl_X86_5fVPERM2I128256_5fRRRI,"VPERM2I128",x86_VPERM2I128,["d",4;"n",4;"m",4;"imm",8],["X",256,"d";"X",256,"n";"X",256,"m";"I",0,"imm"];
  "X86_VPBLENDVB128_RRRR",sail_hl_X86_5fVPBLENDVB128_5fRRRR,"VPBLENDVB",x86_VPBLENDVB,["d",4;"n",4;"m",4;"k",4],["X",128,"d";"X",128,"n";"X",128,"m";"X",128,"k"];
  "X86_VPBLENDVB256_RRRR",sail_hl_X86_5fVPBLENDVB256_5fRRRR,"VPBLENDVB",x86_VPBLENDVB,["d",4;"n",4;"m",4;"k",4],["X",256,"d";"X",256,"n";"X",256,"m";"X",256,"k"];
  "X86_VPCLMULQDQ128_RRRI",sail_hl_X86_5fVPCLMULQDQ128_5fRRRI,"VPCLMULQDQ",x86_VPCLMULQDQ,["d",4;"n",4;"m",4;"imm",8],["X",128,"d";"X",128,"n";"X",128,"m";"I",0,"imm"];
  "X86_VPCLMULQDQ256_RRRI",sail_hl_X86_5fVPCLMULQDQ256_5fRRRI,"VPCLMULQDQ",x86_VPCLMULQDQ,["d",4;"n",4;"m",4;"imm",8],["X",256,"d";"X",256,"n";"X",256,"m";"I",0,"imm"];
  "X86_VMOVMSKPS256_RR",sail_hl_X86_5fVMOVMSKPS256_5fRR,"VMOVMSKPS",x86_VMOVMSKPS,["d",4;"m",4],["G",32,"d";"X",256,"m"];
  "X86_VPMOVMSKB256_RR",sail_hl_X86_5fVPMOVMSKB256_5fRR,"VPMOVMSKB",x86_VPMOVMSKB,["d",4;"m",4],["G",32,"d";"X",256,"m"];
  "X86_PMOVMSKB32_RR",sail_hl_X86_5fPMOVMSKB32_5fRR,"PMOVMSKB",x86_PMOVMSKB,["d",4;"m",4],["G",32,"d";"X",128,"m"];
  "X86_PMOVMSKB64_RR",sail_hl_X86_5fPMOVMSKB64_5fRR,"PMOVMSKB",x86_PMOVMSKB,["d",4;"m",4],["G",64,"d";"X",128,"m"];
];;
if (length SAIL_HL_X86_AVX2_CLAIMS <> 55 ||
   length(setify(map fst SAIL_HL_X86_AVX2_CLAIMS)) <> 55) then
  failwith "avx2 claim count or duplicate";;
List.iter sail_hl_report SAIL_HL_X86_AVX2_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_AVX2_PROOFS_OK";;
