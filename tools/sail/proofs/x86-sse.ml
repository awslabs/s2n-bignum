(* Legacy-encoded SSE integer instructions, VPEXTRD, VPEXTRQ and
   VZEROUPPER: register forms under the documented supplied-byte and
   LongMode boundary. Each theorem compares complete states.

   A legacy SSE instruction assigns the low 128 bits of a vector register
   and keeps bits 128 to 511, so its statement uses s2n-bignum's
   SIMD128_SSE; the VEX instruction VPEXTRD writes a general register and
   reads SIMD128. Instruction fetch, the SSE and AES-NI availability
   checks of check_legacy_simd and the VEX feature checks are not
   compared. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;
needs "tools/sail/proofs/x86-avx2-lemmas.ml";;
needs "tools/sail/proofs/x86-sse-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_sse_standard_new_definition = new_definition;;
(* Declare the generated bodies with fresh-model.ml's new_definition, as
   x86-vector.ml does. *)
module Sail_hl_x86_sse_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-sse.ml";;
end;;
open Sail_hl_x86_sse_model;;
let new_definition = sail_hl_sse_standard_new_definition;;

(* Extra definitions for general-register operands. *)
let SAIL_HL_X86_SSE_DEFINITIONS =
  [GPR32_Z; GPR64; SIMD128_SSE; msimd2; msimd4; msimd8; msimd16];;

(* Rewrites before, and a tactic after, the shared vector tactic, by root
   prefix. *)
(* VPEXTRD and VPEXTRQ read the low 128 bits of the 512-bit register as
   the lane that imm8 selects (modulo 4, or its bit 0). Fix the selector,
   then every bit position is a numeral; the low 128 bits of the
   register are the zero-extended view that SIMD128 reads. *)
let SAIL_HL_X86_SSE_EXTRACT_FINISH_TAC =
  REWRITE_TAC[SIMD128; COMPONENT_COMPOSE_ASSOC; READ_ZEROTOP_128;
              READ_ZEROTOP_256; BIT_WORD_ZX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH];;

let SAIL_HL_X86_SSE_DEXTRACT_TAC =
  REWRITE_TAC[SAIL_HL_X86_AVX2_VAL_SUBWORD2] THEN
  MP_TAC(ARITH_RULE `val(imm:8 word) MOD 4 < 4`) THEN
  SPEC_TAC(`val(imm:8 word) MOD 4`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  SAIL_HL_X86_SSE_EXTRACT_FINISH_TAC;;

let SAIL_HL_X86_SSE_QEXTRACT_TAC =
  REWRITE_TAC[SAIL_HL_X86_AVX2_SELECT_BIT] THEN
  BOOL_CASES_TAC `bit 0 (imm:8 word)` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  SAIL_HL_X86_SSE_EXTRACT_FINISH_TAC;;

let SAIL_HL_X86_SSE_EXTRA = [
  "X86_PCLMULQDQ", (SAIL_HL_X86_AVX2_PMUL_CHAINS,
    REWRITE_TAC[SAIL_HL_X86_AVX2_QWORD_BLEND]);
  "X86_PSHUFB", ([], SAIL_HL_X86_AVX2_PSHUFB_TAC);
  "X86_PBLENDW", ([], SAIL_HL_X86_AVX2_BLEND_TAC);
  "X86_PINSRD", ([], SAIL_HL_X86_AVX2_ZEROTOP_TAC THEN
                     SAIL_HL_X86_AVX2_PINSRD_TAC);
  (* PINSRQ: the immediate's low bit chooses the quadword, as for VPINSRQ. *)
  "X86_PINSRQ", (SAIL_HL_X86_AVX2_LANE_REWRITES,
    SAIL_HL_X86_AVX2_LANE_TAC THEN
    REWRITE_TAC[VAL_WORD_0; VAL_WORD_1; INT_OF_NUM_EQ; ARITH]);
  "X86_VPEXTRD", ([], SAIL_HL_X86_SSE_DEXTRACT_TAC);
  "X86_VPEXTRQ", ([], SAIL_HL_X86_SSE_QEXTRACT_TAC);
];;

let SAIL_HL_X86_SSE_CLAIM
    (root, source, instruction, target, parameters, operands) =
  let statement = SAIL_HL_X86_SSE_STATEMENT
    (root, source, instruction, target, parameters, operands) in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  let started = Sys.time() in
  print_endline("Starting complete-state proof: " ^ name);
  let extra =
    match filter (fun (prefix, _) ->
            String.length root >= String.length prefix &&
            String.sub root 0 (String.length prefix) = prefix)
          SAIL_HL_X86_SSE_EXTRA with
    | (_, entry) :: _ -> entry
    | [] -> ([], ALL_TAC) in
  let rewrites, extra = extra in
  let theorem = prove(statement,
    SAIL_HL_X86_VECTOR_TAC_WITH
      ([COMPONENT_COMPOSE_ASSOC; READ_ZEROTOP_32; WRITE_ZEROTOP_32] @
       SAIL_HL_X86_SSE_REWRITES @ rewrites)
      (source :: target :: SAIL_HL_X86_SSE_DEFINITIONS) THEN
    extra) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name, theorem;;

(* VZEROUPPER clears bits 128 to 511 of ZMM0 to ZMM15 (`ZMM[i][511..128] =
   zeros()`); s2n-bignum writes each YMMi, whose zerotop_256 write clears
   bits 256 to 511, with the zero-extended low 128 bits. The two writes
   of one register agree bit by bit; the rest is the order of the sixteen
   writes, which is the same. *)
let SAIL_HL_X86_VZEROUPPER_LANE = prove
 (`!x:512 word.
    word_insert x (128,384) (word 0:384 word) =
    word_zx (word_zx (word_subword (word_zx x:256 word) (0,128):128 word):256 word):512 word`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_ZX; BIT_WORD_SUBWORD;
              BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_CASES_TAC `i < 128` THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> i < 256`;
               ARITH_RULE `i < 128 ==> ~(128 <= i)`;
               ARITH_RULE `~(i < 128) ==> 128 <= i`]);;

let SAIL_HL_X86_VZEROUPPER_CLAIM () =
  let name = "SAIL_HL_X86_VZEROUPPER_EQ" in
  let started = Sys.time() in
  print_endline("Starting complete-state proof: " ^ name);
  let theorem = prove
   (`!s t:x86state. sail_hl_X86_5fVZEROUPPER s t <=> x86_VZEROUPPER s t`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC([sail_hl_X86_5fVZEROUPPER; x86_VZEROUPPER; assign; SEQ;
                 ASSIGNS_THM; LET_DEF; LET_END_DEF; FST; SND; SEQ_ID;
                 ASSIGNS_SEQ; COMPONENT_COMPOSE_ASSOC; WRITE_ZEROTOP_256;
                 READ_ZEROTOP_256] @
                [YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8; YMM9;
                 YMM10; YMM11; YMM12; YMM13; YMM14; YMM15] @
                [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
                 ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15]) THEN
    REWRITE_TAC[GSYM WORD_IWORD; NUM_OF_INT_OF_NUM; WORD_VAL] THEN
    CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[SAIL_HL_X86_VZEROUPPER_LANE]) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name, theorem;;

let SAIL_HL_X86_SSE_CLAIMS = [
  "X86_PCLMULQDQ128_RRI",sail_hl_X86_5fPCLMULQDQ128_5fRRI,"PCLMULQDQ",x86_PCLMULQDQ,["d",4;"m",4;"imm",8],["S",128,"d";"S",128,"m";"I",0,"imm"];
  "X86_PSLLDQ128_RI",sail_hl_X86_5fPSLLDQ128_5fRI,"PSLLDQ",x86_PSLLDQ,["d",4;"imm",8],["S",128,"d";"I",0,"imm"];
  "X86_PSRLDQ128_RI",sail_hl_X86_5fPSRLDQ128_5fRI,"PSRLDQ",x86_PSRLDQ,["d",4;"imm",8],["S",128,"d";"I",0,"imm"];
  "X86_PADDD128_RR",sail_hl_X86_5fPADDD128_5fRR,"PADDD",x86_PADDD,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_PADDQ128_RR",sail_hl_X86_5fPADDQ128_5fRR,"PADDQ",x86_PADDQ,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_PAND128_RR",sail_hl_X86_5fPAND128_5fRR,"PAND",x86_PAND,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_PXOR128_RR",sail_hl_X86_5fPXOR128_5fRR,"PXOR",x86_PXOR,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_PCMPGTW128_RR",sail_hl_X86_5fPCMPGTW128_5fRR,"PCMPGTW",x86_PCMPGTW,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_PCMPGTD128_RR",sail_hl_X86_5fPCMPGTD128_5fRR,"PCMPGTD",x86_PCMPGTD,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_PSHUFB128_RR",sail_hl_X86_5fPSHUFB128_5fRR,"PSHUFB",x86_PSHUFB,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_PSHUFD128_RRI",sail_hl_X86_5fPSHUFD128_5fRRI,"PSHUFD",x86_PSHUFD,["d",4;"m",4;"imm",8],["S",128,"d";"S",128,"m";"I",0,"imm"];
  "X86_PBLENDW128_RRI",sail_hl_X86_5fPBLENDW128_5fRRI,"PBLENDW",x86_PBLENDW,["d",4;"m",4;"imm",8],["S",128,"d";"S",128,"m";"I",0,"imm"];
  "X86_PINSRD128_RRI",sail_hl_X86_5fPINSRD128_5fRRI,"PINSRD",x86_PINSRD,["d",4;"m",4;"imm",8],["S",128,"d";"G",32,"m";"I",0,"imm"];
  "X86_PINSRQ128_RRI",sail_hl_X86_5fPINSRQ128_5fRRI,"PINSRQ",x86_PINSRQ,["d",4;"m",4;"imm",8],["S",128,"d";"G",64,"m";"I",0,"imm"];
  "X86_PSRLW128_RI",sail_hl_X86_5fPSRLW128_5fRI,"PSRLW",x86_PSRLW,["d",4;"imm",8],["S",128,"d";"I",0,"imm"];
  "X86_PSRAD128_RI",sail_hl_X86_5fPSRAD128_5fRI,"PSRAD",x86_PSRAD,["d",4;"imm",8],["S",128,"d";"I",0,"imm"];
  "X86_MOVAPS128_RR",sail_hl_X86_5fMOVAPS128_5fRR,"MOVAPS",x86_MOVAPS,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_MOVAPS128_STORE_RR",sail_hl_X86_5fMOVAPS128_5fSTORE_5fRR,"MOVAPS",x86_MOVAPS,["m",4;"x",4],["S",128,"m";"S",128,"x"];
  "X86_MOVUPS128_RR",sail_hl_X86_5fMOVUPS128_5fRR,"MOVUPS",x86_MOVUPS,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_MOVUPS128_STORE_RR",sail_hl_X86_5fMOVUPS128_5fSTORE_5fRR,"MOVUPS",x86_MOVUPS,["m",4;"x",4],["S",128,"m";"S",128,"x"];
  "X86_MOVDQA128_RR",sail_hl_X86_5fMOVDQA128_5fRR,"MOVDQA",x86_MOVDQA,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_MOVDQA128_STORE_RR",sail_hl_X86_5fMOVDQA128_5fSTORE_5fRR,"MOVDQA",x86_MOVDQA,["m",4;"x",4],["S",128,"m";"S",128,"x"];
  "X86_MOVDQU128_RR",sail_hl_X86_5fMOVDQU128_5fRR,"MOVDQU",x86_MOVDQU,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_MOVDQU128_STORE_RR",sail_hl_X86_5fMOVDQU128_5fSTORE_5fRR,"MOVDQU",x86_MOVDQU,["m",4;"x",4],["S",128,"m";"S",128,"x"];
  "X86_MOVD128_RR",sail_hl_X86_5fMOVD128_5fRR,"MOVD",x86_MOVD,["d",4;"m",4],["S",128,"d";"G",32,"m"];
  "X86_MOVD128_STORE_RR",sail_hl_X86_5fMOVD128_5fSTORE_5fRR,"MOVD",x86_MOVD,["m",4;"x",4],["G",32,"m";"S",128,"x"];
  "X86_MOVQ128_RR",sail_hl_X86_5fMOVQ128_5fRR,"MOVQ",x86_MOVQ,["d",4;"m",4],["S",128,"d";"G",64,"m"];
  "X86_MOVQ128_STORE_RR",sail_hl_X86_5fMOVQ128_5fSTORE_5fRR,"MOVQ",x86_MOVQ,["m",4;"x",4],["G",64,"m";"S",128,"x"];
  "X86_MOVQ128_F3_RR",sail_hl_X86_5fMOVQ128_5fF3_5fRR,"MOVQ",x86_MOVQ,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_VPEXTRD128_RRI",sail_hl_X86_5fVPEXTRD128_5fRRI,"VPEXTRD",x86_VPEXTRD,["m",4;"x",4;"imm",8],["G",32,"m";"X",128,"x";"I",0,"imm"];
  "X86_VPEXTRQ128_RRI",sail_hl_X86_5fVPEXTRQ128_5fRRI,"VPEXTRQ",x86_VPEXTRQ,["m",4;"x",4;"imm",8],["G",64,"m";"X",128,"x";"I",0,"imm"];
];;
if length SAIL_HL_X86_SSE_CLAIMS <> 31 ||
   length(setify(map (fun (root,_,_,_,_,_) -> root) SAIL_HL_X86_SSE_CLAIMS)) <> 31
then failwith "sse claim count or duplicate";;
let SAIL_HL_X86_SSE_THEOREMS =
  map SAIL_HL_X86_SSE_CLAIM SAIL_HL_X86_SSE_CLAIMS @
  [SAIL_HL_X86_VZEROUPPER_CLAIM ()];;
List.iter sail_hl_report SAIL_HL_X86_SSE_THEOREMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_SSE_PROOFS_OK";;
