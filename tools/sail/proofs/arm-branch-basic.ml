(* All B/BL offsets and RET register fields/states under the frozen
   instruction-PC, disabled-GCS and BType-write exclusion boundaries.
   RET has no proof-side discarded metadata component. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-branch-basic.ml";;
needs "tools/sail/proofs/arm-branch-unconditional-lemmas.ml";;

(* Every encoded imm26 and both signed offset extremes are quantified.
   Under the existing disabled-GCS contract, Sail's short-circuit guard
   does not read PCR or PSTATE, so neither is an exported parameter.
   HOL's input PC has already advanced by four bytes. *)
let SAIL_HL_ARM_B_EQ = prove
 (`!immediate:26 word. !s t:armstate.
   sail_hl_arm_5fB
     (PC :> evaluate (\pc:64 word. word_sub pc (word 4)))
     immediate s t <=>
   arm_B (word(val immediate * 4):28 word) s t`,
  SAIL_HL_ARM_BRANCH_UNCONDITIONAL_TAC [sail_hl_arm_5fB; arm_B]);;
sail_hl_report ("SAIL_HL_ARM_B_EQ", SAIL_HL_ARM_B_EQ);;

let SAIL_HL_ARM_BL_EQ = prove
 (`!immediate:26 word. !s t:armstate.
   sail_hl_arm_5fBL
     (PC :> evaluate (\pc:64 word. word_sub pc (word 4)))
     immediate s t <=>
   arm_BL (word(val immediate * 4):28 word) s t`,
  SAIL_HL_ARM_BRANCH_UNCONDITIONAL_TAC [sail_hl_arm_5fBL; arm_BL]);;
sail_hl_report ("SAIL_HL_ARM_BL_EQ", SAIL_HL_ARM_BL_EQ);;

(* RET under the exporter's explicit BType-write exclusion. Disabled GCS
   short-circuits its PCR/PSTATE queries; the RET decoder selects no PAC.
   No metadata component is replaced by rvalue in this proof. *)
let SAIL_HL_ARM_RET_EQ = prove
 (`!register:5 word.
   !s t:armstate.
   sail_hl_arm_5fRET
     (PC :> evaluate (\pc:64 word. word_sub pc (word 4)))
     register s t <=>
   arm_RET (XREG' register) s t`,
  SAIL_HL_ARM_BRANCH_UNCONDITIONAL_TAC [sail_hl_arm_5fRET; arm_RET]);;
sail_hl_report ("SAIL_HL_ARM_RET_EQ", SAIL_HL_ARM_RET_EQ);;

check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_BRANCH_BASIC_PROOFS_OK";;
