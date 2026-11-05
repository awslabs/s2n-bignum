(* All targets/states under the same explicit flat branch/disabled-GCS
   contracts. This execute-helper/linker theorem is not a decoder claim. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-branch-absolute-execute.ml";;
needs "tools/sail/proofs/arm-branch-unconditional-lemmas.ml";;

(* The offset is reconstructed only in the theorem. The supplied wrapper
   passes its arbitrary64-bit parameter directly to the actual execute
   body. No target-to-register equality or alignment premise is needed. *)
let SAIL_HL_ARM_BL_ABSOLUTE_OFFSET = prove
 (`!target pc:64 word.
   word_add (word_sub pc (word 4))
     (word_sub target (word_sub pc (word 4))) = target`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_BL_ABSOLUTE_EXECUTE_EQ = prove
 (`!target:64 word. !s t:armstate.
   sail_hl_arm_5fBL_5fABSOLUTE_5fEXECUTE
     (PC :> evaluate (\pc:64 word. word_sub pc (word 4)))
     (word_sub target (word_sub (read PC s) (word 4))) s t <=>
   arm_BL_ABSOLUTE target s t`,
  SAIL_HL_ARM_BRANCH_UNCONDITIONAL_TAC
    [sail_hl_arm_5fBL_5fABSOLUTE_5fEXECUTE; arm_BL_ABSOLUTE;
     SAIL_HL_ARM_BL_ABSOLUTE_OFFSET] THEN
  REWRITE_TAC[SAIL_HL_ARM_BL_ABSOLUTE_OFFSET; EQ_SYM_EQ]);;

sail_hl_report ("SAIL_HL_ARM_BL_ABSOLUTE_EXECUTE_EQ", SAIL_HL_ARM_BL_ABSOLUTE_EXECUTE_EQ);;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_BRANCH_ABSOLUTE_EXECUTE_PROOFS_OK";;
