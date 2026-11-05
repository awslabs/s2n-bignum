(* Ordinary record-component laws: neither lemma adds a branch contract. *)
let SAIL_HL_ARM_BRANCH_PC_READS = prove
 (`(!pc:64 word. !s:armstate. read PC (write PC pc s) = pc) /\
   (!pc:64 word. !s:armstate. read events (write PC pc s) = read events s)`,
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[]);;

let SAIL_HL_ARM_BRANCH_PC_SELF = prove
 (`!s:armstate. write PC (read PC s) s = s`,
  MATCH_ACCEPT_TAC(CONJUNCT1(CONJUNCT2(REWRITE_RULE[strongly_valid_component]
    (STRONGLY_VALID_COMPONENT_RULE `PC:(armstate,64 word)component`)))));;
