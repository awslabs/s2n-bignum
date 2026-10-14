(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
          Prove the constant-time and memory-safety property.
******************************************************************************)

needs "arm/proofs/base.ml";;
needs "arm/proofs/consttime.ml";;

(* In s2n-bignum, each assembly function must be proven to be functionally
  correct, and its correctness specification is represented in the
  `<function name>_SUBROUTINE_CORRECT` theorem.
  In Arm, for any assembly function f, there must be a theorem of name
  '<f>_SUBROUTINE_CORRECT'. In x86, there must be four variants for each function
  by a cartesian product of (has IBT?, is Windows ABI?), with the names of
  `<f>{_NOIBT?}{_WINDOWS?}_SUBROUTINE_CORRECT`.

  Additionally, assembly functions in s2n-bignum may be proven to be
  'safe', and the safety properties are named as `*_SUBROUTINE_SAFE`.
  The safety theorem describes the following two properties:

  1. Constant-time property
    Some inputs of an assembly function may contain private (sensitive)
  information. We want execution time of an assembly function to be
  independent from the contents of private inputs.

  2. Memory safety
    Memory safety ensures that all memory accesses during execution happen
  within the permitted memory area. The existing functional correctness specs
  has the `MAYCHANGE` predicate describing which memory areas may have been
  updated, but it still cannot catch the following two corner cases:
    (1) An unpermitted area was read.
    (2) An unpermitted area was silently used as a scratchpad, and then
        recovered to the original value.

  To formally describe & prove these properties, s2n-bignum's formal semantics
  of assembly instructions have a small extension that does not appear in the
  actual architecture: the abstract microarchitectural events.
  For example, a 'ldr' instruction in Arm adds the 'EventLoad(addr,access_size)'
  event to the 'events' field of the program state which is a list of
  microarchitectural events.
  Similarly, a 'str' instruction in Arm will add 'EventStore(addr,access_size)'
  to the event trace. Note that 'EventStore' does not take the stored value as a
  parameter because the stored value won't affect the execution time of 'str'
  (unless Data Memory-dependent Prefetcher is enabled, but it is disabled by
  default when running crypto libs).
  The full definitions of event can be found from the `uarch_event` inductive
  data type in common/safety.ml .

  The spec of a safety property then uses the 'ensures' predicate to inspect
  whether the output events satisfy the two properties. It inspects whether
  (1) The generated events are only depending on the public information, and
  (2) All memory accesses happen within the permitted area,
*)

(* ------------------------------------------------------------------------- *)
(* Proving the safety property of a straight-line code.                      *)
(* ------------------------------------------------------------------------- *)

(* As a start, a simple function that does not have a branch will be chosen and
  verified. The tactics used in this example can be also applied to a function
  that has a loop with constant number of iterations.

  The bignum_mux_4 function in {arm,x86}/p256/bignum_mux_4.S is a simple
  function that receives two input buffers of 32 bytes x[32] and y[32] as well
  as a boolean flag p. If p is zero, x is copied to the output buffer z[32].
  Otherwise, y is copied to z.

  This function must have constant-time execution in the sense that the
  execution time must not depend on the flag p. Also, the function must be
  memory-safe by
  (1) only writing to z[0..31] and
  (2) reading from x[0..31], y[0..32] and possibly z[0..32].

  Let's write the safety spec of this function. As it was done for the
  original functional correctness proofs, the core part of the function without
  callee-save register spills and ret instruction will be veriifed, then
  the full subroutine safety.
  The original correctness theorem BIGNUM_MUX_4_CORRECT was as follows:

  `forall p z x y m n pc.
     nonoverlapping (word pc,0x48) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read PC s = word (pc + 0x44) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [PC; X0; X4] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`

  The safety spec of bignum_mux_4 can be written as follows:
*)

needs "arm/proofs/bignum_mux_4.ml";;

let bignum_mux_4_safety_spec =
  `exists f_events.
      forall e p z x y pc.
        nonoverlapping (word pc,72) (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
        (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
        ==> ensures arm
            (\s.
                aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                read events s = e)
            (\s.
                read PC s = word (pc + 68) /\
                (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z pc /\
                      memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
            (MAYCHANGE [PC; X0; X4] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bignum (z,4)])`;;

(* There are a few interesting points in bignum_mux_4_safety_spec.

  1. The outermost existential quantifier, f_events, enforces that the
     new microarchitectural events only depend on public information.

    The spec says that there exists some function 'f_events' which returns
  a new list of microarchitectural events (e2) after running this program.
  The arguments to f_events are the buffer addresses (x, y, z) and the program
  counter (pc), which are all public information. Note that 'p' must not
  be listed as an argument because it is a private data.
    The benefit of existentially quantifying f_events is that it avoids writing
  the full list of events in the spec which will become too lengthy &
  unreadable. The existential quantification must be located outside the forall
  quantification, not inside, to make f_events independent from possibly
  private parameters like 'p' in forall.
    This style of constant-time property description is written in detail in
  CAV'25, "Relational Hoare Logic for Realistically Modelled Machine Code".
  A slight difference from the paper is that the paper used 'ensures_n' whereas
  the s2n-bignum mainstream uses 'ensures', to reuse existing tactics and lemmas
  at the expense of losing the equivalence property between 'ensures_n' and
  'ensures2'.

  2. The postcondition checks memory safety using the 'memaccess_inbounds'
     predicate.

    'memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]' checks that the new event
  list e2 does not
    (1) have memory read events that don't fit in [x,32; y,32; z,32], and
    (2) have memory write events that don't fit in [z,32].

  3. The MAYCHANGE part is copied from the functional correctness.

    It is already proven in the original functional correctness statement
  (BIGNUM_MUX_4_CORRECT), but the safety property needs it too for
  compositional reasoning, which is about reusing already proven facts about a
  smaller code snippet to prove a larger code: below, the safety of the
  subroutine is derived from that of its core, and the safety theorem of a
  function is used in the same way in the safety proofs of its callers. For
  this, the MAYCHANGE part has to be concretely defined, like
  bignum_mux_4_safety_spec, and all the safety theorems in s2n-bignum have the
  MAYCHANGE parts of their functional correctness theorems.
*)

(*
  For the simple straight-line code, PROVE_SAFETY_SPEC_TAC can be used. It does
  symbolic simulation from the beginning until the PC counter at postcondition
  is hit, accumulates the events, and checks whether the postcondition holds.
*)
let bignum_mux_4_safe = time prove
 (`exists f_events.
      forall e p z x y pc.
        nonoverlapping (word pc,72) (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
        (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
        ==> ensures arm
            (\s.
                aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                read events s = e)
            (\s.
                read PC s = word (pc + 68) /\
                (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z pc /\
                      memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
            (MAYCHANGE [PC; X0; X4] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bignum (z,4)])`,
  (* Assert that the goal is same as bignum_mux_4_safety_spec *)
  ASSERT_CONCL_TAC bignum_mux_4_safety_spec THEN
  (* Go! *)
  PROVE_SAFETY_SPEC_TAC BIGNUM_MUX_4_EXEC);;

(*
  Actually, the above spec is automatically generated from a helper function,
  mk_safety_spec. This is possible because tools/collect-signatures.py parses
  comments of as well as the C function declarations in s2n-bignum.h and
  automatically generates an OCaml list that contains a list of input/output
  buffers. It conservatively marks all function parameters other than buffer
  addresses and buffer sizes as private information.

  needs "arm/proofs/subroutine_signatures.ml";;

  let bignum_mux_4_safety_spec,public_vars = mk_safety_spec
      ~keep_maychanges:true
      (assoc "bignum_mux_4" subroutine_signatures)
      BIGNUM_MUX_4_CORRECT
      BIGNUM_MUX_4_EXEC;;

  public_vars can be passed to PROVE_SAFETY_SPEC_TAC as an optional argument for
  faster symbolic simulation. It will help the tactic ignore values of registers
  that are not described in public_vars.
*)

(* The next step is to prove the subroutine version of the safety spec using
  bignum_mux_4_safe.
  Again, mk_safety_spec can be used to autogenerate the below spec.

  let bignum_mux_4_subroutine_safety_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_mux_4" subroutine_signatures)
    BIGNUM_MUX_4_SUBROUTINE_CORRECT
    BIGNUM_MUX_4_EXEC;;
*)

let bignum_mux_4_subroutine_safe = time prove
 (`exists f_events.
       forall e p z x y pc returnaddress.
           nonoverlapping (word pc,72) (z,8 * 4) /\
           (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
           (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [p; z; x; y] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y z pc returnaddress /\
                         memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,4)])`,
  (* Use ARM_ADD_RETURN_NOSTACK_TAC which already worked for proving subroutine
     spec in the functional correctness world. *)
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MUX_4_EXEC bignum_mux_4_safe THEN

  (* Leaves the following subgoal, which is derived from the 'exists e2. ...'
     clause in the postcondition:
      `exists e2.
        CONS (EventJump (word (pc + 68),returnaddress))
          (APPEND (f_events_callee1 x y z pc) (APPEND [] e)) =
          APPEND e2 e /\
        e2 = f_events x y z pc returnaddress /\
        memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]`

    To prove this kind of goal, DISCHARGE_SAFETY_PROPERTY_TAC will almost always
    work.
  *)
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Proving safety of a program with conditional branches or unbounded loops. *)
(* ------------------------------------------------------------------------- *)

(* If the program of interest has a conditional branch or unbounded loop,
  the end-to-end symbolic simulation tactic (PROVE_SAFETY_SPEC_TAC) won't work.
  Instead, the proof follows the control flow of the program, which is
  described by a skeleton (the safety_skeleton type in common/consttime.ml):

    Leg(name,tac)    a straight-line piece of code, proved by tac;
    Seq(pc,inv,a,b)  a and then b, meeting at pc where inv holds;
    Loop(n,pc1,pc2,inv,pre,body,post)
                     a loop of n iterations (n must not be 0) with head pc1,
                     exit pc2 and invariant inv = \i s. ..., entered by pre
                     and left by post;
    Cases(p,a,b)     a when p holds and b otherwise;
    Then(tac,a)      a after tac, e.g. to establish facts for several legs.

  The skeleton typically follows the flow of the functional correctness proof.
  For example, if the functional correctness proof special-cases n = 0 and
  does symbolic simulation in this case, then the skeleton will also have
  Cases(`n = 0`,...). Similarly, a Seq corresponds to an ENSURES_SEQUENCE_TAC
  and a Loop to an ENSURES_WHILE_*_TAC with the same loop head; the exit of
  the Loop is the instruction after the branch back to the head.

  ARM_SAFETY_SKELETON_TAC computes from the skeleton a scaffolding of f_events
  that mimics the control flow structure of the program, gives it to
  CONCRETIZE_F_EVENTS_TAC, and breaks the ensures with scaffolding down into
  smaller ensure triples using tactics for Hoare logic rules
  (ENSURES_EVENTS_SEQUENCE_TAC for Seq, ENSURES_EVENTS_WHILE_UP2_TAC for Loop)
  and case splits (for Cases). The definitions of these tactics in
  common/consttime.ml have detailed explanations. Each leg then proves its
  ensures triple, typically by symbolic simulation as in a functional
  correctness proof followed by DISCHARGE_SAFETY_PROPERTY_TAC.

  For its example, bignum_mod_n25519 will be illustrated. It takes a big integer
  x of k words (8*k bytes), and stores (n % n_25519) (where n_25519 is a large
  constant) to buffer z of 4 words. Proving its functional correctness needs
  expertise in the algorithmic details, but proving its safety does not need
  that much.
*)

let bignum_mod_n25519_mc =
  define_from_elf "bignum_mod_n25519_mc" "arm/curve25519/bignum_mod_n25519.o";;

let BIGNUM_MOD_N25519_EXEC = ARM_MK_EXEC_RULE bignum_mod_n25519_mc;;

let bignum_mod_n25519_safe = time prove
 (`exists f_events.
        forall e z k x pc.
            nonoverlapping (word pc,304) (z,32)
            ==> ensures arm
                (\s.
                     aligned_bytes_loaded s (word pc) bignum_mod_n25519_mc /\
                     read PC s = word pc /\
                     C_ARGUMENTS [z; k; x] s /\
                     read events s = e)
                (\s.
                     read PC s = word (pc + 248) /\
                     (exists e2.
                          read events s = APPEND e2 e /\
                          e2 = f_events x z k pc /\
                          memaccess_inbounds e2 [x,val k * 8; z,32] [z,32]))
                (MAYCHANGE
                 [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
                 MAYCHANGE SOME_FLAGS ,,
                 MAYCHANGE [events] ,,
                 MAYCHANGE [memory :> bignum (z,4)])`,

  (* The skeleton below gives the following scaffolding to f_events. Each
     f_ev_<name> variable corresponds to the sequence of microarchitectural
     events of the leg <name>, which can be simply proven with symbolic
     simulation.

      \x z k pc.
        // bignum_mod_n25519 has shortcuts when k < 4 (Cases).
        if val k = 0 then
          f_ev_k0 x z k pc
        else if val k = 1 then
          f_ev_k1 x z k pc
        else if val k = 2 then
          f_ev_k2 x z k pc
        else if val k = 3 then
          f_ev_k3 x z k pc
        else
          // This APPEND concatenates the event lists of the two parts of
          // a Seq.
          APPEND
            (if val k - 4 = 0 then
              f_ev_k4 x z k pc
             else
              // This 'APPEND post (APPEND (ENUMERATEL <loopcount> body) pre)'
              // represents the list of events of a Loop.
              APPEND
                (f_ev_post x z k pc)
                (APPEND
                  (ENUMERATEL (val k - 4) (f_ev_loop x z k pc))
                  (f_ev_pre x z k pc)))
            (f_ev_top x z k pc)

     The existentially quantified variables 'f_ev*' are then instantiated
     as metavariables.
     META_EXISTS_TAC is a handy tactic for instantiating existentially
     quantified variable 'x' in the goal 'exists x. ..' where x is some var.
     Compared to `EXISTS_TAC` which has to immediately mention
     what `x` is, `META_EXISTS_TAC` defers the concrete value of `x` until
     special tactics 'UNIFY_REFL_TAC' and 'UNIFY_ACCEPT_TAC' eventually
     tell that 'x was supposed to be instantiated like this!'.
     This is extensively used in safety proofs to defer the instantiation of
     list of microarchitectural events, like 'f_events', because otherwise the
     HOL Light user has to give a lengthy expression for that which can be
     prone to errors. Here, DISCHARGE_SAFETY_PROPERTY_TAC instantiates the
     f_ev* of each leg.

     The word variables listed in the first argument of ARM_SAFETY_SKELETON_TAC
     (here, the number of words k) are generalized as numbers by W64_GEN_TAC,
     with the assumptions `k < 2 EXP 64` and `val (word k) = k`. The terms of
     the skeleton, like `k - 4`, are about these numbers.

     When writing a skeleton, PRINT_GOAL_TAC at the start of a leg shows its
     goal, and 'safety_print_log := true;;' makes
     DISCHARGE_SAFETY_PROPERTY_TAC print the memory accesses that it could not
     prove to be within bounds.
  *)
  ARM_SAFETY_SKELETON_TAC ["k"]
   ((* The four shortcuts. Each leg rewrites the goal with k = 0, ..., so
       UNIFY_REFL_TAC warns that word 0, ... in the arguments of f_ev_k0, ...
       are not variables, which is harmless *)
    Cases(`k = 0`,
      Leg("k0",
        ASM_REWRITE_TAC[] THEN
        ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--9) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC),
    Cases(`k = 1`,
      Leg("k1",
        ASM_REWRITE_TAC[] THEN
        ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--12) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC),
    Cases(`k = 2`,
      Leg("k2",
        ASM_REWRITE_TAC[] THEN
        ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--15) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC),
    Cases(`k = 3`,
      Leg("k3",
        ASM_REWRITE_TAC[] THEN
        ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--17) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC),
    (* The symbolic simulation uses this to take the branch for k >= 4 *)
    Then(SUBGOAL_THEN `4 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC],
    (* The top 4 words of x are loaded, then the rest of the program starts at
       pc + 0x88, where the X1 register holds the number of remaining words *)
    Seq(`pc + 0x88`,
      `\s. read X0 s = z /\ read X2 s = x /\ read X1 s = word(k - 4)`,
      Leg("top",
        (* Facts to normalize the value of X1 and the address of the loads,
           so that the invariant and the bounds of the memory accesses can be
           proven *)
        SUBGOAL_THEN `word_sub (word k) (word 4):int64 = word(k - 4)`
          ASSUME_TAC THENL
         [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN
         `word_add (word_shl (word(k - 4)) 3) x:int64 =
          word_add x (word(8 * (k - 4)))`
          ASSUME_TAC THENL
         [REWRITE_TAC[WORD_SHL_WORD; ARITH_RULE `2 EXP 3 * n = 8 * n`] THEN
          CONV_TAC WORD_RULE;
          ALL_TAC] THEN
        ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--34) THEN
        (* SAFETY_CLOSE_TAC proves the other conjuncts of the postcondition,
           here the invariant, before DISCHARGE_SAFETY_PROPERTY_TAC *)
        SAFETY_CLOSE_TAC),
      (* The main loop runs k - 4 times. As the number of iterations of a Loop
         must not be 0, the case k = 4, which only writes the result back, is
         separate *)
      Cases(`k - 4 = 0`,
        Leg("k4",
          (* With k - 4 = 0, simplify the addresses in the events of the
             top leg, as the symbolic simulation does *)
          ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
          ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--3) THEN
          DISCHARGE_SAFETY_PROPERTY_TAC),
        (* The loop from pc + 0x8c to the branch back at pc + 0xec, exiting at
           pc + 0xf0. X1 counts the remaining words down. *)
        Loop(`k - 4`, `pc + 0x8c`, `pc + 0xf0`,
          `\i s. read X0 s = z /\ read X2 s = x /\ read X1 s = word(k - 4 - i)`,
          Leg("pre",
            VAL_INT64_TAC `k - 4` THEN
            ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC [1] THEN
            SAFETY_CLOSE_TAC),
          Leg("loop",
            (* Facts about the counter word(k - 4 - i), decremented and tested
               for zero, in particular word_sub (word(k - 4 - i)) (word 1) =
               word(k - 4 - (i + 1)) *)
            SAFETY_DOWNCOUNT_FACTS_TAC `i:num` `k - 4` THEN
            ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--25) THEN
            SAFETY_CLOSE_TAC),
          Leg("post",
            ARM_SAFETY_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--2) THEN
            DISCHARGE_SAFETY_PROPERTY_TAC)))))))))));;


(* ------------------------------------------------------------------------- *)
(* Reusing functional correctness tactics for proving the safety property    *)
(* ------------------------------------------------------------------------- *)

(* You can reuse the most of existing tactics for functional correctness. This
  includes

  - ENSURES_INIT_TAC, ENSURES_FINAL_STATE_TAC, {ARM,X86}_STEPS_TAC:
      can be used without any change

  - *_STACK_TAC/*_NOSTACK_TAC: does not immediately discharge the goal
      and will leave a subgoal 'exists e2. ...'.
      DISCHARGE_SAFETY_PROPERTY_TAC will always prove this.

  - {ARM,X86}_SIM_TAC: with two extra arguments, preprocess_tac and
      canonicalize_pc_diff. preprocess_tac must be set to
      'TRY STRIP_EXISTS_ASSUM_TAC', and canonicalize_pc_diff be set to 'false',
      like this:
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false MY_EXEC (..)
      ARM_SAFETY_SIM_TAC MY_EXEC (..) is this ARM_SIM_TAC, and
      X86_SAFETY_SIM_TAC MY_EXEC (..) is a similar simulation for x86. They
      are used in the legs of the skeletons.

  - {ARM,X86}_SUBROUTINE_SIM_TAC: needs is_safety_thm to be set to true, and
      the 'subth' argument must have picked from the assumption registered
      by ASSUME_CALLEE_SAFETY_TAILED_TAC.
      As an example, let's assume that a function f_caller is calling f_callee,
      and f_callee has a safety property theorem named 'f_callee_safe'.
      You can do:

      (* the current goalstate is '|- exists f_events. forall e .... ' *)
      ASSUME_CALLEE_SAFETY_TAILED_TAC smaller_function_safe "H_MY_SAFE" THEN
      META_EXISTS_TAC THEN
      ... THEN
      REMOVE_THEN "H_MY_SAFE" (fun callee_safety_th ->
        X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
          (f_caller_mc,F_CALLER_EXEC,<offset>,F_CALLEE_EXEC,callee_safety_th)
          [`e:(uarch_event)list`; ..(arguments to f_callee)..] <step number>
        THENL [
          ALL_TAC;
          LABEL_TAC "H_MY_SAFE" callee_safety_th (* Register H_MY_SAFE again *)
        ]);;

      Note that {X86,ARM}_SUBROUTINE_SIM_TAC is now returning two subgoals.
      The first subgoal can be proven with EXISTS_E2_TAC.
*)


(* ------------------------------------------------------------------------- *)
(* How can we only prove memory safety but not constant-time property?       *)
(* ------------------------------------------------------------------------- *)

(* You can prove the memory safety property of a program, but not constant-time
  property as follows:

  1. The spec won't need to quantify f_events! The goal is just traditional
     ensures.
  2. You can put this at the postcondition:
    `exists e2.
      read events s = APPEND e2 e /\ memaccess_inbounds e2 [..] [..]`
  3. Just do the symbolic simulation, then reuse DISCHARGE_SAFETY_PROPERTY_TAC.
    It can handle the variant of postcondition having no f_events.

  For slightly more advanced programs like bignum_mod_n25519, using the
  traditional ENSURES_*_TAC with invariants containing
  `read events s = APPEND e2 e /\ memaccess_inbounds e2 [..] [..]` will work.
*)

let bignum_mux_4_memory_safe = time prove
 (`forall e p z x y pc.
      nonoverlapping (word pc,72) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
      (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
      ==> ensures arm
          (\s.
              aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [p; z; x; y] s /\
              read events s = e)
          (\s.
              read PC s = word (pc + 68) /\
              (exists e2.
                    read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
          (MAYCHANGE [PC; X0; X4] ,,
            MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bignum (z,4)])`,
  (* Start with the traditional proof style. *)
  REPEAT GEN_TAC THEN DISCH_THEN ((MAP_EVERY ASSUME_TAC) o CONJUNCTS) THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BIGNUM_MUX_4_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  (* Now the `exists e2. ....` part. *)
  DISCHARGE_SAFETY_PROPERTY_TAC);;