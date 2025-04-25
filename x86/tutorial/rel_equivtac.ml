(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
        An example that proves equivalence of two straight-line codes
        accessing memory or vector registers using EQUIV_STEPS_TAC.
******************************************************************************)

(* Please copy this file to the root directory of
   s2n-bignum, then follow the instructions. *)

needs "x86/proofs/equiv.ml";;

(* This example will define & prove the equivalence of two programs
   using EQUIV_STEPS_TAC.
   This tactic is useful if two programs are supposed to have many
   equivalent parts. EQUIV_STEPS_TAC receives 'actions', which is an
   OCaml list stating which lines are equivalent and which lines are diverging.
   This 'actions' can be generated from, say, syntactic diff of
   two assembly programs. s2n-bignum also has tools/gen-actions.py
   which runs the `diff` linux tool on two assembly files. *)

let mc = define_assert_from_elf "mc" "x86/tutorial/rel_equivtac.o" [
  0x48; 0x8b; 0x38;        (* MOV (% rdi) (Memop Quadword (%% (rax,0))) *)
  0x48; 0x8b; 0x70; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rax,8))) *)
  0x48; 0x83; 0xc7; 0x01;  (* ADD (% rdi) (Imm8 (word 1)) *)
  0x48; 0x0f; 0xaf; 0xf7;  (* IMUL (% rsi) (% rdi) *)
  0x48; 0x89; 0x33         (* MOV (Memop Quadword (%% (rbx,0))) (% rsi) *)
];;

(* Note that the used registers are different between mc and mc2
   (rsi,rdi vs. r8,r9). This is fine since EQUIV_STEPS_TAC
   can smartly map differently used registers. *)
let mc2 = define_assert_from_elf "mc2" "x86/tutorial/rel_equivtac2.o" [
  0x4c; 0x8b; 0x00;        (* MOV (% r8) (Memop Quadword (%% (rax,0))) *)
  0x4c; 0x8b; 0x48; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rax,8))) *)
  0x4d; 0x0f; 0xaf; 0xc1;  (* IMUL (% r8) (% r9) *)
  0x4d; 0x01; 0xc8;        (* ADD (% r8) (% r9) *)
  0x4c; 0x89; 0x03         (* MOV (Memop Quadword (%% (rbx,0))) (% r8) *)
];;

let EXEC = X86_MK_EXEC_RULE mc;;
let EXEC2 = X86_MK_EXEC_RULE mc2;;

(* Define the equality between the input states. *)
let eqin = new_definition
  `forall s1 s1' inbuf outbuf.
    (eqin:(x86state#x86state)->int64->int64->bool) (s1,s1') inbuf outbuf <=>
     (// The values of buffer pointers, RAX and RBX.
      // Their values are symbolically defined as inbuf and outbuf.
      // outbuf is also used for the nonoverlapping precondition between
      // the output buffer and the program bytecode.
      read RAX s1 = inbuf /\
      read RAX s1' = inbuf /\
      read RBX s1 = outbuf /\
      read RBX s1' = outbuf /\
      // The equal buffer contents at the input buffer. '2' stands for 2 words
      // (and 1 word is 8 bytes, hence 2*8=16 bytes)
      (exists n.
        bignum_from_memory (inbuf,2) s1 = n /\
        bignum_from_memory (inbuf,2) s1' = n))`;;

(* Define the equality between the output states. *)
let eqout = new_definition
  `forall s1 s1' outbuf.
    (eqout:(x86state#x86state)->int64->bool) (s1,s1') outbuf <=>
     (read RBX s1 = outbuf /\
      read RBX s1' = outbuf /\
      (exists n.
        bignum_from_memory (outbuf,1) s1 = n /\
        bignum_from_memory (outbuf,1) s1' = n))`;;

(* Now, build the program equivalence statement using
   'mk_equiv_statement_simple'.
   Its first argument states the assumption that will appear at
   LHS of '<assumption> ==> ensures2 ..(equiv statement)..'.

   If it fails, please try `x86_print_log := true`. *)
let equiv_goal = mk_equiv_statement_simple
  `ALL (nonoverlapping (outbuf,8)) [
    (word pc:int64, LENGTH mc);
    (word pc2:int64, LENGTH mc2)
  ]`
  eqin  (* Input state equivalence *)
  eqout (* Output state equivalence *)
  mc EXEC  (* First program machine code *)
  `MAYCHANGE [RIP; RSI; RDI] ,, MAYCHANGE [memory :> bytes (outbuf, 8)] ,,
   MAYCHANGE SOME_FLAGS`
  mc2 EXEC2 (* Second program machine code *)
  `MAYCHANGE [RIP; R8; R9] ,, MAYCHANGE [memory :> bytes (outbuf, 8)] ,,
   MAYCHANGE SOME_FLAGS`;;

(* equiv_goal is:
  `forall pc pc2 inbuf outbuf.
       ALL (nonoverlapping (outbuf,8))
       [word pc,LENGTH mc; word pc2,LENGTH mc2]
       ==> ensures2 x86
           (\(s,s2).
                bytes_loaded s (word pc) mc /\
                read RIP s = word pc /\
                bytes_loaded s2 (word pc2) mc2 /\
                read RIP s2 = word pc2 /\
                eqin (s,s2) inbuf outbuf)
           (\(s,s2).
                bytes_loaded s (word pc) mc /\
                read RIP s = word (pc + 18) /\
                bytes_loaded s2 (word pc2) mc2 /\
                read RIP s2 = word (pc2 + 17) /\
                eqout (s,s2) outbuf)
           (\(s,s2) (s',s2').
                (MAYCHANGE [RIP; RSI; RDI] ,,
                 MAYCHANGE [memory :> bytes (outbuf,8)])
                s
                s' /\
                (MAYCHANGE [RIP; R8; R9] ,,
                 MAYCHANGE [memory :> bytes (outbuf,8)])
                s2
                s2')
           (\s. 5)
           (\s. 5)`
*)

(* Now, let's prove the program equivalence. *)
let EQUIV = prove(equiv_goal,

  (* Rewrite SOME_FLAGS, ALL, nonoverlapping, and LENGTH * *)
  REWRITE_TAC[SOME_FLAGS; ALL;NONOVERLAPPING_CLAUSES;
              fst EXEC; fst EXEC2] THEN
  REPEAT STRIP_TAC THEN

  (** Initialize **)
  EQUIV_INITIATE_TAC eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Do symbolic simulations on the two programs using EQUIV_STEPS_TAC.
     As explained before, the action is an OCaml list.
     Each item describes:
     - ("equal",begin line number of program 1 (start from 0),
                end line number of program 1 (not inclusive),
                begin line number of program 2,
                end line number of program 2)
       : means that these instructions in program 1 and program 2 must
         yield sysmbolically equivalent output. Therefore, EQUIV_STEPS_TAC
         uses a lock-step simulation for these.
         If the symbolic outputs of the matching instructions are not having
         equal expression, it will print an error message.
         Actually, it tries to solve a simple bit-vector equality such as
           'x * (y + 1) = x * y + x',
         and can succeed. This is exactly the example case here.
     - ("replace",beign line number of program 1,
                  end line number of program 1 (not inclusive),
                  begin line number of program 2,
                  end line number of program 2)
       : means that these instructions in program 1 and 2 differ.
         EQUIV_STEPS_TAC uses stuttering simulations for each program.
  *)
  EQUIV_STEPS_TAC [
    ("equal",0,2,0,2);
    ("replace",2,4,2,4);
    ("equal",4,5,4,5)
  ] EXEC EXEC2 THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  (* This tactic below is typically fixed and probably you will want to reuse. :) *)
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[eqout;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (outbuf,1) s`] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

(*
    If the EQUIV_STEPS_TAC fails to prove that instructions that are supposed
    to be equivalent according to actions are yielding equal output expressions,
    it will print a message like this:

    X86_LOCKSTEP_TAC (4,4)
    Running left...
    Running right...
    1 basis elements and 0 critical pairs
            - Error: WORD_RULE could not prove
              `<word expression (program 2)> = <word expression (program 1)>`

    If you are certain that these expressions must be equal, you can improve
    `extra_word_CONV` of symbolic simulator by adding a custom word equation
    to extra_word_CONV.

    ```
    let org_convs = !extra_word_CONV;;
    extra_word_CONV := (GEN_REWRITE_CONV I [<your_word_thm>])::org_convs;;
    ```
*)



(* The second example that uses the SSE registers and vector operations.
   The following `pxor_mc` program has a couple of PXOR instructions. PXOR
   leaves the upper half bits of the YMM registers untouched. We will show that,
   given the equalities on the lower half of YMM registers (Which are `read
   XMM{n}_SSE ..`), after running the two PXOR instructions the YMM registers
   will still result in equalities of their lower halfs.
 *)

let pxor_mc = define_assert_from_elf "pxor_mc" "x86/tutorial/rel_equivtac_sse.o" [
  0x66; 0x0f; 0xef; 0xca;  (* PXOR (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0xef; 0xcb   (* PXOR (%_% xmm1) (%_% xmm3) *)
];;

let PXOR_EXEC = X86_MK_EXEC_RULE pxor_mc;;

(* Define the equality between the state components. *)
let pxor_eq = new_definition
  `forall s1 s1'.
    (pxor_eq:(x86state#x86state)->bool) (s1,s1') <=>
     ((exists n. read XMM1_SSE s1 = n /\ read XMM1_SSE s1' = n) /\
      (exists n. read XMM2_SSE s1 = n /\ read XMM2_SSE s1' = n) /\
      (exists n. read XMM3_SSE s1 = n /\ read XMM3_SSE s1' = n))`;;

let equiv_goal = mk_equiv_statement_simple
  `true` (* no global preconditions *)
  pxor_eq  (* Input state equivalence *)
  pxor_eq (* Output state equivalence *)
  pxor_mc PXOR_EXEC  (* First program machine code *)
  `MAYCHANGE [RIP] ,, MAYCHANGE [YMM1_SSE]`
  pxor_mc PXOR_EXEC (* Second program machine code *)
  `MAYCHANGE [RIP] ,, MAYCHANGE [YMM1_SSE]`;;


(* Given `read XMM{n}_SSE s0 = rhs`, this rule proves
   `exists x. read YMM{n} s0 = word_join x rhs`. *)
let EXPAND_READ_XMM_SSE_RULE th =
  try
    let th' = REWRITE_RULE ([XMM0_SSE; XMM1_SSE; XMM2_SSE; XMM3_SSE;
        XMM4_SSE; XMM5_SSE; XMM6_SSE; XMM7_SSE;
        XMM8_SSE; XMM9_SSE; XMM10_SSE; XMM11_SSE;
        XMM12_SSE; XMM13_SSE; XMM14_SSE; XMM15_SSE;
        READ_BOTTOM_128] @ READ_YMM_SSE_EQUIV) th in
    let the_lhs,rhs = dest_eq (concl th') in
    let c_word_subword,read_ymm::idx::[] = strip_comb (the_lhs) in
    let c_read,the_ymm::statevar::[] = strip_comb read_ymm in
    let upperbits_var = mk_var ("x",`:(128)word`) in
    let new_goal = mk_exists(upperbits_var, mk_eq(read_ymm,
        list_mk_comb (`word_join:(128)word->(128)word->(256)word`,
                      [upperbits_var;rhs]))) in
    TAC_PROOF((["",th],new_goal),
        EXISTS_TAC (list_mk_comb
          (`word_subword:(256)word->(num#num)->(128)word`,
          [read_ymm;`(128,128)`])) THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th'] THEN
        CONV_TAC WORD_BLAST)
  with _ -> failwith ("Could not expand " ^ (string_of_thm th));;


let org_extra_word_conv = !extra_word_CONV;;

(* Enable simplification of word_subwords by default *)
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ !extra_word_CONV;;

(* Now, let's prove the program equivalence. *)
let EQUIV = prove(equiv_goal,

  REWRITE_TAC[fst PXOR_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (** Initialize **)
  EQUIV_INITIATE_TAC pxor_eq THEN
  REPEAT (FIRST_X_ASSUM
    (fun th -> MP_TAC (EXPAND_READ_XMM_SSE_RULE th) THEN STRIP_TAC)) THEN

  EQUIV_STEPS_TAC [
    ("equal",0,2,0,2);
  ] PXOR_EXEC PXOR_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN

  (* No CONJ_TAC this time, because MAYCHANGE part was already discharged! *)
  ASM_REWRITE_TAC([pxor_eq] @ [XMM1_SSE; XMM2_SSE; XMM3_SSE; READ_BOTTOM_128] @
      READ_YMM_SSE_EQUIV) THEN
  CONV_TAC (ONCE_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  MESON_TAC[]);;


extra_word_CONV := org_extra_word_conv;;