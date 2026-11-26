(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the packing and unpacking loops of verify_internal and         *)
(* signature_internal that clang has inlined into them (polyz_unpack,        *)
(* polyz_pack, polyt0_unpack, polyt1_unpack, polyw1_unpack, polyeta_unpack), *)
(* one generator per shape of loop, in the style of INLINE_CADDQ_LOOP in     *)
(* inline_sign.ml: the lemma goes from the head of the loop to its exit, and *)
(* has the correctness and the events together,                              *)
(*                                                                           *)
(*   exists f_events. forall e <pointers> <inputs> pc. ... ==> ensures arm   *)
(*     (\s. aligned_bytes_loaded s (word pc) mc /\                           *)
(*          read PC s = word (pc + head) /\ <registers> /\ <inputs> /\       *)
(*          read events s = e)                                               *)
(*     (\s. read PC s = word (pc + exit) /\ <registers> /\ <outputs> /\      *)
(*          exists e2. read events s = APPEND e2 e /\                        *)
(*                     e2 = f_events <pointers> pc /\                        *)
(*                     memaccess_inbounds e2 <read regions> <written>)       *)
(*     (MAYCHANGE ...)                                                       *)
(*                                                                           *)
(* The head and the exit are given as the name of a label in the layout, or  *)
(* as a numeral (the address in the image) when the layout has no label.     *)
(* The registers are given by name (e.g. "X9", "Q7"), in the order of the    *)
(* canonical vector R0, R1, ... of the shape (order of first appearance in   *)
(* the loop), as in INLINE_CADDQ_LOOP. Each generator is followed by the     *)
(* list of its instances, INLINE_<SHAPE>_INSTANCES, as (function, head,      *)
(* exit, registers).                                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* STATUS (arm-C2). Proved, each on at least two instances where the image   *)
(* has two, with the run times of one instance:                              *)
(*   INLINE_POLYETA4_SCALAR_LOOP   shape 64   2 instances        13 s        *)
(*   INLINE_POLYETA2_LOOP          shape 15   44 and 87 (4)      22-25 s     *)
(*   INLINE_POLYT0_LOOP            shape 23   44 and 87 (3)      45 s        *)
(*   INLINE_POLYZ_PACK_17_LOOP     shape 18   44 (1 instance)    26 s        *)
(* Written but NOT PROVED (the proof ran into the problems noted):           *)
(*   INLINE_POLYW1_88_LOOP         shapes 30, 34, 37 (the same code): the    *)
(*     steps run; LD3 needs the input as 128-bit reads (INLINE_MERGE128_TAC, *)
(*     added last, untested) and the ST4 results have to be split into 32-bit *)
(*     facts (not written); parameters INLINE_POLYW1_88_SHAPE30              *)
(*   INLINE_POLYZ19_LOOP           shapes 81, 82, 120, 57: never run         *)
(* Not written: shapes 26 (the w1 loop that loads its TBL indices in the     *)
(* loop), 65 and 69 (polyeta_unpack, eta = 4, vectorized, with image         *)
(* constants and overlapping partial stores), 67 and 103 (polyz_pack for     *)
(* 2^19, with 17 image constants). Blocked by the model (LDUR of B,          *)
(* arm-A's 7c4b45532, not merged here): shapes 3, 40, 41 (polyz_unpack for   *)
(* 2^17) and 42 (polyt1_unpack).                                             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The exit of a loop, where the loop invariant gives the postcondition ***)

let INLINE_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The exec theorem for the range of a loop: from its head to its exit ***)
(*** (a name of the layout or a numeral for each)                        ***)

let INLINE_LOOP_EXEC loop exit =
  let n s = try int_of_string s with Failure _ -> layout s in
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(n loop, n exit)];;

(* ------------------------------------------------------------------------- *)
(* The common frame of the proofs: a loop of N iterations whose test is the  *)
(* end of the body (ENSURES_EVENTS_WHILE_UP2_TAC), given                     *)
(*   tm      the statement                                                   *)
(*   evbs    the binders of the arguments of f_events, e.g. "(r:int64)"      *)
(*   evas    the same arguments without types, e.g. "r"                      *)
(*   gens    the variables generalized after the events e, ending with pc    *)
(*   n       the number of iterations                                        *)
(*   inv     the invariant (\i s. ...)                                       *)
(*   body    the tactic for the body, after the start of the iteration       *)
(* The events are the epilogue, the n iterations and the prologue, which     *)
(* depend on the addresses only.                                             *)
(* ------------------------------------------------------------------------- *)

let INLINE_CHUNK_PROVE tm evbs evas gens n exec loop exit inv body =
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\%s (pc:num).
        APPEND (f_ev_epil %s pc)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop %s pc i))
                 (f_ev_prol %s pc)) :(uarch_event)list"
     evbs evas n evas evas)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC (map parse_term ("e:(uarch_event)list"::gens)) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_small_numeral n) (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (parse_term inv) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN body;

    INLINE_EXIT_TAC]);;

(*** The input of an iteration as 128-bit values, for LD1, LD2, LD3, LD4: the ***)
(*** reads of n consecutive 16-byte values at a + c * i + 16 * k, in terms    ***)
(*** of the bytes of the input (the facts of CHUNK_INPUT_TAC, at the head).   ***)

let INLINE_MERGE128_TAC (c:int) (n:int) =
  let tm k =
    parse_term(Printf.sprintf
     "read (memory :> bytes128 (word_add a (word (%s)))) s0"
     (if k = 0 then Printf.sprintf "%d * i" c
      else Printf.sprintf "%d * i + %d" c (16 * k))) in
  MP_TAC(end_itlist CONJ (map (fun k -> READ_MEMORY_MERGE_CONV 4 (tm k))
                              (0--(n-1)))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

(*** Simulating the n instructions of a body one at a time, rewriting the   ***)
(*** addresses in the assumptions with the given equations after each step, ***)
(*** so that the addresses of loads and stores keep the form of the         ***)
(*** invariant (pointer plus literal offset) when a register is the sum of  ***)
(*** two registers of the invariant.                                        ***)

let INLINE_NORMALIZE_TAC =
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV));;

(*** A down counter: a register holding word(n - i) at the head of iteration ***)
(*** i, decremented by one (SUBS) and tested for zero. The facts about the   ***)
(*** decremented register and about its zero flag, to be used by the final   ***)
(*** tactic as assumptions.                                                   ***)

let INLINE_DOWN_SUB1 = prove
 (`!n i. i < n /\ n < 2 EXP 64
         ==> word_sub (word (n - i)) (word 1):int64 = word (n - (i + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n - (i + 1) = (n - i) - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let INLINE_DOWN_ZF = prove
 (`!n i. i < n /\ n < 2 EXP 64
         ==> (val(word (n - (i + 1)):int64) = 0 <=> i + 1 = n)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n - (i + 1) < 2 EXP 64` (fun th -> ASM_SIMP_TAC[th; MOD_LT]) THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let INLINE_DOWN_COUNTER_TAC (n:term) =
  MP_TAC(SPECL [n; `i:num`] INLINE_DOWN_SUB1) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [n; `i:num`] INLINE_DOWN_ZF) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; DISCH_TAC];;

(*** The facts about the input at the head of the iteration, CHUNK_INPUT_TAC  ***)
(*** states them at word_add a (word(n + m)). The simulation of a load with ***)
(*** a pointer register that has been advanced by an offset (e.g. the second ***)
(*** register of a LDP with post-index) forms the address as               ***)
(*** word_add (word_add a (word n)) (word m): add a copy of each fact with   ***)
(*** this form of the address.                                              ***)

let INLINE_ADDR_SPLIT = WORD_RULE
 `!a:int64 n m. word_add a (word (n + m)) = word_add (word_add a (word n)) (word m)`;;

let INLINE_INPUT_DUP_TAC =
  let pats = [`read (memory :> bytes8 (word_add a (word (n + m)))) s = x`;
              `read (memory :> bytes16 (word_add a (word (n + m)))) s = x`;
              `read (memory :> bytes32 (word_add a (word (n + m)))) s = x`;
              `read (memory :> bytes64 (word_add a (word (n + m)))) s = x`] in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      if exists (fun p -> can (term_match [] p) (concl th)) pats &&
         not(is_forall(concl th))
      then
        let th' = REWRITE_RULE[INLINE_ADDR_SPLIT] th in
        if concl th' = concl th then failwith "" else th'
      else failwith "") asl in
    MAP_EVERY ASSUME_TAC ths);;

let INLINE_STEPS_TAC exec (rules:thm list) n =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC exec [k] THEN
    RULE_ASSUM_TAC(REWRITE_RULE rules)) (1--n);;

(* ------------------------------------------------------------------------- *)
(* The statement of a lemma: for an input array of INLEN bytes at a (of      *)
(* values b), read, and an output array of OUTLEN bytes at r, written, with  *)
(*   vars    the quantified variables after e, e.g. "r a (b:num->byte)"      *)
(*   pre     the registers and the input at the head                         *)
(*   post    the registers and the output at the exit                        *)
(*   mods    the registers written                                           *)
(* ------------------------------------------------------------------------- *)

let INLINE_STMT mc loop exit vars inlen outlen pre post (mods:string list) =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (r,%d)) [(word pc,libmldsa_size); (a,%d)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  %s /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  %s /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [a,%d; r,%d] [r,%d]))
             (MAYCHANGE [PC; %s] ,, %sMAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(r,%d)])"
   vars outlen inlen mc loop pre exit post inlen outlen outlen
   (String.concat "; " xmods)
   (if qmods = [] then "" else
    Printf.sprintf "MAYCHANGE [%s] ,, " (String.concat "; " qmods)) outlen);;

(* ------------------------------------------------------------------------- *)
(* polyeta_unpack for eta = 4, scalar loop (2 instances in                   *)
(* mldsa65_signature_internal, which clang -O3 has also vectorized, as the   *)
(* shape 65, 69, when the output does not overlap the input): one byte of    *)
(* the input and two coefficients per iteration, with the registers          *)
(*   R0 = temporary, R1 = a (input), R2 = byte index (from 0), R3 = output   *)
(*   pointer, R4 = 4, R5 = temporary                                         *)
(*     ldrb R0, [R1, R2]; and R0, R0, #0xf; str R0, [R3]; sub R0, R4, R0;    *)
(*     ldrb R5, [R1, R2]; add R2, R2, #1; cmp R2, #0x80; sub R5, R4, R5 lsr 4; *)
(*     stp R0, R5, [R3], #8; b.ne                                            *)
(* ------------------------------------------------------------------------- *)

let INLINE_POLYETA4_SCALAR_LOOP_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e r a (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,128)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = word 0 /\\
                  read %s s = r /\\ read %s s = word 4 /\\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word 128 /\\
                  read %s s = word_add r (word 1024) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyeta_unpack_4 b i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [a,128; r,1024] [r,1024]))
             (MAYCHANGE [PC; %s; %s; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(r,1024)])"
   mc loop (r 1) (r 2) (r 3) (r 4) exit (r 2) (r 3) (r 0) (r 2) (r 3) (r 5));;

let INLINE_POLYETA4_SCALAR_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_CHUNK_PROVE (INLINE_POLYETA4_SCALAR_LOOP_TERM mc loop exit rs)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "b:num->byte"; "pc:num"]
   128 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = a /\\ read %s s = word i /\\
            read %s s = word_add r (word(8 * i)) /\\ read %s s = word 4 /\\
            (!j. j < 128
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 2 * i
                 ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                     mld_polyeta_unpack_4 b j)" (r 1) (r 2) (r 3) (r 4))
   (CHUNK_INPUT_TAC `b:num->byte` 1 THEN
    ARM_STEPS_TAC exec (1--10) THEN
    CHUNK_FULL_FINAL_TAC mld_polyeta_unpack_4 `b:num->byte`);;

(*** (function, head, exit, registers) ***)

let INLINE_POLYETA4_SCALAR_INSTANCES =
 ["mldsa65_signature_internal", "mldsa65_signature_internal_loop37",
  "mldsa65_signature_internal_loop37_exit",
  ["X11";"X9";"X8";"X10";"X14";"X12"];
  "mldsa65_signature_internal", "mldsa65_signature_internal_loop46",
  "mldsa65_signature_internal_loop46_exit",
  ["X11";"X9";"X8";"X10";"X14";"X12"]];;

(* ------------------------------------------------------------------------- *)
(* polyeta_unpack for eta = 2, as clang -O3 has inlined it in               *)
(* mldsa{44,87}_signature_internal (4 instances): three bytes of the input   *)
(* and eight coefficients per iteration, 32 iterations. The input is read at *)
(* R2 + R1, the output is at R4 + (R5 - 16) with R5 = 16 + 32 * i. The      *)
(* registers are                                                             *)
(*   R0 = temporary, R1 = byte index (k at the head, k + 3 * i), R2 = input  *)
(*   base (a - k), R3 = temporary, R4 = output base (r), R5 = 16 at the head,*)
(*   R6 = temporary, R7 = 2, R8, ..., R13 = temporaries                      *)
(* with the input at a (so a = R2 + k) and the output at r.                  *)
(* ------------------------------------------------------------------------- *)

let INLINE_POLYETA2_LOOP_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_STMT mc loop exit "r a m (b:num->byte)" 96 1024
   (Printf.sprintf
     "read %s s = word m /\\ read %s s = word_sub a (word m) /\\
      read %s s = r /\\ read %s s = word 16 /\\ read %s s = word 2 /\\
      (!j. j < 96
           ==> read(memory :> bytes8(word_add a (word j))) s = b j)"
     (r 1) (r 2) (r 4) (r 5) (r 7))
   (Printf.sprintf
     "read %s s = word (m + 96) /\\ read %s s = word 1040 /\\
      (!i. i < 256
           ==> read(memory :> bytes32(word_add r (word(4 * i)))) s =
               mld_polyeta_unpack_2 b i)" (r 1) (r 5))
   (map r [0;1;3;5;6;8;9;10;11;12;13]);;

let INLINE_POLYETA2_ADDR_RULES =
 [WORD_RULE `!m i a. word_add (word (m + 3 * i)) (word_sub a (word m)) =
                     word_add a (word (3 * i))`;
  WORD_RULE `!r i. word_add r (word (16 + 32 * i)) =
                   word_add (word_add r (word (32 * i))) (word 16)`];;

let INLINE_POLYETA2_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_CHUNK_PROVE (INLINE_POLYETA2_LOOP_TERM mc loop exit rs)
   "(r:int64) (a:int64)" "r a"
   ["r:int64"; "a:int64"; "m:num"; "b:num->byte"; "pc:num"]
   32 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word (m + 3 * i) /\\ read %s s = word_sub a (word m) /\\
            read %s s = r /\\ read %s s = word(16 + 32 * i) /\\
            read %s s = word 2 /\\
            (!j. j < 96
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 8 * i
                 ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                     mld_polyeta_unpack_2 b j)" (r 1) (r 2) (r 4) (r 5) (r 7))
   (CHUNK_INPUT_TAC `b:num->byte` 3 THEN
    INLINE_STEPS_TAC exec INLINE_POLYETA2_ADDR_RULES 44 THEN
    INLINE_NORMALIZE_TAC THEN
    CHUNK_FULL_FINAL_TAC mld_polyeta_unpack_2 `b:num->byte`);;

(*** (function, head, exit, registers) ***)

let INLINE_POLYETA2_INSTANCES =
 ["mldsa44_signature_internal", "mldsa44_signature_internal_loop28",
  "mldsa44_signature_internal_loop28_exit",
  ["X10";"X8";"X27";"X12";"X20";"X9";"X11";"X24";"X13";"X14";"X15";"X16";"X17";"X18"];
  "mldsa44_signature_internal", "mldsa44_signature_internal_loop37",
  "mldsa44_signature_internal_loop37_exit",
  ["X10";"X8";"X20";"X12";"X23";"X9";"X11";"X24";"X13";"X14";"X15";"X16";"X17";"X18"];
  "mldsa87_signature_internal", "mldsa87_signature_internal_loop45",
  "mldsa87_signature_internal_loop45_exit",
  ["X10";"X8";"X19";"X12";"X23";"X9";"X11";"X0";"X13";"X14";"X15";"X16";"X17";"X18"];
  "mldsa87_signature_internal", "mldsa87_signature_internal_loop54",
  "mldsa87_signature_internal_loop54_exit",
  ["X10";"X8";"X19";"X12";"X27";"X9";"X11";"X0";"X13";"X14";"X15";"X16";"X17";"X18"]];;

(* ------------------------------------------------------------------------- *)
(* polyt0_unpack, as clang -O3 has inlined it in signature_internal          *)
(* (3 instances): 13 bytes of the input and 8 coefficients per iteration, 32 *)
(* iterations, with scalar loads and stores (the loop writes partial results *)
(* before the final ones, as the C code does). The registers are             *)
(*   R0 = temporary, R1 = input pointer (a + 6 at the head: the loop reads   *)
(*   the 13 bytes at R1 - 6), R2 = temporary (output pointer), R3 = output   *)
(*   base (r), R4 = output offset (0, + 32), R5 = temporary, R6 = 4096,      *)
(*   R7, ..., R13 = temporaries                                              *)
(* ------------------------------------------------------------------------- *)

let INLINE_POLYT0_LOOP_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_STMT mc loop exit "r a (b:num->byte)" 416 1024
   (Printf.sprintf
     "read %s s = word_add a (word 6) /\\ read %s s = r /\\
      read %s s = word 0 /\\ read %s s = word 4096 /\\
      (!j. j < 416
           ==> read(memory :> bytes8(word_add a (word j))) s = b j)"
     (r 1) (r 3) (r 4) (r 6))
   (Printf.sprintf
     "read %s s = word_add (word_add a (word 416)) (word 6) /\\
      read %s s = word 1024 /\\
      (!i. i < 256
           ==> read(memory :> bytes32(word_add r (word(4 * i)))) s =
               mld_polyt0_unpack b i)" (r 1) (r 4))
   (map r [0;1;2;4;5;7;8;9;10;11;12;13]);;

let INLINE_POLYT0_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_CHUNK_PROVE (INLINE_POLYT0_LOOP_TERM mc loop exit rs)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "b:num->byte"; "pc:num"]
   32 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word_add (word_add a (word(13 * i))) (word 6) /\\
            read %s s = r /\\ read %s s = word(32 * i) /\\
            read %s s = word 4096 /\\
            (!j. j < 416
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 8 * i
                 ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                     mld_polyt0_unpack b j)" (r 1) (r 3) (r 4) (r 6))
   (CHUNK_INPUT_TAC `b:num->byte` 13 THEN
    ARM_STEPS_TAC exec (1--75) THEN
    CHUNK_FULL_FINAL_TAC mld_polyt0_unpack `b:num->byte`);;

(*** (function, head, exit, registers) ***)

let INLINE_POLYT0_INSTANCES =
 ["mldsa44_signature_internal", "mldsa44_signature_internal_loop41",
  "mldsa44_signature_internal_loop41_exit",
  ["X11";"X9";"X10";"X23";"X8";"X12";"X1";"X13";"X14";"X15";"X16";"X17";"X18";"X0"];
  "mldsa65_signature_internal", "mldsa65_signature_internal_loop51",
  "mldsa65_signature_internal_loop51_exit",
  ["X11";"X9";"X10";"X20";"X8";"X12";"X1";"X13";"X14";"X15";"X16";"X17";"X18";"X0"];
  "mldsa87_signature_internal", "mldsa87_signature_internal_loop58",
  "mldsa87_signature_internal_loop58_exit",
  ["X11";"X9";"X10";"X27";"X8";"X12";"X1";"X13";"X14";"X15";"X16";"X17";"X18";"X0"]];;

(* ------------------------------------------------------------------------- *)
(* polyz_pack for gamma1 = 2^17, as clang -O3 has inlined it in              *)
(* mldsa44_signature_internal (1 instance): 4 coefficients and 9 bytes per   *)
(* iteration, 64 iterations, with a down counter. The input is read at R2 -  *)
(* 8 (R2 = a + 8 at the head), the output is written at R10 - 8 (R10 = r + 8 *)
(* at the head). The registers are                                           *)
(*   R0, R1 = temporaries, R2 = input pointer, R3, R4 = temporaries,         *)
(*   R5 = counter (64 at the head), R6 = 2^17, R7, R8, R9 = temporaries,     *)
(*   R10 = output pointer, R11 = temporary                                   *)
(* ------------------------------------------------------------------------- *)

let INLINE_POLYZ_PACK_17_LOOP_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_STMT mc loop exit "r a (x:num->int32)" 1024 576
   (Printf.sprintf
     "read %s s = word_add a (word 8) /\\ read %s s = word_add r (word 8) /\\
      read %s s = word 64 /\\ read %s s = word 131072 /\\
      (!j. j < 256
           ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j)"
     (r 2) (r 10) (r 5) (r 6))
   (Printf.sprintf
     "read %s s = word_add (word_add a (word 1024)) (word 8) /\\
      read %s s = word_add (word_add r (word 576)) (word 8) /\\
      read %s s = word 0 /\\
      (!j. j < 576
           ==> read(memory :> bytes8(word_add r (word j))) s =
               mld_polyz_pack_17 x j)" (r 2) (r 10) (r 5))
   (map r [0;1;2;3;4;5;7;8;9;10;11]);;

let INLINE_POLYZ_PACK_17_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_CHUNK_PROVE (INLINE_POLYZ_PACK_17_LOOP_TERM mc loop exit rs)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "x:num->int32"; "pc:num"]
   64 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word_add (word_add a (word(16 * i))) (word 8) /\\
            read %s s = word_add (word_add r (word(9 * i))) (word 8) /\\
            read %s s = word (64 - i) /\\ read %s s = word 131072 /\\
            (!j. j < 256
                 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                     x j) /\\
            (!j. j < 9 * i
                 ==> read(memory :> bytes8(word_add r (word j))) s =
                     mld_polyz_pack_17 x j)" (r 2) (r 10) (r 5) (r 6))
   (INLINE_DOWN_COUNTER_TAC `64` THEN
    CHUNK_INPUT_TAC `x:num->int32` 4 THEN INLINE_INPUT_DUP_TAC THEN
    ARM_STEPS_TAC exec (1--28) THEN INLINE_NORMALIZE_TAC THEN
    CHUNK_FULL_FINAL_TAC mld_polyz_pack_17 `x:num->int32`);;

(*** (function, head, exit, registers) ***)

let INLINE_POLYZ_PACK_17_INSTANCES =
 ["mldsa44_signature_internal", "mldsa44_signature_internal_loop34",
  "mldsa44_signature_internal_loop34_exit",
  ["X11";"X12";"X9";"X13";"X14";"X10";"X0";"X16";"X18";"X15";"X8";"X17"]];;

(* ------------------------------------------------------------------------- *)
(* polyz_unpack for gamma1 = 2^19 (ML-DSA-65 and ML-DSA-87), as clang -O3    *)
(* has inlined it in verify_internal (shapes 81, 82 and 120) and             *)
(* signature_internal (shape 57), vectorized by the SLP vectorizer: 8        *)
(* coefficients and 20 bytes of the input per iteration, 32 iterations, the  *)
(* bytes inserted in vector lanes (LD1 lane loads), the result stored by     *)
(* ST2. Parameters of the generator (the registers are the X registers in    *)
(* order of first appearance in the loop, then the Q registers, as printed   *)
(* by the instances, with the indices                                        *)
(*   in    the input pointer, at a + in_off at the head (the loop reads the  *)
(*         20 bytes at in - in_off), plus 20 per iteration                   *)
(*   ob    the register with the output base: r - idx0 (r if idx0 = 0)      *)
(*   idx   the output offset: idx0 at the head, plus 32 per iteration       *)
(*   qm    the vector with the mask 0xff in each 32-bit lane               *)
(*   qc    the vector with 2^19 in each 32-bit lane                          *)
(* and the indices of the registers the loop writes.                         *)
(* ------------------------------------------------------------------------- *)

let INLINE_Z19_CONSTS cs rs =
  String.concat "" (map (fun (k,v) ->
    Printf.sprintf " /\\ read %s s = %s" (List.nth rs k) v) cs);;

let INLINE_POLYZ19_LOOP_TERM
    (in_i,ob_i,idx_i,qm_i,qc_i,in_off,idx0,nsteps,mods_i,cs) mc loop exit
    (rs:string list) =
  let r k = List.nth rs k in
  INLINE_STMT mc loop exit "r a (b:num->byte)" 640 1024
   (Printf.sprintf
     "read %s s = word_add a (word %d) /\\ read %s s = %s /\\
      read %s s = word %d /\\
      read %s s = word 0x000000ff000000ff000000ff000000ff /\\
      read %s s = word 0x00080000000800000008000000080000%s /\\
      (!j. j < 640
           ==> read(memory :> bytes8(word_add a (word j))) s = b j)"
     (r in_i) in_off (r ob_i)
     (if idx0 = 0 then "r" else Printf.sprintf "word_sub r (word %d)" idx0)
     (r idx_i) idx0 (r qm_i) (r qc_i) (INLINE_Z19_CONSTS cs rs))
   (Printf.sprintf
     "read %s s = word_add (word_add a (word 640)) (word %d) /\\
      read %s s = word %d /\\
      (!i. i < 256
           ==> read(memory :> bytes32(word_add r (word(4 * i)))) s =
               mld_polyz_unpack_19 b i)" (r in_i) in_off (r idx_i) (idx0 + 1024))
   (map r mods_i);;

let INLINE_POLYZ19_ADDR_RULES =
 [WORD_RULE `!r i. word_add (word_sub r (word 1024)) (word (1024 + 32 * i)) =
                   word_add r (word (32 * i))`;
  WORD_RULE `!r i. word_add (word_sub r (word 4096)) (word (4096 + 32 * i)) =
                   word_add r (word (32 * i))`];;

let INLINE_POLYZ19_LOOP
    ((in_i,ob_i,idx_i,qm_i,qc_i,in_off,idx0,nsteps,mods_i,cs) as p)
    mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  INLINE_CHUNK_PROVE (INLINE_POLYZ19_LOOP_TERM p mc loop exit rs)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "b:num->byte"; "pc:num"]
   32 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word_add (word_add a (word(20 * i))) (word %d) /\\
            read %s s = %s /\\ read %s s = word(%s32 * i) /\\
            read %s s = word 0x000000ff000000ff000000ff000000ff /\\
            read %s s = word 0x00080000000800000008000000080000%s /\\
            (!j. j < 640
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 8 * i
                 ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                     mld_polyz_unpack_19 b j)"
     (r in_i) in_off (r ob_i)
     (if idx0 = 0 then "r" else Printf.sprintf "word_sub r (word %d)" idx0)
     (r idx_i) (if idx0 = 0 then "" else Printf.sprintf "%d + " idx0)
     (r qm_i) (r qc_i) (INLINE_Z19_CONSTS cs rs))
   (CHUNK_INPUT_TAC `b:num->byte` 20 THEN INLINE_INPUT_DUP_TAC THEN
    INLINE_STEPS_TAC exec INLINE_POLYZ19_ADDR_RULES nsteps THEN
    INLINE_NORMALIZE_TAC THEN
    CHUNK_FULL_FINAL_TAC mld_polyz_unpack_19 `b:num->byte`);;

(*** Parameters for the shapes. Shape 81 (verify_internal, five polynomials of ***)
(*** z of ML-DSA-65 and ML-DSA-87): X0, in = X1, X2 .. X5, ob = X6, idx = X7,  ***)
(*** Q2 .. Q7 (8 .. 13), Q0 (14) = mask, Q1 (15) = 2^19; the output is at     ***)
(*** ob + idx with idx = 0x400 at the head.                                    ***)

let INLINE_POLYZ19_SHAPE81 = (1,6,7,14,15,19,1024,67,
  [0;1;2;3;4;5;7;8;9;10;11;12;13],[]);;

(*** Shapes 82 and 120 (verify_internal, the sixth and seventh polynomials of  ***)
(*** z of ML-DSA-87 and the sixth of ML-DSA-65): the loop bound is in X10      ***)
(*** (idx runs from 0x1000 to 0x1400); X0 .. X5, in = X1, ob = X6, idx = X7,  ***)
(*** X8 = 0x1400, Q2 .. Q7, Q0 (14)... see the registers of the instances.    ***)

let INLINE_POLYZ19_SHAPE81_INSTANCES =
 ["mldsa65_verify_internal", "mldsa65_verify_internal_loop2",
  "mldsa65_verify_internal_loop2_exit",
  ["X12"; "X9"; "X14"; "X15"; "X11"; "X13"; "X10"; "X8"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop3",
  "mldsa65_verify_internal_loop3_exit",
  ["X11"; "X8"; "X13"; "X14"; "X10"; "X12"; "X26"; "X9"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop4",
  "mldsa65_verify_internal_loop4_exit",
  ["X11"; "X8"; "X13"; "X14"; "X10"; "X12"; "X27"; "X9"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop5",
  "mldsa65_verify_internal_loop5_exit",
  ["X11"; "X8"; "X13"; "X14"; "X10"; "X12"; "X28"; "X9"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop2",
  "mldsa87_verify_internal_loop2_exit",
  ["X12"; "X9"; "X14"; "X15"; "X11"; "X13"; "X10"; "X8"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop3",
  "mldsa87_verify_internal_loop3_exit",
  ["X11"; "X8"; "X13"; "X14"; "X10"; "X12"; "X27"; "X9"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop4",
  "mldsa87_verify_internal_loop4_exit",
  ["X11"; "X8"; "X13"; "X14"; "X10"; "X12"; "X28"; "X9"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop5",
  "mldsa87_verify_internal_loop5_exit",
  ["X11"; "X8"; "X13"; "X14"; "X10"; "X12"; "X26"; "X9"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"]];;

(* ------------------------------------------------------------------------- *)
(* polyw1_unpack for gamma2 = (q - 1) / 88 (ML-DSA-44), as clang -O3 has     *)
(* inlined it in mldsa44_signature_internal in four parts (shapes 26, 30,   *)
(* 34, 37 of the same instruction sequence up to the registers, and the     *)
(* loads of the constants in the first): 64 coefficients and 48 bytes of    *)
(* the input per iteration (LD3 of the bytes, TBL to spread them in 32-bit  *)
(* lanes, ST4 of the results), 4 iterations. The input is at a, the output *)
(* at r. Parameters: the indices into the registers (the X registers in     *)
(* order of first appearance, then the Q registers) of                      *)
(*   inb   the register with the input base a                               *)
(*   idx   the input offset, 0 at the head, plus 48 per iteration           *)
(*   out   the output pointer, r at the head, plus 256 per iteration       *)
(* the registers that hold constants during the loop with their values (the *)
(* four vectors of TBL indices, the masks 0x30 and 0x3c, and the page of   *)
(* the image with the TBL indices for the first part, which loads them in   *)
(* the loop: adrp gives word(pc + 245760)), and the number of steps.        *)
(* ------------------------------------------------------------------------- *)

let INLINE_W1_PAGE = "word(pc + 245760)";;
let INLINE_W1_TBL0 = "word 0xffffff03ffffff02ffffff01ffffff00";;
let INLINE_W1_TBL1 = "word 0xffffff07ffffff06ffffff05ffffff04";;
let INLINE_W1_TBL2 = "word 0xffffff0bffffff0affffff09ffffff08";;
let INLINE_W1_TBL3 = "word 0xffffff0fffffff0effffff0dffffff0c";;
let INLINE_W1_MASK30 = "word 0x00000030000000300000003000000030";;
let INLINE_W1_MASK3C = "word 0x0000003c0000003c0000003c0000003c";;

let INLINE_POLYW1_88_LOOP_TERM (inb,idx,out,consts,nsteps) mc loop exit
                               (rs:string list) =
  let r k = List.nth rs k in
  let cs = String.concat " /\\ "
    (map (fun (k,v) -> Printf.sprintf "read %s s = %s" (r k) v) consts) in
  let mods = filter (fun k -> k <> inb && not(List.mem_assoc k consts))
                    (0--(length rs - 1)) in
  INLINE_STMT mc loop exit "r a (b:num->byte)" 192 1024
   (Printf.sprintf
     "read %s s = a /\\ read %s s = word 0 /\\ read %s s = r /\\ %s /\\
      (!j. j < 192
           ==> read(memory :> bytes8(word_add a (word j))) s = b j)"
     (r inb) (r idx) (r out) cs)
   (Printf.sprintf
     "read %s s = word 192 /\\ read %s s = word_add r (word 1024) /\\
      (!i. i < 256
           ==> read(memory :> bytes32(word_add r (word(4 * i)))) s =
               mld_polyw1_unpack_88 b i)" (r idx) (r out))
   (map r mods);;

let INLINE_POLYW1_88_INV (inb,idx,out,consts,nsteps) (rs:string list) =
  let r k = List.nth rs k in
  let cs = String.concat " /\\ "
    (map (fun (k,v) -> Printf.sprintf "read %s s = %s" (r k) v) consts) in
  Printf.sprintf
     "\\i s. read %s s = a /\\ read %s s = word(48 * i) /\\
            read %s s = word_add r (word(256 * i)) /\\ %s /\\
            (!j. j < 192
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 64 * i
                 ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                     mld_polyw1_unpack_88 b j)"
     (r inb) (r idx) (r out) cs;;

let INLINE_POLYW1_88_LOOP ((inb,idx,out,consts,nsteps) as p) mc exec loop exit
                          (rs:string list) =
  INLINE_CHUNK_PROVE (INLINE_POLYW1_88_LOOP_TERM p mc loop exit rs)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "b:num->byte"; "pc:num"]
   4 exec loop exit (INLINE_POLYW1_88_INV p rs)
   (CHUNK_INPUT_TAC `b:num->byte` 48 THEN INLINE_INPUT_DUP_TAC THEN
    ARM_STEPS_TAC exec (1--nsteps) THEN INLINE_NORMALIZE_TAC THEN
    CHUNK_FULL_FINAL_TAC mld_polyw1_unpack_88 `b:num->byte`);;

(*** Shape 30, 34, 37: the constants are in registers before the loop ***)

let INLINE_POLYW1_88_SHAPE30 = (1,2,3,
  [8,INLINE_W1_TBL0; 12,INLINE_W1_TBL1; 16,INLINE_W1_TBL2; 19,INLINE_W1_TBL3;
   26,INLINE_W1_MASK3C; 27,INLINE_W1_MASK30],66);;
let INLINE_POLYW1_88_SHAPE30_INSTANCES =
 ["mldsa44_signature_internal", "mldsa44_signature_internal_loop47",
  "mldsa44_signature_internal_loop47_exit",
  ["X11"; "X12"; "X9"; "X10"; "Q2"; "Q4"; "Q5"; "Q3"; "Q12"; "Q6"; "Q7"; "Q16"; "Q13"; "Q17"; "Q18"; "Q20"; "Q1"; "Q24"; "Q21"; "Q0"; "Q22"; "Q30"; "Q25"; "Q19"; "Q23"; "Q31"; "Q15"; "Q14"; "Q26"; "Q8"; "Q27"; "Q9"; "Q28"; "Q29"; "Q10"; "Q11"]];;

(*** The same parameters and registers for shapes 34 and 37 (same code up to ***)
(*** the numbers of the scalar registers) ***)

let INLINE_POLYW1_88_SHAPE34_INSTANCES =
 ["mldsa44_signature_internal", "mldsa44_signature_internal_loop49",
  "mldsa44_signature_internal_loop49_exit",
  ["X11"; "X0"; "X9"; "X10"; "Q2"; "Q4"; "Q5"; "Q3"; "Q12"; "Q6"; "Q7"; "Q16"; "Q13"; "Q17"; "Q18"; "Q20"; "Q1"; "Q24"; "Q21"; "Q0"; "Q22"; "Q30"; "Q25"; "Q19"; "Q23"; "Q31"; "Q15"; "Q14"; "Q26"; "Q8"; "Q27"; "Q9"; "Q28"; "Q29"; "Q10"; "Q11"]];;

let INLINE_POLYW1_88_SHAPE37_INSTANCES =
 ["mldsa44_signature_internal", "mldsa44_signature_internal_loop51",
  "mldsa44_signature_internal_loop51_exit",
  ["X11"; "X1"; "X9"; "X10"; "Q2"; "Q4"; "Q5"; "Q3"; "Q12"; "Q6"; "Q7"; "Q16"; "Q13"; "Q17"; "Q18"; "Q20"; "Q1"; "Q24"; "Q21"; "Q0"; "Q22"; "Q30"; "Q25"; "Q19"; "Q23"; "Q31"; "Q15"; "Q14"; "Q26"; "Q8"; "Q27"; "Q9"; "Q28"; "Q29"; "Q10"; "Q11"]];;


let INLINE_POLYZ19_SHAPE82 = (1,6,7,15,16,19,4096,67,
  [0;1;2;3;4;5;7;9;10;11;12;13;14],[8,"word 5120"]);;

let INLINE_POLYZ19_SHAPE120 = INLINE_POLYZ19_SHAPE82;;

(*** Shape 57 (signature_internal, polynomials of z of ML-DSA-65 and          ***)
(*** ML-DSA-87): in = X1 (a + 9 at the head), ob = X5 = r, idx = X6 (from 0), ***)
(*** Q6 (13) = mask, Q7 (14) = 2^19                                           ***)

let INLINE_POLYZ19_SHAPE57 = (1,5,6,13,14,9,0,69,
  [0;1;2;3;4;6;7;8;9;10;11;12],[]);;

let INLINE_POLYZ19_SHAPE82_INSTANCES =
 ["mldsa65_verify_internal", "mldsa65_verify_internal_loop6",
  "mldsa65_verify_internal_loop6_exit",
  ["X12"; "X8"; "X14"; "X15"; "X11"; "X13"; "X22"; "X9"; "X10"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop6",
  "mldsa87_verify_internal_loop6_exit",
  ["X12"; "X8"; "X14"; "X15"; "X11"; "X13"; "X22"; "X9"; "X10"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"]];;

let INLINE_POLYZ19_SHAPE120_INSTANCES =
 ["mldsa87_verify_internal", "mldsa87_verify_internal_loop7",
  "mldsa87_verify_internal_loop7_exit",
  ["X12"; "X8"; "X14"; "X15"; "X11"; "X13"; "X23"; "X9"; "X10"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop8",
  "mldsa87_verify_internal_loop8_exit",
  ["X12"; "X8"; "X14"; "X15"; "X11"; "X13"; "X24"; "X9"; "X10"; "Q2"; "Q4"; "Q3"; "Q5"; "Q6"; "Q7"; "Q0"; "Q1"]];;

let INLINE_POLYZ19_SHAPE57_INSTANCES =
 ["mldsa65_signature_internal", "mldsa65_signature_internal_loop5",
  "mldsa65_signature_internal_loop5_exit",
  ["X10"; "X9"; "X11"; "X12"; "X13"; "X20"; "X8"; "Q0"; "Q1"; "Q2"; "Q3"; "Q4"; "Q5"; "Q6"; "Q7"];
  "mldsa65_signature_internal", "mldsa65_signature_internal_loop41",
  "mldsa65_signature_internal_loop41_exit",
  ["X10"; "X9"; "X11"; "X12"; "X13"; "X20"; "X8"; "Q0"; "Q1"; "Q2"; "Q3"; "Q4"; "Q5"; "Q6"; "Q7"];
  "mldsa87_signature_internal", "mldsa87_signature_internal_loop5",
  "mldsa87_signature_internal_loop5_exit",
  ["X10"; "X9"; "X11"; "X12"; "X13"; "X27"; "X8"; "Q0"; "Q1"; "Q2"; "Q3"; "Q4"; "Q5"; "Q6"; "Q7"];
  "mldsa87_signature_internal", "mldsa87_signature_internal_loop48",
  "mldsa87_signature_internal_loop48_exit",
  ["X10"; "X9"; "X11"; "X12"; "X13"; "X27"; "X8"; "Q0"; "Q1"; "Q2"; "Q3"; "Q4"; "Q5"; "Q6"; "Q7"]];;

