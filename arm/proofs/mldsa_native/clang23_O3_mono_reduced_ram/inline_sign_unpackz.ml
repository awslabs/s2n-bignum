(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The polyz_unpack loops for gamma1 = 2^17 that clang 23 -O3 has inlined    *)
(* into mldsa44_verify_internal (polyvecl_unpack_z, one loop per polynomial  *)
(* of z): 36 bytes of the input and 16 coefficients per iteration, 16        *)
(* iterations. The code loads the bytes with LDRB, LDUR and lane inserts,    *)
(* spreads them with BIC, USHR, UXTL, SHL, TBL and ORR, subtracts the 18-bit *)
(* fields from 2^17 and stores the four vectors with ST4.                    *)
(*                                                                           *)
(* There are two shapes:                                                     *)
(*   A (the first polynomial): the input pointer is a + 1 at the head and    *)
(*     the offset of the output counts up from 0 in steps of 64;             *)
(*   B (the others): the input pointer is a + 35 at the head, the offset of  *)
(*     the output counts from k0 to k0 + 1024 (k0 = 1024 * polynomial) and   *)
(*     the base of z is in another register.                                 *)
(* The vector constants are in registers: QM = 0x000000ff in each lane,      *)
(* QG = 2^17 in each lane, QT1 and QT0 the indices of the two TBL.           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpack.ml";;

let INLINE_Z17_STMT mc loop exit bias k0 (xin,xbase,xoff) (qm,qg,qt1,qt0)
                    (mods:string list) =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  let out = if k0 = 0 then "r" else Printf.sprintf "word_add r (word %d)" k0 in
  let outi = if k0 = 0 then "word_add r (word(4 * i))"
             else Printf.sprintf "word_add r (word(%d + 4 * i))" k0 in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e r a (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (%s,1024)) [(word pc,libmldsa_size); (a,576)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word %d) /\\ read %s s = r /\\
                  read %s s = word %d /\\
                  read %s s = word 0x000000ff000000ff000000ff000000ff /\\
                  read %s s = word 0x00020000000200000002000000020000 /\\
                  read %s s = word 0xffffff07ffffff06ffffff05ffffff04 /\\
                  read %s s = word 0xffffff03ffffff02ffffff01ffffff00 /\\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word %d) /\\ read %s s = r /\\
                  read %s s = word %d /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(%s)) s =
                           mld_polyz_unpack_17 b i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [a,576; %s,1024] [%s,1024]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(%s,1024)])"
   out mc loop xin bias xbase xoff k0 qm qg qt1 qt0
   exit xin (576 + bias) xbase xoff (k0 + 1024) outi out out
   (String.concat "; " xmods) (String.concat "; " qmods) out);;

(*** The addresses of the loads, as the simulation forms them from the  ***)
(*** input pointer a + 36 * i + bias, as the facts of CHUNK_INPUT_TAC   ***)

let INLINE_Z17_ALIASES bias =
  let ptr = Printf.sprintf "(36 * i + %d)" bias in
  let old k = if k = 0 then "word_add a (word (36 * i))"
              else Printf.sprintf "word_add a (word (36 * i + %d))" k in
  List.concat(map (fun k ->
    let d = k - bias in
    if d = 0 then [] else if d > 0 then
      [Printf.sprintf "word_add a (word (%s + %d)):int64 = %s" ptr d (old k)]
    else
      let m = -d in
      [Printf.sprintf "word_add a (word (%s + %s)):int64 = %s" ptr
         (string_of_num (((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/
                         (Num.num_of_int m))) (old k);
       Printf.sprintf "word_add a (word_sub (word %s) (word %d)):int64 = %s"
         ptr m (old k)]) (0--35));;

let INLINE_Z17_EVENTS bias =
  let ptr = Printf.sprintf "(36 * i + %d)" bias in
  let old k = if k = 0 then "word_add a (word (36 * i))"
              else Printf.sprintf "word_add a (word (36 * i + %d))" k in
  [List.concat(map (fun k ->
    let d = k - bias in
    if d = 0 then [] else if d > 0 then
      [Printf.sprintf "word_add (word_add a (word %s)) (word %d):int64 = %s"
         ptr d (old k);
       Printf.sprintf "word_add a (word (%s + %d)):int64 = %s" ptr d (old k)]
    else
      let m = -d in
      [Printf.sprintf "word_add (word_add a (word %s)) (word %s):int64 = %s" ptr
         (string_of_num (((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/
                         (Num.num_of_int m))) (old k);
       Printf.sprintf "word_sub (word_add a (word %s)) (word %d):int64 = %s"
         ptr m (old k);
       Printf.sprintf "word_add a (word_sub (word %s) (word %d)):int64 = %s"
         ptr m (old k)]) (0--35))];;

(*** qpart: the vector registers whose first write in the loop is a lane  ***)
(*** insert, whose initial values are abbreviated as variables (otherwise  ***)
(*** the store of the results, which mentions them, is lost in stepping)   ***)

let INLINE_POLYZ17_GEN_LOOP mc exec loop exit bias k0 nsteps
                        (xin,xbase,xoff) (qm,qg,qt1,qt0) (mods:string list)
                        (qpart:string list) =
  let outj = if k0 = 0 then "word_add r (word(4 * j))"
             else Printf.sprintf "word_add r (word(%d + 4 * j))" k0 in
  let offi = if k0 = 0 then "64 * i" else Printf.sprintf "%d + 64 * i" k0 in
  INLINE_CHUNK_PROVE
   (INLINE_Z17_STMT mc loop exit bias k0 (xin,xbase,xoff) (qm,qg,qt1,qt0) mods)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "b:num->byte"; "pc:num"]
   16 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word_add a (word (36 * i + %d)) /\\
            read %s s = r /\\ read %s s = word (%s) /\\
            read %s s = word 0x000000ff000000ff000000ff000000ff /\\
            read %s s = word 0x00020000000200000002000000020000 /\\
            read %s s = word 0xffffff07ffffff06ffffff05ffffff04 /\\
            read %s s = word 0xffffff03ffffff02ffffff01ffffff00 /\\
            (!j. j < 576
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 16 * i
                 ==> read(memory :> bytes32(%s)) s =
                     mld_polyz_unpack_17 b j)"
     xin bias xbase xoff offi qm qg qt1 qt0 outj)
   (CHUNK_INPUT_TAC `b:num->byte` 36 THEN
    INLINE_ALIAS_TAC (INLINE_Z17_ALIASES bias) THEN
    MAP_EVERY (fun q ->
      let v = mk_var(String.lowercase_ascii q,`:int128`) in
      let r = mk_const(q,[]) in
      SUBGOAL_THEN (mk_exists(v,mk_eq(list_mk_comb(`read:(armstate,int128)component->armstate->int128`,[r;`s0:armstate`]),v)))
        (X_CHOOSE_TAC v) THENL
       [EXISTS_TAC (list_mk_comb(`read:(armstate,int128)component->armstate->int128`,[r;`s0:armstate`])) THEN REFL_TAC; ALL_TAC])
     qpart THEN
    ARM_STEPS_TAC exec (1--nsteps) THEN
    WIDE_STORE_SPLIT_TAC `r:int64` 32 THEN INLINE_ST4_LANES_TAC THEN
    INLINE_CHUNK_FINAL_TAC mld_polyz_unpack_17 `b:num->byte`
      [INLINE_DIV4_16; INLINE_MOD4_16]
      [ARITH_RULE `64 * (i + 1) = 64 * i + 64`;
       ARITH_RULE (parse_term(Printf.sprintf "%d + 64 * (i + 1) = (%d + 64 * i) + 64" k0 k0));
       ARITH_RULE (parse_term(Printf.sprintf "36 * (i + 1) + %d = (36 * i + %d) + 36" bias bias))]
      (INLINE_Z17_EVENTS bias));;

let INLINE_POLYZ17_LOOP mc exec loop exit bias k0 nsteps xs qs mods =
  INLINE_POLYZ17_GEN_LOOP mc exec loop exit bias k0 nsteps xs qs mods
   ["Q6";"Q16";"Q17";"Q18"];;

(*** The instances: function, head, exit, bias, k0, number of steps, the  ***)
(*** input pointer, the base and the offset of the output, the vector     ***)
(*** constants (mask, 2^17, the indices of the second and the first TBL)  ***)

let INLINE_Z17_MODS_A =
  ["X0";"X1";"X2";"X3";"X4";"X5";"X6";"X7";"X8";"X9";"X11";"X12";"X13";
   "X14";"X15";"X16";"X17";"X18";"X26";"X27";
   "Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q16";"Q17";"Q18";"Q19";"Q20"];;

let INLINE_Z17_MODS_B t =
  ["X0";"X1";"X2";"X3";"X4";"X5";"X6";"X7";"X8";"X9";"X10";"X11";"X12";
   "X13";"X14";"X15";"X16";"X17";"X18";t;
   "Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q16";"Q17";"Q18";"Q19";"Q20"];;

let INLINE_POLYZ17_INSTANCES =
 ["mldsa44_verify_internal", "mldsa44_verify_internal_loop2",
  "mldsa44_verify_internal_loop2_exit", 1, 0, 134,
  ("X9","X10","X8"), INLINE_Z17_MODS_A;
  "mldsa44_verify_internal", "mldsa44_verify_internal_loop3",
  "mldsa44_verify_internal_loop3_exit", 35, 1024, 133,
  ("X8","X26","X9"), INLINE_Z17_MODS_B "X27";
  "mldsa44_verify_internal", "mldsa44_verify_internal_loop4",
  "mldsa44_verify_internal_loop4_exit", 35, 2048, 133,
  ("X8","X27","X9"), INLINE_Z17_MODS_B "X28";
  "mldsa44_verify_internal", "mldsa44_verify_internal_loop5",
  "mldsa44_verify_internal_loop5_exit", 35, 3072, 133,
  ("X8","X28","X9"), INLINE_Z17_MODS_B "X30"];;

let INLINE_POLYZ17_OF_INSTANCE (fn,hl,el,bias,k0,n,xs,mods) =
  INLINE_POLYZ17_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el bias k0 n xs ("Q0","Q1","Q22","Q21") mods;;
