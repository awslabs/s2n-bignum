(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The SHAKE256 of the public key that clang 23 -O3 has inlined into         *)
(* mldsa{44,65,87}_pk_from_sk for tr = H(pk, 64): the lemma of               *)
(* inline_sign_shake_gen.ml (generated for mld_verify_internal), with the    *)
(* register that holds pk and the frame of the state as parameters, and the  *)
(* registers of the surrounding comparison of t0 (mld_ct_memcmp), whose last *)
(* instructions the compiler has scheduled into the sponge (the result of    *)
(* the comparison in X24 = w28 ^ w27, the OR of two check flags in X11), as  *)
(* parameters of the statement.                                              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_shake_gen.ml";;

(*** The statement for pk in register pkreg; the frame region that must not ***)
(*** overlap pk and the code is [fp - 240, fp + sh_t + sh_t64), with the    ***)
(*** state and tr inside it                                                 ***)

let KG_SHAKE_TERM p pkreg =
  let fr = 240 + (max (p.sh_a + 208) (p.sh_t + 64)) in
  parse_term(Printf.sprintf
 "exists f_events.
    forall e (fp:int64) (pk:int64) PK %s (st:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ st = word_add fp (word %d) /\\
      nonoverlapping (word_sub fp (word 240),%d) (word pc,libmldsa_size) /\\
      nonoverlapping (word_sub fp (word 240),%d) (pk,%d)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %d) /\\
                read SP s = fp /\\ read %s s = pk /\\ %s
                read (memory :> bytes(pk,%d)) s = PK /\\
                read events s = e)
           (\\s. read PC s = word (pc + %d) /\\ %s
                read (memory :> bytes(word_add fp (word %d),64)) s =
                  num_of_bytelist(list_of_seq (mld_shake256_byte %d PK) 64) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp pk pc /\\
                   memaccess_inbounds e2
                    [pk,%d; word_add fp (word %d),208;
                     word_add fp (word %d),64; word_sub fp (word 240),240;
                     %sword(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_add fp (word %d),208; word_add fp (word %d),64;
                     word_sub fp (word 240),240]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [%s] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word %d),208);
                       memory :> bytes(word_add fp (word %d),64);
                       memory :> bytes(word_sub fp (word 240),240)])"
  p.sh_vars p.sh_a fr fr p.sh_pklen (SHAKE_START p) pkreg p.sh_pre p.sh_pklen
  (SHAKE_STOP p) p.sh_post p.sh_t p.sh_pklen p.sh_pklen p.sh_a p.sh_t
  p.sh_reads p.sh_a p.sh_t p.sh_mods p.sh_a p.sh_t);;

(*** As INLINE_SHAKE_PROVE, for the statement KG_SHAKE_TERM ***)

let KG_SHAKE_PROVE p pkreg =
  let c0 = hd p.sh_calls in
  prove
   (KG_SHAKE_TERM p pkreg,
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
     "H_PERM" THEN
    CONCRETIZE_F_EVENTS_TAC
     `\(fp:int64) (pk:int64) (pc:num). f_ev_shk fp pk pc :(uarch_event)list` THEN
    META_EXISTS_TAC THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst (SHAKE_EXEC p)] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `st:int64` then SUBST_ALL_TAC th
      else NO_TAC) THEN
    FULL_INIT_TAC THEN SHAKE_PK_LANES_TAC p THEN
    SHAKE_PK_ABBREV_TAC p THEN SHAKE_PK_BOUND_TAC p THEN SHAKE_PK128_TAC p THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC (SHAKE_EXEC p) [n] THEN SHAKE_SPLIT_TAC p)
     (1--c0) THEN
    SHAKE_ASSEMBLE_TAC p (SHAKE_TA 0) (SHAKE_SV c0) THEN
    SHAKE_CALL_TAC p (SHAKE_TA 0) (c0 + 1) THEN
    MAP_EVERY (SHAKE_BLOCK_TAC p) (1--(SHAKE_NB p - 1)) THEN
    SHAKE_LAST_TAC p THEN SHAKE_TAIL_TAC p);;

(* ------------------------------------------------------------------------- *)
(* The instance of mldsa44_pk_from_sk: pk (1312 bytes) in X19 from the first  *)
(* block (the state at fp + 7008 is zeroed by stores of Q17 = 0), tr at      *)
(* fp + 6848, and ends before the last store of the zeroing of the state (the *)
(* PC is the address of that store). X0 and X24 hold the address of the state, X23 and X25 two      *)
(* check flags (ORed into X11 inside the tail), X27 and X28 the registers of *)
(* the comparison (X24 := w28 ^ w27 at the last padding byte).               *)
(* ------------------------------------------------------------------------- *)

let KG_SHAKE44_INST =
  { sh_fn = "mldsa44_pk_from_sk"; sh_start = "in_shake256_part3";
    sh_stop = "in_shake256_part5_end";
    sh_pklen = 1312; sh_a = 7008; sh_t = 6848;
    sh_vars = "(r23:int64) (r25:int64) (r27:int64) (r28:int64)";
    sh_pre = "read X0 s = st /\\
              read X24 s = st /\\
              read X23 s = r23 /\\ read X25 s = r25 /\\
              read X27 s = r27 /\\ read X28 s = r28 /\\
              read Q17 s = word 0 /\\";
    sh_post = "read X8 s = st /\\
               read X11 s = word_zx(word_or (word_zx r23:int32)
                                            (word_zx r25:int32)) /\\
               read X24 s = word_zx(word_xor (word_zx r28:int32)
                                             (word_zx r27:int32)) /\\";
    sh_reads = ""; sh_mods = "X18; X24; X30";
    sh_calls = [70;134;198;263;335;407;479;551;623;680];
    sh_last_bytes = (88--95) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [88;128]; sh_steps = 705 };;

(* ------------------------------------------------------------------------- *)
(* The instance of mldsa87_pk_from_sk: pk (2592 bytes) in X19, the state at   *)
(* fp + 11744 (X0 and X22 point to it), tr at fp + 11584, and the registers   *)
(* X26 and X27 (two check flags), whose OR is put in X13 in the tail. The     *)
(* result of the comparison of t0 has been computed before the region.       *)
(* ------------------------------------------------------------------------- *)

let KG_SHAKE87_INST =
  { sh_fn = "mldsa87_pk_from_sk"; sh_start = "in_shake256_part3";
    sh_stop = "in_shake256_part4_end";
    sh_pklen = 2592; sh_a = 11744; sh_t = 11584;
    sh_vars = "(r26:int64) (r27:int64)";
    sh_pre = "read X0 s = st /\\
              read X22 s = st /\\
              read X26 s = r26 /\\ read X27 s = r27 /\\
              read Q17 s = word 0 /\\";
    sh_post = "read X8 s = st /\\
               read X13 s = word_zx(word_or (word_zx r26:int32)
                                            (word_zx r27:int32)) /\\";
    sh_reads = ""; sh_mods = "X18; X30";
    sh_calls = [70;134;198;263;335;407;479;551;623;695;767;839;911;983;1055;
                1127;1199;1271;1343;1359];
    sh_last_bytes = (8--15) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [8;128]; sh_steps = 1384 };;

(* ------------------------------------------------------------------------- *)
(* The instance of mldsa65_pk_from_sk: pk (1952 bytes) in X19, the state at   *)
(* fp + 8864 (X0 and X20 point to it), tr at fp + 8704, and the registers     *)
(* X21, X22, X27 and X28 (four check flags), whose ORs in pairs are put in    *)
(* X11 and X12 in the tail. The result of the comparison of t0 has been       *)
(* computed before the region.                                                *)
(* ------------------------------------------------------------------------- *)

let KG_SHAKE65_INST =
  { sh_fn = "mldsa65_pk_from_sk"; sh_start = "in_shake256_part3";
    sh_stop = "in_shake256_part5_end";
    sh_pklen = 1952; sh_a = 8864; sh_t = 8704;
    sh_vars = "(r21:int64) (r22:int64) (r27:int64) (r28:int64)";
    sh_pre = "read X0 s = st /\\
              read X20 s = st /\\
              read X21 s = r21 /\\ read X22 s = r22 /\\
              read X27 s = r27 /\\ read X28 s = r28 /\\
              read Q17 s = word 0 /\\";
    sh_post = "read X8 s = st /\\
               read X11 s = word_zx(word_or (word_zx r28:int32)
                                            (word_zx r22:int32)) /\\
               read X12 s = word_zx(word_or (word_zx r21:int32)
                                            (word_zx r27:int32)) /\\";
    sh_reads = ""; sh_mods = "X18; X30";
    sh_calls = [70;134;198;263;335;407;479;551;623;695;767;839;911;983;1007];
    sh_last_bytes = (48--55) @ (128--135); sh_last_chunks = [0;16;32];
    sh_pk128 = [1904;1920;1936]; sh_split = [0;16;32]; sh_rebuild = [48;128];
    sh_steps = 1033 };;
