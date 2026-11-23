(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the constant-time and memory safety proofs of mlkem_gen_matrix  *)
(* (x86/mlkem_native/asm/mlkem_gen_matrix.S): its events depend on rho,      *)
(* through the rejection sampling, so the proofs follow the lanes of the     *)
(* matrix as the correctness proofs do, with the theorems that are           *)
(* correctness and safety in one ("FULL") for the Keccak permutations and    *)
(* the sampling, and only the safety of the rest (the hash jobs, the noise,  *)
(* mlkem_unpack), except for the digest of job 0 in decapsulation, H(ek),    *)
(* whose caller branches on it. As arm/proofs/utils/mlkem_native2_gm_safe.ml *)
(* for AArch64.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/asm/mlkem_gen_matrix.ml";;
needs "x86/proofs/utils/mlkem_native2_safety.ml";;
needs "x86/proofs/utils/mlkem_native2_keccak_full.ml";;
needs "x86/proofs/utils/mlkem_native2_rej_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The FULL theorem of mlkem_rej_uniform_alt_VARIABLE_TIME in the forms of   *)
(* the sampling of a matrix polynomial: from the three blocks in its buffer, *)
(* and from a further block in its lane.                                     *)
(* ------------------------------------------------------------------------- *)

let rej_full_post_tac =
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `wordlist_from_memory(a,n) s = l`) o concl)) THEN
  MATCH_ACCEPT_TAC WORDLIST_FROM_MEMORY_BYTES16_NUM;;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES = prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer returnaddress.
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,val buflen); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist /\
                read (memory :> bytes(res,2 * val n)) s =
                num_of_wordlist curlist /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (C_RETURN s =
                 word(LENGTH(SUB_LIST (0,256)
                   (APPEND curlist (FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word) inlist))))) /\
                 read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                   (APPEND curlist (FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word) inlist)))))) s =
                 num_of_wordlist(SUB_LIST (0,256)
                   (APPEND curlist (FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word) inlist))))) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 32),40]
                       [word_sub stackpointer (word 32),32; res,512]))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL THEN
  EXISTS_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                int64->int64->(uarch_event)list` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
    (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8; LENGTH_MLKEM_REJ_UNIFORM_TABLE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
                 `val(buflen:int64)`; `inlist:(12 word)list`]
    (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`res:int64`; `val(n:int64)`; `2 * val(n:int64)`;
                 `curlist:int16 list`]
    (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN rej_full_post_tac);;

let MLKEM_REJ_UNIFORM_BUF_OUT_FULL = prove
 (`exists f_events.
     forall e res buf table b pc stackpointer returnaddress.
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,504); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,504); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; word 0; buf; word 504; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,504)) s =
                num_of_bytelist(list_of_seq (shake128 b) 504) /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (C_RETURN s = word(LENGTH(mlkem_rej_out b 3)) /\
                 read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b 3)))
                      s =
                 num_of_wordlist(mlkem_rej_out b 3)) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res buf table b pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,504; table,4096;
                        word_sub stackpointer (word 32),40]
                       [word_sub stackpointer (word 32),32; res,512]))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES THEN
  EXISTS_TAC
   `\(res:int64) (buf:int64) (table:int64) (b:byte list) (pc:num)
     (sp:int64) (ra:int64).
      (f:int64->int64->int64->int64->int64->(12 word)list->num->
          int64->int64->(uarch_event)list)
       res (word 0) buf (word 504) table
       (wordlist_of_num 336
          (num_of_bytelist(list_of_seq (shake128 b) 504))) pc sp ra` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`e:(uarch_event)list`; `res:int64`; `word 0:int64`; `buf:int64`;
    `word 504:int64`; `table:int64`; `[]:int16 list`;
    `wordlist_of_num 336
       (num_of_bytelist(list_of_seq (shake128 b) 504)):(12 word)list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; LENGTH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `8 * 504 = 12 * 336`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM MLKEM_REJ_OUT_BUF]);;

let MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL = prove
 (`exists f_events.
     forall e res buf table b m pc stackpointer returnaddress.
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,168); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,168); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; word(LENGTH(mlkem_rej_out b m)); buf;
                             word 168; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,168)) s =
                num_of_bytelist
                 (list_of_seq (\j. shake128 b (168 * m + j)) 168) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b m))) s =
                num_of_wordlist(mlkem_rej_out b m) /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (C_RETURN s = word(LENGTH(mlkem_rej_out b (m + 1))) /\
                 read (memory :>
                       bytes(res,2 * LENGTH(mlkem_rej_out b (m + 1)))) s =
                 num_of_wordlist(mlkem_rej_out b (m + 1))) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res buf table b m pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,168; table,4096;
                        word_sub stackpointer (word 32),40]
                       [word_sub stackpointer (word 32),32; res,512]))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES THEN
  EXISTS_TAC
   `\(res:int64) (buf:int64) (table:int64) (b:byte list) (m:num) (pc:num)
     (sp:int64) (ra:int64).
      (f:int64->int64->int64->int64->int64->(12 word)list->num->
          int64->int64->(uarch_event)list)
       res (word(LENGTH(mlkem_rej_out b m))) buf (word 168) table
       (wordlist_of_num 112
          (num_of_bytelist
            (list_of_seq (\j. shake128 b (168 * m + j)) 168))) pc sp ra` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`e:(uarch_event)list`; `res:int64`;
    `word(LENGTH(mlkem_rej_out b m)):int64`; `buf:int64`;
    `word 168:int64`; `table:int64`; `mlkem_rej_out b m`;
    `wordlist_of_num 112
       (num_of_bytelist(list_of_seq (\j. shake128 b (168 * m + j)) 168)):
     (12 word)list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b m)):int64) =
                LENGTH(mlkem_rej_out b m)` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`b:byte list`; `m:num`] LENGTH_MLKEM_REJ_OUT_LE) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; LENGTH_MLKEM_REJ_OUT_LE] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `8 * 168 = 12 * 112`] THEN
  REWRITE_TAC[MLKEM_REJ_OUT_BLOCK]);;

(* ------------------------------------------------------------------------- *)
(* The safety of mlkem_unpack with its frame, as a callee needs it.          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_UNPACK_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
    forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mlkem_unpack_tmc) (a,512) /\
        nonoverlapping (stackpointer,8) (a,512)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_unpack_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a pc stackpointer returnaddress /\
                      memaccess_inbounds e2 [a,512; stackpointer,8]
                                            [a,512; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_unpack_tmc MLKEM_UNPACK_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_UNPACK_SUBROUTINE_SAFE_FRAMED =
  ADD_IBT_RULE MLKEM_UNPACK_NOIBT_SUBROUTINE_SAFE_FRAMED;;

(* ------------------------------------------------------------------------- *)
(* The sampling of a matrix polynomial as one step, as in                    *)
(* MLKEM_GEN_MATRIX_SAMPLEPOLY, with its events a function of the seed b:    *)
(* those of the three blocks in the buffer and then of each further block,   *)
(* mlkem_rej_blocks b - 3 of them, and of mlkem_unpack.                      *)
(* ------------------------------------------------------------------------- *)

let gm_samplepoly_safe_tm =
  subst [mk_small_numeral(gm_pc "rejloop" 0),`pc0:num`;
         mk_small_numeral(gm_pc "rejloop" 148),`pc1:num`]
 `exists f_events.
   forall e b (A:1600 word) a c idx l stackpointer pc.
     mlkem_samplentt_terminates b /\
     (!t. num_of_bytelist(list_of_seq (\j. shake128 b (168 * t + j)) 168) =
          val(keccak_squeeze (t + 1) A) MOD 2 EXP 1344) /\
     l < 4 /\ idx + l < 16 /\ aligned 32 a /\
     ALL (nonoverlapping (stackpointer,3072))
         [(word pc,mlkem_native2_image_size);
          (word_add a (word(512 * (idx + l))),512); (c,6048)] /\
     ALL (nonoverlapping (word_add a (word(512 * (idx + l))),512))
         [(word pc,mlkem_native2_image_size); (c,6048)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + pc0) /\
               read RSP s = word_add stackpointer (word 40) /\
               read RBX s = a /\ read R15 s = c /\
               read R12 s = word idx /\ read R14 s = word l /\
               read (memory :> bytes(word_add stackpointer
                                      (word(840 + 504 * l)),504)) s =
               num_of_bytelist(list_of_seq (shake128 b) 504) /\
               read (memory :> bytes(word_add stackpointer
                                      (word(40 + 200 * l)),200)) s =
               val(keccak_squeeze 3 A) /\
               read (memory :> bytes(word_add c (word 1952),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read events s = e)
          (\s. read RIP s = word(pc + pc1) /\
               read RSP s = word_add stackpointer (word 40) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events b a c idx l stackpointer pc /\
                  memaccess_inbounds e2
                   [word_add a (word(512 * (idx + l))),512; c,6048;
                    word(pc + sha3_keccak_f1600_alt2_rotations),384;
                    stackpointer,3072]
                   [word_add a (word(512 * (idx + l))),512;
                    stackpointer,3072]))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_add a (word(512 * (idx + l))),512);
                      memory :> bytes(word_add stackpointer
                                       (word(40 + 200 * l)),200);
                      memory :> bytes(word_add stackpointer (word 3024),8);
                      memory :> bytes(stackpointer,40)])`;;

let gsp_vars = [`b:byte list`; `a:int64`; `c:int64`; `idx:num`; `l:num`;
                `stackpointer:int64`; `pc:num`];;

(*** A call in the sampling by its theorem with the label, at the new state
 *** k, the events in the variables vars
 ***)

let GM_SAFE_CALL_TAC vars label (off,mc) ilist k =
  NATIVE2_SAFE_THM_TAC MLKEM_GEN_MATRIX_EXEC vars label (off,mc) I ilist
    (k-1);;

let MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE = prove
 (gm_samplepoly_safe_tm,
  let NORM_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `val(word l:int64) = l`;
      ASSUME `val(word_mul (word l) (word 504):int64) = 504 * l`;
      ASSUME `val(word_mul (word l) (word 200):int64) = 200 * l`;
      ASSUME `val(word_shl (word_add (word idx) (word l)) 9:int64) =
              512 * (idx + l)`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_RULE
       `word_add (word_add (x:int64) (word 40)) (word (504 * l + 800)) =
        word_add x (word(840 + 504 * l))`;
      WORD_RULE
       `word_add (word_add (x:int64) (word 40)) (word (200 * l)) =
        word_add x (word(40 + 200 * l))`]) in
  let REJ0_TAC =
    GM_SAFE_CALL_TAC gsp_vars "H_REJ0"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `read RDX s`; `read R8 s`;
       `b:byte list`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @
      return_args) 10 in
  let UNPACK_TAC vars k =
    GM_SAFE_CALL_TAC vars "H_UNPACK" (layout "mlkem_unpack",mlkem_unpack_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `pc + mlkem_unpack`] @
      return_args) k in
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BUF_OUT_FULL "H_REJ0" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL "H_REJ1" THEN
  ASSUME_CALLEE_TAILED_TAC SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_F1600 "H_K1" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_UNPACK_SUBROUTINE_SAFE_FRAMED "H_UNPACK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(b:byte list) (a:int64) (c:int64) (idx:num) (l:num)
     (stackpointer:int64) (pc:num).
      if mlkem_rej_blocks b - 3 = 0
      then f_ev_skip b a c idx l stackpointer pc
      else APPEND (f_ev_exit b a c idx l stackpointer pc)
             (APPEND (ENUMERATEL (mlkem_rej_blocks b - 3)
                       (\i. f_ev_loop b a c idx l stackpointer pc i))
                     (f_ev_enter b a c idx l stackpointer pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  SUBGOAL_THEN `aligned 32 (word_add a (word(512 * (idx + l))):int64)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `512 * n = 32 * (16 * n)`] THEN
    ASM_SIMP_TAC[ALIGNED_BLOCK];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word l:int64) = l /\
    val(word_mul (word l) (word 504):int64) = 504 * l /\
    val(word_mul (word l) (word 200):int64) = 200 * l /\
    val(word_shl (word_add (word idx) (word l)) 9:int64) = 512 * (idx + l)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD; WORD_SHL_WORD; VAL_WORD;
                DIMINDEX_64] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o snd) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC]);
    ALL_TAC] THEN
  ASM_CASES_TAC `mlkem_rej_blocks b - 3 = 0` THEN ASM_REWRITE_TAC[] THENL
   [(*** No more blocks: the three in the buffer suffice ***)
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) = 256` ASSUME_TAC THENL
     [SUBGOAL_THEN `mlkem_rej_blocks b = 3` (SUBST1_TAC o SYM) THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS]];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `LENGTH(mlkem_rej_out b 3) = 256`]) THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--16) THEN NORM_TAC THEN
    UNPACK_TAC gsp_vars 17 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `mlkem_rej_blocks b - 3`
   (gm_pc_tm(gm_pc "rejloop" 54)) (gm_pc_tm(gm_pc "rejloop" 131))
   (mk_abs(`i:num`,samplepoly_inv `3 + i`)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** The buffer, and the test the first time ***)

    REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) < 256` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b 3)):int64) =
                  LENGTH(mlkem_rej_out b 3)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ENUMERATEL; APPEND] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: another block from the lane, its fields, the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * (idx + l))),
                      2 * LENGTH(mlkem_rej_out b (3 + i)))
                     (stackpointer:int64,3072)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(LENGTH(mlkem_rej_out b ((3 + i) + 1)) < 256 <=>
       i + 1 < mlkem_rej_blocks b - 3) /\
      val(word(LENGTH(mlkem_rej_out b ((3 + i) + 1))):int64) =
      LENGTH(mlkem_rej_out b ((3 + i) + 1))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_CASES_TAC `i + 1 < mlkem_rej_blocks b - 3` THEN
        ASM_REWRITE_TAC[NOT_LT] THENL
         [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          SUBGOAL_THEN `(3 + i) + 1 = mlkem_rej_blocks b` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS]] THEN
          ARITH_TAC];
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        MP_TAC(SPECL [`b:byte list`; `(3 + i) + 1`]
                     LENGTH_MLKEM_REJ_OUT_LE) THEN
        ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--5) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(40 + 200 * l)):int64` 5 THEN
    RC_TAC `c:int64` 5 THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_K1"
     (0,mlkem_native2_image_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
       `keccak_squeeze (3 + i) (A:1600 word)`; `pc:num`] @ return_args) 6 THEN
    FROM_WBYTES_TAC 6 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (7--15) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(40 + 200 * l)),168))
           s15 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + i) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(40 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + i)
                                       (A:1600 word)))`;
                    `s15:x86state`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_REJ1"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `read RDX s`; `read R8 s`;
       `b:byte list`; `3 + i`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @
      return_args) 16 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (17--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `3 + i + 1 = (3 + i) + 1`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    (fun gl -> allowed_vars_e := `i:num` :: !allowed_vars_e; ALL_TAC gl) THEN
    REWRITE_TAC[GSYM ADD1; ENUMERATEL] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit, with the 256 coefficients, and mlkem_unpack ***)

    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--4) THEN NORM_TAC THEN
    UNPACK_TAC gsp_vars 5 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One block of a hash job absorbed into its lane, with the events depending *)
(* only on the addresses and the lengths: a whole block, or the last t bytes *)
(* and the padding.                                                          *)
(* ------------------------------------------------------------------------- *)

let gm_absorb_full_safe_tm j ds =
  let lane = 400 + 200 * j and st = 2816 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 18 + 124 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 124),`pc1:num`;
         ns ds,`ds:num`]
  `exists f_events.
   forall e n inp i frm pc.
    n < 2 EXP 63 /\ 136 * (i + 1) <= n /\
    ALL (nonoverlapping (word_add frm (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    ALL (nonoverlapping (word_add frm (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    nonoverlapping (word_add frm (word lane),200) (word_add frm (word st),24)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + pc0) /\
          read RSP s = frm /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * i)) /\
          read (memory :> bytes64(word_add frm (word st8))) s =
          word(n - 136 * i) /\
          read (memory :> bytes64(word_add frm (word st16))) s = word ds /\
          read events s = e)
     (\s. read RIP s = word(pc + pc1) /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * (i + 1))) /\
          read (memory :> bytes64(word_add frm (word st8))) s =
          word(n - 136 * (i + 1)) /\
          (exists e2.
             read events s = APPEND e2 e /\
             e2 = f_events inp i frm pc /\
             memaccess_inbounds e2
              [inp,n; word_add frm (word lane),200;
               word_add frm (word st),24]
              [word_add frm (word lane),200; word_add frm (word st),16]))
     (MAYCHANGE [RIP; RAX; RCX; RDX; RDI; R8; R9; R10; R11] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add frm (word st),16);
                 memory :> bytes(word_add frm (word lane),200)])`;;

let GM_ABSORB_FULL_SAFE_PROOF_TAC =
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word(n - 136 * i):int64) = n - 136 * i /\
    ~(ival(word(n - 136 * i):int64) < &0) /\
    ~(n - 136 * i < 136) /\
    136 <= n - 136 * i`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN REWRITE_TAC[BIT_VAL] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ r /\ t ==> p /\ q /\ r /\ t`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `n < 2 EXP 63` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[DIV_LT; ARITH_RULE `x < 2 EXP 63 ==> x - y < 2 EXP 63`;
               ASSUME `n < 2 EXP 63`] THEN
      CONV_TAC NUM_REDUCE_CONV;
      UNDISCH_TAC `136 * (i + 1) <= n` THEN ARITH_TAC;
      UNDISCH_TAC `136 * (i + 1) <= n` THEN ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE [ASSUME `~(n - 136 * i < 136)`]) THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (13--118) THEN
  RULE_ASSUM_TAC(REWRITE_RULE [ASSUME `~(n - 136 * i < 136)`]) THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (119--122) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `n - 136 * i = (n - 136 * (i + 1)) + 136` SUBST1_TAC THENL
     [UNDISCH_TAC `136 * (i + 1) <= n` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let gm_absorb_last_safe_tm j t ds =
  let lane = 400 + 200 * j and st = 2816 + 32 * j
  and pc0 = gm_pc "noiseinit_done" 18 + 124 * j in
  let ns = mk_small_numeral in
  subst [ns lane,`lane:num`; ns st,`st:num`; ns (st + 8),`st8:num`;
         ns (st + 16),`st16:num`; ns pc0,`pc0:num`; ns (pc0 + 124),`pc1:num`;
         ns t,`t:num`; ns ds,`ds:num`]
  `exists f_events.
   forall e n inp q frm pc.
    n = 136 * q + t /\ n < 2 EXP 63 /\
    ALL (nonoverlapping (word_add frm (word lane),200))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    ALL (nonoverlapping (word_add frm (word st),24))
        [(word pc,mlkem_native2_image_size); (inp,n)] /\
    nonoverlapping (word_add frm (word lane),200) (word_add frm (word st),24)
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + pc0) /\
          read RSP s = frm /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * q)) /\
          read (memory :> bytes64(word_add frm (word st8))) s = word t /\
          read (memory :> bytes64(word_add frm (word st16))) s = word ds /\
          read events s = e)
     (\s. read RIP s = word(pc + pc1) /\
          read (memory :> bytes64(word_add frm (word st))) s =
          word_add inp (word(136 * q + t)) /\
          read (memory :> bytes64(word_add frm (word st8))) s =
          word 18446744073709551615 /\
          (exists e2.
             read events s = APPEND e2 e /\
             e2 = f_events inp q frm pc /\
             memaccess_inbounds e2
              [inp,n; word_add frm (word lane),200;
               word_add frm (word st),24]
              [word_add frm (word lane),200; word_add frm (word st),16]))
     (MAYCHANGE [RIP; RAX; RCX; RDX; RDI; R8; R9; R10; R11] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add frm (word st),16);
                 memory :> bytes(word_add frm (word lane),200)])`;;

let GM_ABSORB_LAST_SAFE_PROOF_TAC t =
  let nsteps = 15 + 6 * (t / 8) + 7 in
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--nsteps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the Keccak state at the end, as in GM_ZERO_END, with its   *)
(* events.                                                                   *)
(* ------------------------------------------------------------------------- *)

let GM_ZERO_END_SAFE = prove
 (`exists f_events.
     forall e stackpointer pc.
       nonoverlapping (stackpointer,800) (word pc,mlkem_native2_image_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_gen_matrix_end) /\
                 read RSP s = stackpointer /\
                 read events s = e)
            (\s. read RIP s = word(pc + mlkem_gen_matrix_zerodone) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events stackpointer pc /\
                    memaccess_inbounds e2
                     [stackpointer,800] [stackpointer,800]))
            (MAYCHANGE [RIP; RDI; RCX] ,, MAYCHANGE [ZMM0] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(stackpointer,800)])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(stackpointer:int64) (pc:num).
      APPEND (f_ev_epil stackpointer pc)
             (APPEND (ENUMERATEL 6 (\i. f_ev_loop stackpointer pc i))
                     (f_ev_prol stackpointer pc)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + mlkem_gen_matrix_zeroloop`
   (gm_pc_tm(gm_pc "zeroloop" 30))
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(6 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC (1--7) THEN
    ASM_SIMP_TAC[GM_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC [1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The instances of the absorb lemmas for the jobs of the API: job 1, H(pk)  *)
(* in encapsulation and J(z || c) in decapsulation (job 0 is only used in    *)
(* decapsulation, in the FULL form below).                                   *)
(* ------------------------------------------------------------------------- *)

let gm_absorb_full_safe_ths =
  map (fun (j,ds) ->
         (j,ds),time prove(gm_absorb_full_safe_tm j ds,
                           GM_ABSORB_FULL_SAFE_PROOF_TAC))
      [1,6; 1,31];;

let gm_absorb_last_safe_ths =
  map (fun (j,t,ds) ->
         (j,t,ds),time prove(gm_absorb_last_safe_tm j t ds,
                             GM_ABSORB_LAST_SAFE_PROOF_TAC t))
      [1,120,6; 1,96,6; 1,72,6; 1,120,31; 1,32,31; 1,104,31];;

let gm_af_label j ds = "H_AF_"^string_of_int j^"_"^string_of_int ds;;
let gm_al_label j t ds =
  "H_AL_"^string_of_int j^"_"^string_of_int t^"_"^string_of_int ds;;

(* ------------------------------------------------------------------------- *)
(* For the configurations of decapsulation, the absorbing of job 0 (ek, for  *)
(* H(ek)) with its result and its events: the absorb lemmas of the           *)
(* correctness proof in FULL form.                                           *)
(* ------------------------------------------------------------------------- *)

let gm_absorb_full_full_tm j ds =
  let lane = 400 + 200 * j and st = 2816 + 32 * j in
  let ns = mk_small_numeral in
  let la = vsubst [ns lane,`n:num`] `word_add (frm:int64) (word n)`
  and sa = vsubst [ns st,`n:num`] `word_add (frm:int64) (word n)` in
  full_tm_of (gm_absorb_full_tm j ds)
   [`inp:int64`; `i:num`; `frm:int64`; `pc:num`]
   [`inp:int64,LENGTH(m:byte list)`; mk_pair(la,`200`); mk_pair(sa,`24`)]
   [mk_pair(la,`200`); mk_pair(sa,`16`)];;

let gm_absorb_last_full_tm j t ds =
  let lane = 400 + 200 * j and st = 2816 + 32 * j in
  let ns = mk_small_numeral in
  let la = vsubst [ns lane,`n:num`] `word_add (frm:int64) (word n)`
  and sa = vsubst [ns st,`n:num`] `word_add (frm:int64) (word n)` in
  full_tm_of (gm_absorb_last_tm j t ds)
   [`inp:int64`; `q:num`; `frm:int64`; `pc:num`]
   [`inp:int64,LENGTH(m:byte list)`; mk_pair(la,`200`); mk_pair(sa,`24`)]
   [mk_pair(la,`200`); mk_pair(sa,`16`)];;

let GM_ABSORB_FULL_FULL_PROOF_TAC j ds =
  META_EXISTS_TAC THEN
  GM_ABSORB_FULL_TAC (400 + 200 * j) ds THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    SUBGOAL_THEN
     `LENGTH(m:byte list) - 136 * i = (LENGTH m - 136 * (i + 1)) + 136`
    SUBST1_TAC THENL
     [UNDISCH_TAC `136 * (i + 1) <= LENGTH(m:byte list)` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    SUBGOAL_THEN (subst [mk_small_numeral ds,`ds:num`]
     `(keccak_padded 136 ds m DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136) =
      B`)
    SUBST1_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[keccak_padded] THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM READ_MEMORY_WBYTES_1600; READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `B:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let GM_ABSORB_LAST_FULL_PROOF_TAC j t ds =
  let w = t / 8 in
  let lane = 400 + 200 * j in
  let lanetm = mk_comb(`word_add (frm:int64)`,
                       mk_comb(`word:num->int64`,mk_small_numeral lane)) in
  let nsteps1 = 15 + 6 * w in
  let tn = mk_small_numeral t and wn = mk_small_numeral w
  and dsn = mk_small_numeral ds in
  let stv n = mk_var("s"^string_of_int n,`:x86state`) in
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (subst [dsn,`ds:num`]
   `A = keccak_absorb 136 (keccak_padded 136 ds m) q`) THEN
  ABBREV_TAC (subst [tn,`t:num`]
   `L = (num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD 2 EXP (8 * t)`) THEN

  (*** The lanes of the state after the last words are XORed in ***)

  SUBGOAL_THEN (subst [wn,`w:num`]
   `!j. j < 25
        ==> word_subword (word_xor (A:1600 word) (word L)) (64 * j,64):int64 =
            if j < w
            then word_xor (word_subword A (64 * j,64))
                  (word((num_of_bytelist m DIV
                         2 EXP (8 * (136 * q + 8 * j))) MOD 2 EXP 64))
            else word_subword A (64 * j,64)`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `L:num`; wn; `j:num`] KECCAK_XOR_LANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) DIV_MOD_EXP_LOW o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC (subst [wn,`w:num`] `j < w`) THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state and the words of the message ***)

  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
    REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] o
    check (can (term_match [`frm:int64`]
      (subst [lanetm,`l:int64`]
        `read (memory :> bytes(l,200)) s = val(A:1600 word)`)) o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN (subst [wn,`w:num`]
   `!j. j < w
        ==> read (memory :> bytes64(word_add inp (word(136 * q + 8 * j)))) s0 =
            word((num_of_bytelist m DIV 2 EXP (8 * (136 * q + 8 * j))) MOD
                 2 EXP 64)`)
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN
    EXISTS_TAC `LENGTH(m:byte list)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (subst [wn,`w:num`] `j < w`) THEN ARITH_TAC;
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC] THEN
  W(fun (asl,w) ->
    let ths = filter (fun th ->
      can (term_match [`inp:int64`]
            `read (memory :> bytes64 (word_add inp (word(n + k)))) s =
             (y:int64)`) (concl th)) (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[WORD_ADD_SPLIT_OFFSET]) ths) THEN

  (*** The XOR of the last words into the lane ***)

  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--nsteps1) THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; stv nsteps1,`s:x86state`]
    `read (memory :> wbytes l) s = word_xor (A:1600 word) (word L)`)
  MP_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `L:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The domain byte at byte t ***)

  REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC tn th) (ARITH_RULE(subst [tn,`t:num`] `t < 200`)))) THEN
    ASSUME_TAC(RESTRICT_RULE tn th)) THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+1)--(nsteps1+3)) THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral lane,`l:num`; stv(nsteps1+3),`s:x86state`;
           tn,`t:num`; dsn,`ds:num`]
    `!j. j < 200
         ==> read (memory :> bytes8(word_add frm (word(l + j)))) s =
             word_subword (word_xor (word_xor (A:1600 word) (word L))
                                    (word(2 EXP (8 * t) * ds))) (8 * j,8)`)
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE(subst [dsn,`ds:num`] `ds < 256`);
                 ARITH_RULE(subst [tn,`t:num`] `t < 200`)] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The final bit at byte 135 ***)

  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC `135` th) (ARITH_RULE `135 < 200`))) THEN
    ASSUME_TAC(RESTRICT_RULE `135` th)) THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [nsteps1+4] THEN
  SUBGOAL_THEN
   (subst [lanetm,`l:int64`; stv(nsteps1+4),`s:x86state`;
           tn,`t:num`; dsn,`ds:num`]
    `read (memory :> bytes(l,200)) s =
     val(word_xor (word_xor (word_xor (A:1600 word) (word L))
                            (word(2 EXP (8 * t) * ds)))
                  (word(2 EXP (8 * 135) * 128)))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM READ_MEMORY_WBYTES_1600; READ_MEMORY_WBYTES_BYTES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `128 < 256 /\ 135 < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC ((nsteps1+5)--(nsteps1+7)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`136`; dsn; `m:byte list`] KECCAK_LAST_BLOCK_XOR) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN (subst [tn,`t:num`]
   `(136 * q + t) DIV 136 = q /\ (136 * q + t) MOD 136 = t`)
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC tn THEN ARITH_TAC;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `num_of_bytelist m DIV 2 EXP (8 * 136 * q) = L` SUBST1_TAC THENL
   [EXPAND_TAC "L" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    MP_TAC(ISPEC `m:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
    MATCH_MP_TAC(ARITH_RULE `a = b ==> x < a ==> x < b`) THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[];;

let gm_absorb_full_full_ths =
  map (fun (j,ds) ->
         (j,ds),GM_BLOCK_RULE(time prove(gm_absorb_full_full_tm j ds,
                                         GM_ABSORB_FULL_FULL_PROOF_TAC j ds)))
      [0,6];;

let gm_absorb_last_full_ths =
  map (fun (j,t,ds) ->
         (j,t,ds),
         GM_BLOCK_RULE(time prove(gm_absorb_last_full_tm j t ds,
                                  GM_ABSORB_LAST_FULL_PROOF_TAC j t ds)))
      [0,120,6; 0,96,6; 0,72,6];;

(* ------------------------------------------------------------------------- *)
(* The calls: the x4 permutation by its FULL theorem (the lanes whose states *)
(* are not followed, those of the hash jobs and the noise, taken as they     *)
(* are), the sampling of a matrix polynomial, a block of a hash job (job 0   *)
(* of decapsulation in FULL form), mlkem_cbd2 and mlkem_getnoise.            *)
(* ------------------------------------------------------------------------- *)

(*** The calls. A safety theorem is taken from the assumptions by its label
 *** and put back afterwards.
 ***)

let lane_state_opt a k gl =
  try let r = rand(concl(bytes_fact a 200 k gl)) in
      let f,x = dest_comb r in
      if name_of f = "val" && type_of x = `:1600 word` then Some x else None
  with Failure _ -> None;;

let GM_SAFE_SIM_TAC vars label th' th k gl =
  let vs = vars @ fev_vars gl in
  (X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
    (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,0,mlkem_native2_image_mc,
     FRESH_TAIL_RULE th') [] (k+1) THENL
   [EXISTS_E2_TAC (ref vs); LABEL_TAC label th]) gl;;

let GM_K4_SAFE_CALL_TAC vars k (asl,w as gl) =
  let a = find_read_fact `RDI` k gl and rc = find_read_fact `RSI` k gl
  and rho8 = find_read_fact `RDX` k gl and rho56 = find_read_fact `RCX` k gl in
  let sv = state_of k in
  let ads = map (addr_plus a) [0;200;400;600] in
  let lane ad =
    match lane_state_opt ad k gl with
      Some x -> TO_WBYTES_TAC ad k,x
    | None -> ALL_TAC,vsubst [ad,`a:int64`; sv,`s:x86state`]
                        `read (memory :> wbytes a) s:1600 word` in
  let ls = map lane ads in
  (RC_TAC rc k THEN RHO_TAC rho8 rho56 k THEN EVERY (map fst ls) THEN
   GM_SAFE_CALL_TAC vars "H_K4"
    (layout "sha3_keccak4_f1600_alt",sha3_keccak4_f1600_alt_mc)
    ([`e:(uarch_event)list`; `read RSI s`; `read RDI s`; `read RDX s`;
      `read RCX s`] @ map snd ls @ [`pc + sha3_keccak4_f1600_alt`] @
     return_args) (k+1) THEN
   FROM_WBYTES_TAC (k+1)) gl;;

let GM_SAMPLEPOLY_SAFE_TAC vars spoff k gl =
  let l = dest_small_numeral(rand(find_read_fact `R14` k gl))
  and idx = dest_small_numeral(rand(find_read_fact `R12` k gl)) in
  let lane = gm_lane_addr spoff l and buf = gm_buf_addr spoff l in
  let sv = state_of k in
  let st = rand(rand(concl(bytes_fact lane 200 k gl))) in
  let aa = rand(rand(rand st)) in
  let y = rand aa and x = rand(rator aa) and rho = rand(rator(rator aa)) in
  let b = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,rho),
                  mk_list([x;y],`:byte`)) in
  let bufth = MP_TAC(SPECL [rho; x; y; buf; sv] MLKEM_MATRIX_BUFFER) THEN
              CONV_TAC(LAND_CONV(KECCAK_SQUEEZE_NUM_CONV THENC
                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
              ASM_REWRITE_TAC[] THEN DISCH_TAC in
  let spth = SPECL [rho; x; y] MLKEM_MATRIX_SPONGE_BLOCK in
  let lth = find_asm (fun c ->
              c = mk_eq(mk_comb(`LENGTH:byte list->num`,rho),`32`)) gl in
  let term_th = MP (SPECL [rho; x; y] MLKEM_SAMPLENTT_TERMINATES_SEED) lth in
  (ASSUME_TAC term_th THEN bufth THEN
   MP_TAC spth THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   REMOVE_THEN "H_SP" (fun th ->
     let lemma = SPECL [`e:(uarch_event)list`; b; aa; `a:int64`; `c:int64`;
                        mk_small_numeral idx; mk_small_numeral l;
                        addr_plus `stackpointer:int64` (spoff - 40);
                        `pc:num`] th in
     let lemma' = CONV_RULE(ONCE_DEPTH_CONV KECCAK_SQUEEZE_NUM_CONV) lemma in
     MP_TAC lemma' THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     REWRITE_TAC[] THEN
     DISCH_THEN(fun th' -> GM_SAFE_SIM_TAC vars "H_SP" th' th k))) gl;;

let GM_ABSORB_SAFE_CALL_TAC vars lens spoff j k (asl,w as gl) =
  let st = gm_st spoff (2816 + 32 * j) in
  let rd a = rand(concl(bytes64_fact a k gl)) in
  let dsv = rd (addr_plus st 16) in
  if dsv = `word 0:int64` then X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [k+1] gl
  else
  let ds = dest_small_numeral(rand dsv) in
  let pv = rd st and r = dest_small_numeral(rand(rd (addr_plus st 8))) in
  let inp = word_base pv and len = assoc j lens in
  let ns = mk_small_numeral and sp = find_read_fact `RSP` k gl in
  let label,args =
    if r >= 136 then
      gm_af_label j ds,[ns len; inp; ns((len - r) / 136); sp; `pc:num`]
    else
      gm_al_label j r ds,[ns len; inp; ns(len / 136); sp; `pc:num`] in
  REMOVE_THEN label (fun th ->
    let th1 = SPECL (`e:(uarch_event)list` :: args) th in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
               (REWRITE_RULE[WORD_ADD_0] (CONV_RULE NUM_REDUCE_CONV th1)) in
    GM_SAFE_SIM_TAC vars label th2 th k) gl;;

let GM_GETNOISE_SAFE_CALL_TAC vars k gl =
  let v reg = mk_small_numeral(dest_small_numeral
                (rand(find_read_fact reg k gl))) in
  let sp = find_read_fact `RSP` k gl in
  let c = rand(concl(bytes64_fact (addr_plus sp 8) k gl)) in
  REMOVE_THEN "H_GETNOISE" (fun th ->
    let th1 = SPECL [`e:(uarch_event)list`; find_read_fact `RDI` k gl;
                     find_read_fact `RSI` k gl; v `RDX`; v `RCX`; v `R8`;
                     v `R9`; c; `pc:num`; sp;
                     rand(concl(bytes64_fact sp k gl))] th in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
               (REWRITE_RULE[ARITH_EQ] th1) in
    GM_SAFE_SIM_TAC vars "H_GETNOISE" th2 th k) gl;;

(*** The call of an absorb lemma of job j in FULL form: as in the
 *** correctness proof, with the state of the lane first put as
 *** keccak_absorb 136 P i, and the theorem taken from the assumptions
 ***)

let gm_aff_label j ds = "H_AFF_"^string_of_int j^"_"^string_of_int ds;;
let gm_alf_label j t ds =
  "H_ALF_"^string_of_int j^"_"^string_of_int t^"_"^string_of_int ds;;

let GM_ABSORB_FULL_CALL_TAC vars spoff j k (asl,w as gl) =
  let sv = state_of k in
  let st = gm_st spoff (2816 + 32 * j) in
  let rd a = rand(concl(bytes64_fact a k gl)) in
  let dsv = rd (addr_plus st 16) in
  if dsv = `word 0:int64` then X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [k+1] gl
  else
  let ds = dest_small_numeral(rand dsv) in
  let pv = rd st and r = dest_small_numeral(rand(rd (addr_plus st 8))) in
  let inp = word_base pv in
  let mth = find_asm (fun c ->
    try let a,n,s = dest_bytes_read(lhand c) in
        a = inp && s = sv && is_numeral n &&
        fst(dest_const(rator(rand c))) = "num_of_bytelist"
    with Failure _ -> false) gl in
  let _,ln,_ = dest_bytes_read(lhand(concl mth)) in
  let len = dest_small_numeral ln and m = rand(rand(concl mth)) in
  let lenth = find_asm (fun c ->
    try lhand c = mk_comb(`LENGTH:byte list->num`,m)
    with Failure _ -> false) gl in
  let lane = gm_lane_addr spoff (2 + j) in
  let p = list_mk_comb(`keccak_padded`,[`136`; mk_small_numeral ds; m]) in
  let i = if r >= 136 then (len - r) / 136 else len / 136 in
  let ka = list_mk_comb(`keccak_absorb`,[`136`; p; mk_small_numeral i]) in
  let lane_tac =
    if i = 0 then
      FIRST_X_ASSUM(fun th ->
        if concl th = vsubst [lane,`a:int64`; sv,`s:x86state`]
                       `read (memory :> bytes(a,200)) s = 0`
        then ASSUME_TAC(TRANS th (SYM(REWRITE_CONV[keccak_absorb; VAL_WORD_0]
                                       (mk_comb(`val:1600 word->num`,ka)))))
        else NO_TAC)
    else
      FIRST_X_ASSUM(fun th ->
        if lhand(concl th) = vsubst [lane,`a:int64`; sv,`s:x86state`]
                               `read (memory :> bytes(a,200)) s`
        then ASSUME_TAC(CONV_RULE(RAND_CONV
               (REWRITE_CONV[KECCAK_ABSORB_BLOCK_STEP] THENC
                NUM_REDUCE_CONV)) th)
        else NO_TAC) in
  let sp = find_read_fact `RSP` k gl in
  let label = if r >= 136 then gm_aff_label j ds else gm_alf_label j r ds in
  (lane_tac THEN
   REMOVE_THEN label (fun th ->
     let th1 = SPECL [`e:(uarch_event)list`; m; inp; mk_small_numeral i; sp;
                      `pc:num`] th in
     let th2 = REWRITE_RULE[WORD_ADD_0]
                (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[lenth] th1)) in
     let th3 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                th2 in
     GM_SAFE_SIM_TAC vars label th3 th k)) gl;;

(* ------------------------------------------------------------------------- *)
(* The proof of an instance with stack size n: the hooks (those of the       *)
(* correctness proof for the job and noise structures and the lanes of the   *)
(* matrix, and for job 0 of decapsulation its lane and digest), the          *)
(* variables of the events, the absorb lemmas the jobs need, the setup, the  *)
(* run and the discharge.                                                    *)
(* ------------------------------------------------------------------------- *)

(*** The hooks for the safety proof: the job and noise structures, the
 *** lanes of the matrix and their copies to the buffers (the others are
 *** not needed), and the calls
 ***)

let gm_safe_derive spoff =
  [gm_pc "nonoise" (-14), GM_MERGE_TAC `R9` [0];
   gm_pc "nonoise" 0, (fun k -> TRY(GM_SPLIT_TAC spoff [2880] k));
   gm_pc "nonoise" 8, GM_MERGE_TAC `R8` [0; 32];
   gm_pc "jobsdone" 0, (fun k -> TRY(GM_SPLIT_TAC spoff [2816; 2848] k));
   gm_pc "initloop" 133, GM_LANE_SPLIT_TAC 136;
   gm_pc "initloop" 140, GM_MATRIX_LANE_TAC;
   gm_pc "copyloop" 0, GM_COPY_LOAD_TAC;
   gm_pc "copyloop" 68, GM_COPY_STORE_TAC];;

let gm_safe_calls spoff lens vars =
  let exec = MLKEM_GEN_MATRIX_EXEC in
  [gm_pc "end" 0,
     NATIVE2_SAFE_THM_TAC exec vars "H_ZERO" (0,mlkem_native2_image_mc) I
      [`e:(uarch_event)list`; `read RSP s`; `pc:num`];
   layout "sha3_keccak4_f1600_alt", GM_K4_SAFE_CALL_TAC vars;
   gm_pc "rejloop" 0, GM_SAMPLEPOLY_SAFE_TAC vars spoff;
   gm_pc "noiseinit_done" 18, GM_ABSORB_SAFE_CALL_TAC vars lens spoff 0;
   gm_pc "noiseinit_done" 142, GM_ABSORB_SAFE_CALL_TAC vars lens spoff 1;
   layout "mlkem_cbd2",
     NATIVE2_SAFE_THM_TAC exec vars "H_CBD2"
      (layout "mlkem_cbd2",mlkem_cbd2_mc) I
      ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
        `pc + mlkem_cbd2`] @ return_args);
   layout "mlkem_getnoise",
     (fun k -> GM_SWAP_RDI_TAC k THEN GM_GETNOISE_SAFE_CALL_TAC vars k)];;

(*** The jobs of an instance (index, length, domain byte) from its
 *** statement, those with a nonzero domain byte
 ***)

let gm_jobs_of tm =
  let body = snd(strip_forall(snd(dest_exists tm))) in
  let ens = snd(dest_imp body) in
  let pre = el 1 (snd(strip_comb ens)) in
  let cs = conjuncts(snd(dest_abs pre)) in
  let field off =
    let lhs = vsubst [mk_small_numeral off,`off:num`]
      `read (memory :> bytes64 (word_add jobs (word off))) s` in
    try let c = find (fun c -> is_eq c && lhand c = lhs) cs in
        Some(dest_small_numeral(rand(rand c)))
    with Failure _ -> None in
  flat(map (fun j ->
    match field (8 + 32 * j),field (16 + 32 * j) with
      Some len,Some ds when ds <> 0 -> [j,len,ds]
    | _ -> []) [0; 1]);;

(*** The driver with the jobs in full (those whose message is kept) ***)

let gm_safe_params tm =
  let vars0 = tl(fst(strip_forall(snd(dest_exists tm)))) in
  let vars = filter (fun v -> type_of v <> `:byte list` ||
                              name_of v = "rho") vars0 in
  let full = flat(map (fun v ->
               if name_of v = "m0" then [0] else
               if name_of v = "m1" then [1] else []) vars0) in
  let jobs = gm_jobs_of tm in
  let lens = map (fun (j,len,_) -> j,len) jobs in
  let absorbs = flat(map (fun (j,len,ds) ->
    let t = len mod 136 in
    if mem j full then
      (if len >= 136
       then [gm_aff_label j ds,assoc (j,ds) gm_absorb_full_full_ths]
       else []) @
      [gm_alf_label j t ds,assoc (j,t,ds) gm_absorb_last_full_ths]
    else
      (if len >= 136
       then [gm_af_label j ds,assoc (j,ds) gm_absorb_full_safe_ths]
       else []) @
      [gm_al_label j t ds,assoc (j,t,ds) gm_absorb_last_safe_ths]) jobs) in
  vars,lens,absorbs,full;;

let gm_safe_derive_jobs spoff full =
  gm_safe_derive spoff @
  (if full = [] then [] else
   [gm_pc "outer" 0, (fun k -> TRY(GM_ZERO_LANES_TAC spoff k));
    gm_pc "nohash1" 65, GM_LANE256_TAC 400;
    gm_pc "nohash1" 78, GM_DIGEST_TAC 400]);;

let gm_safe_calls_jobs spoff lens vars full =
  let absorb j =
    if mem j full then GM_ABSORB_FULL_CALL_TAC vars spoff j
    else GM_ABSORB_SAFE_CALL_TAC vars lens spoff j in
  map (fun (off,tac) ->
         if off = gm_pc "noiseinit_done" 18 then off,absorb 0
         else if off = gm_pc "noiseinit_done" 142 then off,absorb 1
         else off,tac)
      (gm_safe_calls spoff lens vars);;

let GM_SAFE_SETUP_TAC n absorbs =
  ASSUME_CALLEE_TAILED_TAC GM_ZERO_END_SAFE "H_ZERO" THEN
  ASSUME_CALLEE_TAILED_TAC
    SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL_F1600 "H_K4" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE "H_SP" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED "H_CBD2" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_GETNOISE_SUBROUTINE_SAFE "H_GETNOISE" THEN
  MAP_EVERY (fun (l,th) -> ASSUME_CALLEE_TAILED_TAC th l) absorbs THEN
  META_EXISTS_TAC THEN
  REPEAT(W(fun (_,w) ->
    let v = fst(dest_forall w) in
    if fst(dest_var v) = "stackpointer" then NO_TAC else X_GEN_TAC v)) THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS;
              WORDLIST_FROM_MEMORY_RHO8; WORDLIST_FROM_MEMORY_RHO56] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun r -> ENSURES_PRESERVED_TAC
                (String.lowercase_ascii(fst(dest_const r))^"_init") r)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  ENSURES_INIT_TAC "s0" THEN
  GM_BYTES256_OF_32_TAC `rhop:int64` `num_of_bytelist(rho:byte list)`;;

let GM_SAFE_FINALE_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;

let GM_SAFE_INSTANCE_TAC n (asl,w as gl) =
  let vars,lens,absorbs,full = gm_safe_params w in
  let spoff = n - 3080 in
  (GM_SAFE_SETUP_TAC n absorbs THEN
   NATIVE2_SAFE_RUN_TAC MLKEM_GEN_MATRIX_EXEC (gm_safe_derive_jobs spoff full)
     (gm_safe_calls_jobs spoff lens vars full) 0 THEN
   GM_SAFE_FINALE_TAC) gl;;
