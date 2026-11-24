(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hash H of ML-KEM, SHA3-256 of FIPS 202, with the x1 Keccak            *)
(* permutation sha3_keccak_f1600_alt2, in the x86 mlkem_native2 image.       *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/sponge_spec.ml";;

(**** The function's code is x86/mlkem_native/asm/mlkem_hash_h.S. Its frame of
 **** 216 bytes below the four saved registers has the 200-byte state at the
 **** stack pointer, and the call of sha3_keccak_f1600_alt2 puts its return
 **** address below that, so the stack used is the 256 bytes below the
 **** return address. The digest is taken after the last permutation, at
 **** mlkem_hash_h_pad + 22, given the name mlkem_hash_h_digest here.
 ****)

let MLKEM_HASH_H_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem_hash_h"];;

let pc_plus name off =
  parse_term (Printf.sprintf "pc + %d" (layout name + off));;

install_layout ["mlkem_hash_h_digest",layout "mlkem_hash_h_pad" + 22];;

(* ------------------------------------------------------------------------- *)
(* One whole block of 136 bytes of the message m at inp, as for              *)
(* keccak_absorb on the padded message, from the test at the start of the    *)
(* loop back to it. Here stackpointer is the stack pointer of the function   *)
(* after its frame is made, where the state is. The 256-bit loads and stores *)
(* of the state and the message are given to the simulation as joins of      *)
(* their 64-bit lanes, and the stores are split back into lanes after it.    *)
(* The round constants are bytes in memory, which the simulation keeps,      *)
(* unlike wordlist_from_memory.                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_BLOCK_STMT =
  `!m inp c i pc stackpointer.
    LENGTH m < 2 EXP 64 /\ 136 * (i + 1) <= LENGTH m /\
    ALL (nonoverlapping (stackpointer,200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (stackpointer,200)]
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_block) /\
          read RSP s = stackpointer /\
          read RBP s = word_add inp (word(136 * i)) /\
          read R12 s = word(LENGTH m - 136 * i) /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          keccak_absorb 136 (keccak_padded 136 6 m) i)
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_block) /\
          read RSP s = stackpointer /\
          read RBP s = word_add inp (word(136 * (i + 1))) /\
          read R12 s = word(LENGTH m - 136 * (i + 1)) /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          keccak_absorb 136 (keccak_padded 136 6 m) (i + 1))
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [RBP; R12] ,,
      MAYCHANGE [memory :> bytes(stackpointer,200);
                 memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_HASH_H_BLOCK = assume_spec MLKEM_HASH_H_BLOCK_STMT;;

(* ------------------------------------------------------------------------- *)
(* The last t < 136 bytes of the message, after q whole blocks, from the     *)
(* exit of the loop above to the padding: first the t DIV 8 whole words,     *)
(* each XORed into a lane of the state A, then the t MOD 8 single bytes.     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_WORDS_STMT =
  `!m inp c pc stackpointer q t (A:1600 word).
    LENGTH(m:byte list) = 136 * q + t /\ t < 136 /\ LENGTH m < 2 EXP 64 /\
    ALL (nonoverlapping (stackpointer,200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (stackpointer,200)]
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_block) /\
          read RSP s = stackpointer /\
          read RBP s = word_add inp (word(136 * q)) /\
          read R12 s = word t /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s = A)
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_lastbytes) /\
          read RSP s = stackpointer /\
          read RDI s = word_add stackpointer (word(8 * t DIV 8)) /\
          read RBP s = word_add inp (word(136 * q + 8 * t DIV 8)) /\
          read R12 s = word t /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          word_xor A (word((num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD
                           2 EXP (64 * t DIV 8))))
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [RBP; R12] ,,
      MAYCHANGE [memory :> bytes(stackpointer,200);
                 memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_HASH_H_WORDS = assume_spec MLKEM_HASH_H_WORDS_STMT;;

let MLKEM_HASH_H_BYTES_STMT =
  `!m inp c pc stackpointer q t (A:1600 word).
    LENGTH(m:byte list) = 136 * q + t /\ t < 136 /\ LENGTH m < 2 EXP 64 /\
    ALL (nonoverlapping (stackpointer,200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (stackpointer,200)]
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_lastbytes) /\
          read RSP s = stackpointer /\
          read RDI s = word_add stackpointer (word(8 * t DIV 8)) /\
          read RBP s = word_add inp (word(136 * q + 8 * t DIV 8)) /\
          read R12 s = word t /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          word_xor A (word((num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD
                           2 EXP (64 * t DIV 8))))
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_pad) /\
          read RSP s = stackpointer /\
          read RDI s = word_add stackpointer (word t) /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          word_xor A (word(num_of_bytelist m DIV 2 EXP (8 * 136 * q))))
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [RBP; R12] ,,
      MAYCHANGE [memory :> bytes(stackpointer,200);
                 memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_HASH_H_BYTES = assume_spec MLKEM_HASH_H_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* The padding of the last block, the domain byte 0x06 at byte t and 0x80 at *)
(* byte 135 (the same byte if t = 135), and the permutation.                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_PAD_STMT =
  `!inp len c pc stackpointer t (A:1600 word) M.
    t < 136 /\
    ALL (nonoverlapping (stackpointer,200))
        [(word pc,mlkem_native2_image_size); (inp,len); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,mlkem_native2_image_size); (inp,len); (c,192);
         (stackpointer,200)]
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_pad) /\
          read RSP s = stackpointer /\
          read RDI s = word_add stackpointer (word t) /\
          read R13 s = c /\
          read (memory :> bytes(inp,len)) s = M /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s = A)
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_digest) /\
          read RSP s = stackpointer /\
          read R13 s = c /\
          read (memory :> bytes(inp,len)) s = M /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          keccak_f1600(word_xor (word_xor A (word(2 EXP (8 * t) * 6)))
                                (word(2 EXP (8 * 135) * 128))))
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [RBP; R12] ,,
      MAYCHANGE [memory :> bytes(stackpointer,200);
                 memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_HASH_H_PAD = assume_spec MLKEM_HASH_H_PAD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The last block as a whole, from the exit of the loop over whole blocks to *)
(* the state for the digest, which is that of KECCAK_SPONGE_BYTES.           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_TAIL_STMT =
  `!m inp c pc stackpointer.
    LENGTH m < 2 EXP 64 /\
    ALL (nonoverlapping (stackpointer,200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (stackpointer,200)]
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_block) /\
          read RSP s = stackpointer /\
          read RBP s = word_add inp (word(136 * LENGTH m DIV 136)) /\
          read R12 s = word(LENGTH m - 136 * LENGTH m DIV 136) /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_digest) /\
          read RSP s = stackpointer /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (word((keccak_padded 136 6 m DIV
                    2 EXP (8 * 136 * LENGTH m DIV 136)) MOD 2 EXP (8 * 136)))))
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [RBP; R12] ,,
      MAYCHANGE [memory :> bytes(stackpointer,200);
                 memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_HASH_H_TAIL = assume_spec MLKEM_HASH_H_TAIL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The whole absorption, from block i by induction on the blocks left, and   *)
(* from the zero state, without the code in the postcondition so that the    *)
(* proof below can use it as a step.                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_ABSORB_STMT =
  `!m inp c pc stackpointer i.
    LENGTH m < 2 EXP 64 /\
    i <= LENGTH m DIV 136 /\
    ALL (nonoverlapping (stackpointer,200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (stackpointer,200)]
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_block) /\
          read RSP s = stackpointer /\
          read RBP s = word_add inp (word(136 * i)) /\
          read R12 s = word(LENGTH m - 136 * i) /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          keccak_absorb 136 (keccak_padded 136 6 m) i)
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_digest) /\
          read RSP s = stackpointer /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (word((keccak_padded 136 6 m DIV
                    2 EXP (8 * 136 * LENGTH m DIV 136)) MOD 2 EXP (8 * 136)))))
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [RBP; R12] ,,
      MAYCHANGE [memory :> bytes(stackpointer,200);
                 memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_HASH_H_ABSORB = assume_spec MLKEM_HASH_H_ABSORB_STMT;;

let MLKEM_HASH_H_ABSORB_0_STMT =
  `!m inp c pc stackpointer.
    LENGTH m < 2 EXP 64 /\
    ALL (nonoverlapping (stackpointer,200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (stackpointer,200)]
    ==> ensures x86
     (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read RIP s = word(pc + mlkem_hash_h_block) /\
          read RSP s = stackpointer /\
          read RBP s = inp /\
          read R12 s = word(LENGTH m) /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          (word 0:1600 word))
     (\s. read RIP s = word(pc + mlkem_hash_h_digest) /\
          read RSP s = stackpointer /\
          read (memory :> wbytes stackpointer) s =
          keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (word((keccak_padded 136 6 m DIV
                    2 EXP (8 * 136 * LENGTH m DIV 136)) MOD 2 EXP (8 * 136)))))
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [RBP; R12] ,,
      MAYCHANGE [memory :> bytes(stackpointer,200);
                 memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLKEM_HASH_H_ABSORB_0 = assume_spec MLKEM_HASH_H_ABSORB_0_STMT;;

(*** The same with the state at stackpointer + 8, as in the function after
 *** its frame is made when stackpointer is the lowest address of its stack
 ***)

let MLKEM_HASH_H_ABSORB_0_AT =
  let th = SPECL [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
                  `word_add stackpointer (word 8):int64`]
                 MLKEM_HASH_H_ABSORB_0 in
  GENL [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
        `stackpointer:int64`]
   (REWRITE_RULE[WORD_RULE
     `word_sub (word_add x (word 8)) (word 8):int64 = x`] th);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the function: the 32 bytes of the result at out are        *)
(* sha3_256 of the message m at inp, given the round constants at c (in the  *)
(* constants block, which may be in the image). The stack is the 256 bytes   *)
(* below the return address.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out inp (m:byte list) c pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 256),256))
         [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
     ALL (nonoverlapping (out,32))
         [(word pc,mlkem_native2_image_size);
          (word_sub stackpointer (word 256),264)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem_hash_h) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [out; inp; word(LENGTH m); c] s /\
               read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
               wordlist_from_memory(c,24) s = round_constants)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes(out,32)) s = num_of_bytelist(sha3_256 m))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out,32);
                      memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* length of the message: those of the prologue and of each whole block, the *)
(* last block's whole words and single bytes, and the padding, the last      *)
(* permutation and the epilogue, with those of the permutations from the     *)
(* framed theorem for sha3_keccak_f1600_alt2 in the image.                   *)
(* ------------------------------------------------------------------------- *)

(*** The registers saved in the frame, part of every invariant ***)

let MLKEM_HASH_H_SAVED =
  `read (memory :> bytes64 (word_add stackpointer (word 248))) s = rbx_init /\
   read (memory :> bytes64 (word_add stackpointer (word 240))) s = rbp_init /\
   read (memory :> bytes64 (word_add stackpointer (word 232))) s = r12_init /\
   read (memory :> bytes64 (word_add stackpointer (word 224))) s = r13_init /\
   read (memory :> bytes64 (word_add stackpointer (word 256))) s =
   returnaddress`;;

let mlkem_hash_h_inv tm =
  mk_abs(`s:x86state`,mk_conj(tm,MLKEM_HASH_H_SAVED));;

let mlkem_hash_h_loop_inv tm =
  mk_abs(`i:num`,mk_abs(`s:x86state`,mk_conj(tm,MLKEM_HASH_H_SAVED)));;

(*** The call of sha3_keccak_f1600_alt2, its safety theorem as H_KECCAK ***)

let MLKEM_HASH_H_SAFE_CALL_TAC extra n =
  W(fun (asl,w) ->
    let fevs = filter (fun v -> String.length (name_of v) > 4 &&
                                String.sub (name_of v) 0 4 = "f_ev")
                      (frees w) in
    let vars =
      [`inp:int64`; `len:num`; `c:int64`; `out:int64`; `pc:num`;
       `stackpointer:int64`; `returnaddress:int64`] @ extra @ fevs in
    REMOVE_THEN "H_KECCAK" (fun safety_th ->
      X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mlkem_native2_image_mc,MLKEM_HASH_H_EXEC,0,
         mlkem_native2_image_mc,safety_th)
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
         `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] n THENL
       [EXISTS_E2_TAC (ref vars); LABEL_TAC "H_KECCAK" safety_th]));;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, but with a tactic to expand local     ***)
(*** abbreviations for the unification of the events, and the old events  ***)
(*** in the same association as the new for the memory accesses           ***)

let MLKEM_HASH_H_DISCHARGE_TAC unabbrev normalize =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [unabbrev THEN FULL_UNIFY_F_EVENTS_TAC;
    (if normalize then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND_NIL]) THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND_NIL]
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC];;

(*** The decrement of a loop counter, and the test after it ***)

let MLKEM_HASH_H_COUNTER_TAC =
  let pth = prove
   (`!n k. k < n /\ n < 2 EXP 64
           ==> word_sub (word(n - k)) (word 1):int64 = word(n - (k + 1)) /\
               (~(val(word(n - (k + 1)):int64) = 0) <=> k + 1 < n)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `n - k = (n - (k + 1)) + 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
      SUBGOAL_THEN `val(word(n - (k + 1)):int64) = n - (k + 1)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC]]) in
  fun n k ->
    MP_TAC(SPECL [n; k] pth) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ARITH_TAC]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC);;

let MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out inp len c pc stackpointer returnaddress.
       ALL (nonoverlapping (word_sub stackpointer (word 256),256))
           [(word pc,mlkem_native2_image_size); (inp,len); (c,192)] /\
       ALL (nonoverlapping (out,32))
           [(word pc,mlkem_native2_image_size);
            (word_sub stackpointer (word 256),264)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_hash_h) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; inp; word len; c] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events inp len c out pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [inp,len; c,192; out,32;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      word_sub stackpointer (word 256),264]
                     [out,32; word_sub stackpointer (word 256),256]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
