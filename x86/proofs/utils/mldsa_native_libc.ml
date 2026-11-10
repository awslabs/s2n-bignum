(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The contracts for the external functions called by mldsa-native's x86-64  *)
(* binary, and tactics for calls of them, as for AArch64 (see                *)
(* arm/proofs/utils/mldsa_native_libc.ml and the files it loads, whose       *)
(* contracts these are, for the x86 model).                                  *)
(*                                                                           *)
(* The binary calls the C library functions memset and memcpy and the        *)
(* function randombytes through its PLT and GOT (see                         *)
(* mldsa_native/README.md): the stub plt_g in the image jumps to the address *)
(* in the GOT slot got_g, which is outside the image. Their code is not part *)
(* of the image, so their behaviour is assumed, as a notional high-level     *)
(* contract for each of them. A contract states the behaviour of the         *)
(* function at an address f (which a caller reads from the GOT) in any state *)
(* where some region (ea,el) of memory, containing its code and any data it  *)
(* uses, has fixed contents ev; the callers require that region not to       *)
(* overlap anything they write, so that it is unchanged when they call the   *)
(* function. The function returns to the return address on the stack, may    *)
(* change the registers that the ABI allows it to, but no memory except its  *)
(* outputs; in particular it is assumed not to use the stack, apart from     *)
(* reading the return address. As the ABI requires on entry, the direction   *)
(* flag is clear. memset sets each of the len bytes at dst to the low byte   *)
(* of c (and memset_ret also returns dst, as the C standard says it does,    *)
(* which the code of mld_sig_unpack_hints uses), memcpy copies the len bytes *)
(* at src to dst, which must not overlap, and randombytes writes len bytes   *)
(* at buf, with no assumption about their values, and returns a status in    *)
(* RAX, again with no assumption about it.                                   *)
(*                                                                           *)
(* Each contract is for correctness, constant time and memory safety         *)
(* together, as the FULL theorems of the functions are: the events of a call *)
(* depend only on its arguments, the stack pointer and the return address,   *)
(* and it only reads its inputs, its return address and the region (ea,el)   *)
(* and only writes its outputs. For randombytes, whose results are not       *)
(* specified, the contract is the one for constant time and memory safety.   *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The contracts.                                                            *)
(* ------------------------------------------------------------------------- *)

let memset_full_contract = new_definition
 `memset_full_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e dst c len stackpointer returnaddress.
        nonoverlapping (dst,val len) (ea,el) /\
        nonoverlapping (dst,val len) (stackpointer,8)
        ==> ensures x86
             (\s. read RIP s = f /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [dst; c; len] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < val len
                       ==> read (memory :> bytes8(word_add dst (word i))) s =
                           word_zx c) /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events dst c len stackpointer returnaddress /\
                        memaccess_inbounds e2
                         [dst,val len; stackpointer,8; ea,el]
                         [dst,val len]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let memset_ret_full_contract = new_definition
 `memset_ret_full_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e dst c len stackpointer returnaddress.
        nonoverlapping (dst,val len) (ea,el) /\
        nonoverlapping (dst,val len) (stackpointer,8)
        ==> ensures x86
             (\s. read RIP s = f /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [dst; c; len] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = dst /\
                  (!i. i < val len
                       ==> read (memory :> bytes8(word_add dst (word i))) s =
                           word_zx c) /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events dst c len stackpointer returnaddress /\
                        memaccess_inbounds e2
                         [dst,val len; stackpointer,8; ea,el]
                         [dst,val len]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let memcpy_full_contract = new_definition
 `memcpy_full_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e dst src len x stackpointer returnaddress.
        nonoverlapping (dst,val len) (ea,el) /\
        nonoverlapping (dst,val len) (src,val len) /\
        nonoverlapping (dst,val len) (stackpointer,8)
        ==> ensures x86
             (\s. read RIP s = f /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [dst; src; len] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(src,val len)) s = x /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(dst,val len)) s = x /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events dst src len stackpointer
                                      returnaddress /\
                        memaccess_inbounds e2
                         [dst,val len; src,val len; stackpointer,8; ea,el]
                         [dst,val len]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let randombytes_safety_contract = new_definition
 `randombytes_safety_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e buf len stackpointer returnaddress.
        nonoverlapping (buf,val len) (ea,el) /\
        nonoverlapping (buf,val len) (stackpointer,8)
        ==> ensures x86
             (\s. read RIP s = f /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [buf; len] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events buf len stackpointer returnaddress /\
                        memaccess_inbounds e2
                         [buf,val len; stackpointer,8; ea,el]
                         [buf,val len]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(buf,val len)])`;;

(* ------------------------------------------------------------------------- *)
(* memset_ret_full_contract implies memset_full_contract.                    *)
(* ------------------------------------------------------------------------- *)

let MEMSET_RET_FULL_CONTRACT = prove
 (`!f ea el ev. memset_ret_full_contract f ea el ev
                ==> memset_full_contract f ea el ev`,
  REWRITE_TAC[memset_ret_full_contract; memset_full_contract] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f_events:int64->int64->int64->int64->int64->(uarch_event)list`
  THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_PREPOST) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Simulating a call. After the CALL of the stub plt_g at step k, the jump   *)
(* of the stub through the GOT is step k + 1, after which RIP is the address *)
(* read from the GOT, which must be in the assumptions as                    *)
(* read (memory :> bytes64 (word(pc + got_g))) s = f; LIBC_PLT_TAC execth    *)
(* plt got k restates that assumption in the form in which the simulation    *)
(* reads the slot and does that step. Then LIBC_FULL_CALL_TAC name execth    *)
(* ilist allowed (k + 2) uses the contract, as given by                      *)
(* ASSUME_CALLEE_SAFETY_TAILED_TAC, with the arguments ilist, to reach the   *)
(* state at step k + 2, where the call has returned, and unifies the events  *)
(* of the call with those of the contract, as for subroutines. These are the *)
(* tactics of the x86 mlkem-native proofs.                                   *)
(* ------------------------------------------------------------------------- *)

let WORD_VAL_ADD_64 = prove
 (`!m n. word(val(word m:int64) + n):int64 = word(m + n)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

let LIBC_GOT_RULE next target =
  let disp = target - next in
  let lt = mk_comb(`word:num->int64`,
    mk_binop `(+):num->num->num`
     (mk_comb(`val:int64->num`,
        mk_comb(`word:num->int64`,
          mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral next))))
     (mk_small_numeral disp)) in
  let eth = (REWRITE_CONV[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THENC
             NUM_REDUCE_CONV) lt in
  REWRITE_RULE[GSYM eth];;

let LIBC_PLT_TAC execth plt got k =
  let next = plt + 6 in
  let pat = subst [mk_small_numeral got,`n:num`]
   `read (memory :> bytes64 (word(pc + n))) s = (f:int64)` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(LIBC_GOT_RULE next got th) else NO_TAC) THEN
  X86_STEPS_TAC execth [k + 1];;

let VAL_WORD_NUMERAL_CONV tm =
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
      WORD_REDUCE_CONV tm
  | _ -> failwith "VAL_WORD_NUMERAL_CONV";;

let LIBC_CONTRACT_SIM_TAC ?(is_safety_thm=false) execth contract_th =
  fun ilist0 n ->
    let sname' = "s"^string_of_int n in
    let svar = mk_var("s"^string_of_int(n-1),`:x86state`)
    and svar0 = mk_var("s",`:x86state`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    MP_TAC(SPECL ilist contract_th) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; fst execth] THEN
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV VAL_WORD_NUMERAL_CONV) THEN
    (if is_safety_thm then
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN META_EXISTS_TAC
     else ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REPEAT CONJ_TAC THEN
      TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
      NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    X86_BIGSTEP_TAC execth sname' THEN
    TRY(ASM_REWRITE_TAC[C_ARGUMENTS] THEN NO_TAC);;

let LIBC_FULL_CALL_TAC name execth ilist allowed n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [FULL_EXISTS_E2_TAC allowed; LABEL_TAC name th]);;
