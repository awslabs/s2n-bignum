(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The contract for the external function randombytes called by the         *)
(* mlkem-native binary, and tactics for calls of it.                         *)
(*                                                                           *)
(* The binary calls randombytes through its PLT and GOT (see                 *)
(* mlkem_native/README.md): the stub randombytes@plt at 0x1010 in the image  *)
(* jumps to the address in the GOT entry at 0xaff8, which is outside the     *)
(* image. The code of the function is not part of the image, so its          *)
(* behaviour is assumed, as a notional high-level contract, as for AArch64   *)
(* (see arm/proofs/utils/mlkem_native_libc.ml). The contract states the      *)
(* behaviour of the function at an address f (which the stub reads from the  *)
(* GOT) in any state where some region (ea,el) of memory, containing its     *)
(* code and any data it uses, has fixed contents ev; the callers require     *)
(* that region not to overlap anything they write, so that it is unchanged   *)
(* when they call the function. The function writes len bytes at buf, with   *)
(* no assumption about their values, returns to the return address on the    *)
(* stack, with a status in RAX, again with no assumption about it, and may   *)
(* change the registers that the ABI allows it to, but no memory except its  *)
(* output; in particular it is assumed not to use the stack, apart from      *)
(* reading the return address. (The memset and memcpy that the AArch64       *)
(* binary calls are inlined by gcc for x86-64, as REP STOSQ and REP MOVSQ.)  *)
(*                                                                           *)
(* The contract for constant time and memory safety, used in the proofs of   *)
(* the corresponding properties of the callers, states that the events of a  *)
(* call depend only on its arguments and the stack pointer, apart from the   *)
(* data, and that it only reads its output, its return address and the       *)
(* region (ea,el) and only writes its output.                                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;
needs "x86/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* The contracts.                                                            *)
(* ------------------------------------------------------------------------- *)

let randombytes_contract = new_definition
 `randombytes_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !buf len stackpointer returnaddress.
        nonoverlapping (buf,val len) (ea,el) /\
        nonoverlapping (buf,val len) (stackpointer,8)
        ==> ensures x86
             (\s. read RIP s = f /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [buf; len] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(buf,val len)])`;;

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
(* The PLT stub and the GOT entry in the image.                              *)
(* ------------------------------------------------------------------------- *)

let mlkem_native_plt_randombytes = 0x1010
and mlkem_native_got_randombytes = 0xaff8;;

(* ------------------------------------------------------------------------- *)
(* Simulating a call. After the call of the stub at step k, the jump of the  *)
(* stub through the GOT is step k + 1, after which RIP is the address read   *)
(* from the GOT, which must be in the assumptions as                         *)
(* read (memory :> bytes64 (word(pc + 0xaff8))) s = f. Then                  *)
(* LIBC_CALL_TAC name execth ilist (k + 2) uses the contract, which must be  *)
(* an assumption with that label, unfolded to |- !args. P ==> ensures ...,   *)
(* with the arguments ilist, to reach the state at step k + 2, where the     *)
(* call has returned. LIBC_SAFE_CALL_TAC does the same for the safety        *)
(* contract, as given by ASSUME_CALLEE_SAFETY_TAILED_TAC, and unifies the    *)
(* events of the call with those of the contract, as for subroutines.        *)
(* ------------------------------------------------------------------------- *)

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

let LIBC_PLT_TAC execth k =
  let next = mlkem_native_plt_randombytes + 6
  and target = mlkem_native_got_randombytes in
  let pat = subst [mk_small_numeral target,`n:num`]
   `read (memory :> bytes64 (word(pc + n))) s = (f:int64)` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(LIBC_GOT_RULE next target th) else NO_TAC) THEN
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

let LIBC_CALL_TAC name execth ilist n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC execth th ilist n THEN LABEL_TAC name th);;

let LIBC_SAFE_CALL_TAC name execth ilist allowed n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [EXISTS_E2_TAC allowed; LABEL_TAC name th]);;
