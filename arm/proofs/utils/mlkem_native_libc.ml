(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Contracts for the external functions called by the mlkem-native binary,   *)
(* and tactics for calls of them.                                            *)
(*                                                                           *)
(* Besides __stack_chk_fail, which is only called when the check of the      *)
(* stack guard fails, and so never in the proofs, the binary calls the C     *)
(* library functions memset and memcpy and the function randombytes,         *)
(* through its PLT and GOT (see mlkem_native/README.md). Their code is not   *)
(* part of the image, so their behaviour is assumed, as a notional           *)
(* high-level contract for each of them. A contract states the behaviour of  *)
(* the function at an address f (which a caller reads from the GOT) in any   *)
(* state where some region (ea,el) of memory, containing its code and any    *)
(* data it uses, has fixed contents ev; the callers require that region not  *)
(* to overlap anything they write, so that it is unchanged when they call    *)
(* the function. The functions may change the registers that the ABI allows  *)
(* them to, as well as X18 and X30, but no memory except their outputs; in   *)
(* particular they are assumed not to use the stack. memset sets each of     *)
(* the len bytes at dst to the low byte of c, memcpy copies the len bytes at *)
(* src to dst, which must not overlap, and randombytes writes len bytes at   *)
(* buf, with no assumption about their values, and returns a status in X0,   *)
(* again with no assumption about it.                                        *)
(*                                                                           *)
(* The contracts for constant time and memory safety, used in the proofs of  *)
(* the corresponding properties of the callers, state that the events of a   *)
(* call depend only on its arguments, apart from the data, and that it only  *)
(* reads its arguments and the region (ea,el) and only writes its outputs.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;
needs "arm/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* The contracts for correctness.                                            *)
(* ------------------------------------------------------------------------- *)

let memset_contract = new_definition
 `memset_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !dst c len returnaddress.
        nonoverlapping (dst,val len) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; c; len] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  !i. i < val len
                      ==> read (memory :> bytes8(word_add dst (word i))) s =
                          word_zx c)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let memcpy_contract = new_definition
 `memcpy_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !dst src len x returnaddress.
        nonoverlapping (dst,val len) (ea,el) /\
        nonoverlapping (dst,val len) (src,val len)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; src; len] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(src,val len)) s = x)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(dst,val len)) s = x)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let randombytes_contract = new_definition
 `randombytes_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !buf len returnaddress.
        nonoverlapping (buf,val len) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [buf; len] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(buf,val len)])`;;

(* ------------------------------------------------------------------------- *)
(* The contracts for constant time and memory safety.                        *)
(* ------------------------------------------------------------------------- *)

let memset_safety_contract = new_definition
 `memset_safety_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e dst c len returnaddress.
        nonoverlapping (dst,val len) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; c; len] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events dst c len returnaddress /\
                        memaccess_inbounds e2 [dst,val len; ea,el]
                                              [dst,val len]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let memcpy_safety_contract = new_definition
 `memcpy_safety_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e dst src len returnaddress.
        nonoverlapping (dst,val len) (ea,el) /\
        nonoverlapping (dst,val len) (src,val len)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; src; len] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events dst src len returnaddress /\
                        memaccess_inbounds e2
                         [dst,val len; src,val len; ea,el] [dst,val len]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let randombytes_safety_contract = new_definition
 `randombytes_safety_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e buf len returnaddress.
        nonoverlapping (buf,val len) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [buf; len] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events buf len returnaddress /\
                        memaccess_inbounds e2 [buf,val len; ea,el]
                                              [buf,val len]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(buf,val len)])`;;

(* ------------------------------------------------------------------------- *)
(* The PLT stubs and GOT entries in the image, and zeroing by memset. After  *)
(* a call of memset with c = 0, MEMSET_ZERO_BYTES_TAC adds the fact that the *)
(* region is zero, from the postcondition of the contract for each byte, in  *)
(* which the address of byte i for a destination word_add a (word k) may     *)
(* have been normalized to word_add a (word(k + i)) by the simulation.       *)
(* ------------------------------------------------------------------------- *)

let mlkem_native_plt_memcpy = 0x810
and mlkem_native_plt_randombytes = 0x820
and mlkem_native_plt_memset = 0x840;;

let mlkem_native_got_memcpy = 0x1ffd0
and mlkem_native_got_randombytes = 0x1ffd8
and mlkem_native_got_memset = 0x1ffe8;;

let MEMSET_ZERO_BYTES = prove
 (`!a n s:armstate.
        (!i. i < n
             ==> read (memory :> bytes8(word_add a (word i))) s =
                 word_zx(word 0:int64))
        ==> read (memory :> bytes(a,n)) s = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `0`; `s:armstate`]
               READ_MEMORY_BYTES_OF_BYTES8) THEN
  ASM_SIMP_TAC[DIV_0; MOD_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC WORD_REDUCE_CONV);;

let MEMSET_ZERO_BYTES_OFFSET = prove
 (`!a k n s:armstate.
        (!i. i < n
             ==> read (memory :> bytes8(word_add a (word(k + i)))) s =
                 word_zx(word 0:int64))
        ==> read (memory :> bytes(word_add a (word k),n)) s = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEMSET_ZERO_BYTES THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_SIMP_TAC[]);;

let MEMSET_ZERO_BYTES_TAC =
  FIRST_ASSUM(fun th ->
    ASSUME_TAC(try MATCH_MP MEMSET_ZERO_BYTES_OFFSET th
               with Failure _ -> MATCH_MP MEMSET_ZERO_BYTES th));;

(* ------------------------------------------------------------------------- *)
(* Simulating a call. LIBC_PLT_TAC execth k does the four steps of the PLT   *)
(* stub after the "bl" at step k, after which the PC is the address read     *)
(* from the GOT, which must be in the form                                   *)
(* read (memory :> bytes64 (word_add (word pc) (word n))) s = f in the       *)
(* assumptions, as normalized by MLKEM_NATIVE_ADRP_TAC. Then                 *)
(* LIBC_CALL_TAC name execth ilist (k + 5) uses the contract, which must be  *)
(* an assumption with that label, unfolded to |- !args. P ==> ensures ...,   *)
(* with the arguments ilist, to reach the state at step k + 5, where the     *)
(* call has returned. LIBC_SAFE_CALL_TAC does the same for the safety        *)
(* contracts, as given by ASSUME_CALLEE_SAFETY_TAILED_TAC, and unifies the   *)
(* events of the call with those of the contract, as for subroutines.        *)
(* ------------------------------------------------------------------------- *)

let LIBC_PLT_TAC execth k =
  ARM_STEPS_TAC execth [k + 1] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC execth ((k + 2)--(k + 4));;

let VAL_WORD_NUMERAL_CONV tm =
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
      WORD_REDUCE_CONV tm
  | _ -> failwith "VAL_WORD_NUMERAL_CONV";;

let LIBC_CONTRACT_SIM_TAC ?(is_safety_thm=false) execth contract_th =
  fun ilist0 n ->
    let sname' = "s"^string_of_int n in
    let svar = mk_var("s"^string_of_int(n-1),`:armstate`)
    and svar0 = mk_var("s",`:armstate`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    MP_TAC(SPECL ilist contract_th) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS; fst execth] THEN
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
    ARM_BIGSTEP_TAC execth sname' THEN
    TRY(ASM_REWRITE_TAC[C_ARGUMENTS] THEN NO_TAC);;

(*** The calls, with the contract as an assumption with the given label ***)

let LIBC_CALL_TAC name execth ilist n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC execth th ilist n THEN LABEL_TAC name th);;

let LIBC_SAFE_CALL_TAC name execth ilist allowed n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [EXISTS_E2_TAC allowed; LABEL_TAC name th]);;
