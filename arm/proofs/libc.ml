(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Contracts for memcpy, memmove and memset on AArch64, and tactics for      *)
(* calls of external functions through the PLT of a shared object.           *)
(*                                                                           *)
(* The contracts (made by libc_contracts, common/libc_contracts.ml, which    *)
(* describes the five forms) are for the function at an address f, which a   *)
(* caller reads from a GOT slot, in any state in which the region (ea,el) of *)
(* memory, with the code and data of the C library, holds ev. A call starts *)
(* at f with the return address in X30 and returns there; it may change the *)
(* registers that the AAPCS64 lets a callee change (X0-X17, the flags, Q0-Q7 *)
(* and Q16-Q31, the upper halves of Q8-Q15: MAYCHANGE_REGS_AND_FLAGS_        *)
(* PERMITTED_BY_ABI), X18 and X30, and of memory only its destination.       *)
(* X16 and X17 are those that the PLT stub and a veneer of the linker use.   *)
(*                                                                           *)
(*  - memcpy dst src len: dst and src do not overlap; dst gets the len bytes *)
(*    at src; returns dst.                                                   *)
(*  - memmove dst src len: the regions may overlap; dst gets the len bytes   *)
(*    that were at src; returns dst.                                         *)
(*  - memset dst c len: each of the len bytes at dst becomes the low byte    *)
(*    of c; returns dst.                                                     *)
(*                                                                           *)
(* For memory safety, the reads are within the destination, the source and   *)
(* (ea,el), and the writes within the destination.                           *)
(*                                                                           *)
(* ASSUMPTIONS ABOUT THE IMPLEMENTATIONS, which a reader has to accept:       *)
(*                                                                           *)
(*  - They use no stack: no memory changes except the destination, and SP   *)
(*    is the same at the return (it is not in the frame). This holds for the *)
(*    AArch64 implementations of glibc (memcpy/memmove/memset in             *)
(*    sysdeps/aarch64, generic, SIMD, SVE and MOPS variants, all leaf        *)
(*    functions that keep their state in registers) and of musl and          *)
(*    bionic. An implementation written in C and compiled without that       *)
(*    property (with spills) would not satisfy these contracts; they would   *)
(*    then need a stack region below SP, disjoint from the caller's data, in *)
(*    the frame and in the writable regions.                                 *)
(*  - The ifunc resolution of glibc picks one of these variants when the     *)
(*    library is loaded; with -z now that is done before the code runs, so   *)
(*    the GOT slot holds the address of the chosen variant.                  *)
(*  - The state of the model has no SVE registers or other state that the    *)
(*    SVE variants change, and FPCR/FPSR are not changed.                    *)
(*  - The reads of memcpy and memmove for small len overlap within the       *)
(*    source (as glibc's do), but stay within it: no read beyond the end of  *)
(*    the source, or of the destination. For len = 0 there is no access.     *)
(*                                                                           *)
(* CALLS THROUGH THE PLT                                                     *)
(*                                                                           *)
(* A call bl <f@plt> (or a tail call b <f@plt>) at step k is followed by the *)
(* four instructions of the stub:                                            *)
(*                                                                           *)
(*     adrp x16, <page of the GOT slot>                                      *)
(*     ldr  x17, [x16, #<offset>]                                            *)
(*     add  x16, x16, #<offset>                                              *)
(*     br   x17                                                              *)
(*                                                                           *)
(* The ldr reads the GOT slot, whose fact (from ELF_RELOCATED_TAC or         *)
(* ELF_RELOCATED_DATA_TAC, common/elf_image.ml) is                           *)
(* read (memory :> bytes64 (word_add (word pc) (word got))) s = imp "f",     *)
(* so the stub ends at imp "f", where the contract applies.                  *)
(*                                                                           *)
(* With ARM_STEPS_TAC (classic): ARM_PLT_STUB_TAC execth k steps the stub,   *)
(* and ARM_PLT_CALL_TAC name execth ilist (k + 5) applies the contract (the  *)
(* assumption with label name, unfolded to !args. H ==> ensures ...) to the  *)
(* arguments ilist (terms in s, the state after the stub), reaching state    *)
(* s<k+5> where the call has returned. ARM_PLT_CT_CALL_TAC does the same for *)
(* the constant-time contracts (<f>_safety_contract, <f>_full_contract, as  *)
(* given by ASSUME_CALLEE_SAFETY_TAILED_TAC), unifying the events of the     *)
(* call with those of the contract, as LIBC_SAFE_CALL_TAC of mlkem-native.   *)
(*                                                                           *)
(* With bstep: ARM_BSTEP_PLT_STUB_TAC execth steps the stub from the current *)
(* goal (after a block that ended with the bl; the block may as well go on   *)
(* through the stub), and ARM_BSTEP_PLT_CALL_TAC                             *)
(* execth th ilist sname goes through the contract th (unfolded, any of the  *)
(* forms without an events function) to a new state sname. The arguments    *)
(* ilist are terms in s, evaluated in the current state by its facts, so the *)
(* contract does not mention the state. ARM_BSTEP_PLT_TAC does both.          *)
(*                                                                           *)
(* ADRP                                                                      *)
(*                                                                           *)
(* An image at a 4096-aligned pc has the pages of ADRP at word pc plus a     *)
(* constant; IMAGE_ADRP_TAC (arm/proofs/utils/loaded_image.ml) rewrites them *)
(* in the assumptions after ARM_STEPS_TAC. bstep does it in its step         *)
(* theorems when the goal has the assumption aligned 4096 (word pc)          *)
(* (arch_base_facts, arm/proofs/bstep.ml), so a block goes on through an     *)
(* ADRP and the LDR from its page. ARM_ADRP_FACT_TAC c rewrites the page in  *)
(* the fact of the register c only, for a fact made otherwise.               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bstep.ml";;
needs "arm/proofs/utils/loaded_image.ml";;
needs "common/elf_image.ml";;
needs "common/libc_contracts.ml";;

(* ------------------------------------------------------------------------- *)
(* The AArch64 calling convention for the contracts.                         *)
(* ------------------------------------------------------------------------- *)

let arm_libc_abi =
  { abi_step = `arm`;
    abi_memory = `memory:(armstate,int64->byte)component`;
    abi_events = `events:(armstate,(uarch_event)list)component`;
    abi_link = [`returnaddress:int64`];
    abi_call = (fun f s ->
      [mk_eq(mk_comb(`read PC:armstate->int64`,s),f);
       mk_eq(mk_comb(`read X30:armstate->int64`,s),`returnaddress:int64`)]);
    abi_return = (fun s ->
      mk_eq(mk_comb(`read PC:armstate->int64`,s),`returnaddress:int64`));
    abi_args = (fun args s ->
      list_mk_comb(`C_ARGUMENTS:int64 list->armstate->bool`,
                   [mk_list(args,`:int64`); s]));
    abi_result = (fun s r -> mk_eq(mk_comb(`C_RETURN:armstate->int64`,s),r));
    abi_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18; X30]`;
  };;

(* ------------------------------------------------------------------------- *)
(* memcpy, memmove and memset.                                               *)
(* ------------------------------------------------------------------------- *)

let memcpy_function =
  { lf_name = "memcpy";
    lf_args = [`dst:int64`; `src:int64`; `len:int64`];
    lf_ghosts = [`x:num`];
    lf_hyp = [`nonoverlapping (dst:int64,val(len:int64)) (src,val len)`];
    lf_pre = [`read (memory :> bytes(src,val(len:int64))) (s:armstate) = x`];
    lf_post = [`read (memory :> bytes(dst,val(len:int64))) (s:armstate) = x`];
    lf_result = Some `dst:int64`;
    lf_reads = [`dst:int64,val(len:int64)`; `src:int64,val(len:int64)`];
    lf_writes = [`dst:int64,val(len:int64)`];
  };;

let memmove_function =
  { memcpy_function with
    lf_name = "memmove";
    lf_hyp = [] };;

let memset_function =
  { lf_name = "memset";
    lf_args = [`dst:int64`; `c:int64`; `len:int64`];
    lf_ghosts = [];
    lf_hyp = [];
    lf_pre = [];
    lf_post = [`!i. i < val(len:int64)
                    ==> read (memory :> bytes8(word_add dst (word i)))
                             (s:armstate) =
                        word_zx(c:int64)`];
    lf_result = Some `dst:int64`;
    lf_reads = [`dst:int64,val(len:int64)`];
    lf_writes = [`dst:int64,val(len:int64)`];
  };;

let [memcpy_contract; memcpy_safe_contract; memcpy_correct_safe_contract;
     memcpy_safety_contract; memcpy_full_contract],
    [_,MEMCPY_FULL_CONTRACT; _,MEMCPY_CORRECT_SAFE_CONTRACT;
     _,MEMCPY_SAFETY_CONTRACT] =
  libc_contracts arm_libc_abi memcpy_function;;

let [memmove_contract; memmove_safe_contract; memmove_correct_safe_contract;
     memmove_safety_contract; memmove_full_contract],
    [_,MEMMOVE_FULL_CONTRACT; _,MEMMOVE_CORRECT_SAFE_CONTRACT;
     _,MEMMOVE_SAFETY_CONTRACT] =
  libc_contracts arm_libc_abi memmove_function;;

let [memset_contract; memset_safe_contract; memset_correct_safe_contract;
     memset_safety_contract; memset_full_contract],
    [_,MEMSET_FULL_CONTRACT; _,MEMSET_CORRECT_SAFE_CONTRACT;
     _,MEMSET_SAFETY_CONTRACT] =
  libc_contracts arm_libc_abi memset_function;;

(* The postcondition of memset with c = 0 as the bytes of the region.        *)

let READ_BYTES_EQ_0 = prove
 (`!(a:A word) n t.
        (!i. i < n ==> read (bytes8 (word_add a (word i))) t = word 0)
        ==> read (bytes(a,n)) t = 0`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[READ_BYTES_TRIVIAL] THEN
  REWRITE_TAC[ADD1; READ_BYTES_COMBINE; READ_BYTES_BYTES8] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[ARITH_RULE `i < n ==> i < n + 1`]);;

let READ_MEMORY_BYTES_EQ_0 = prove
 (`!(m:(S,A word->byte)component) a n s.
        (!i. i < n ==> read (m :> bytes8 (word_add a (word i))) s = word 0)
        ==> read (m :> bytes(a,n)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_EQ_0]);;

(* memmove's contract gives memcpy's: memmove is a memcpy.                   *)

let MEMMOVE_MEMCPY_CONTRACT = prove
 (`!f ea el ev.
        memmove_contract f ea el ev ==> memcpy_contract f ea el ev`,
  REWRITE_TAC[memmove_contract; memcpy_contract] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* ADRP in an image at a 4096-aligned pc. IMAGE_ADRP_TAC                     *)
(* (arm/proofs/utils/loaded_image.ml) rewrites the pages in all the          *)
(* assumptions, after ARM_STEPS_TAC; bstep makes them in that form itself.   *)
(* ARM_ADRP_FACT_TAC c rewrites only the fact read c s = v of the current    *)
(* state s, without walking the values of the other facts, with              *)
(* ARM_ADRP_PAGE_CONV (arm/proofs/bstep.ml).                                 *)
(* ------------------------------------------------------------------------- *)

let ARM_ADRP_FACT_TAC (c:term) =
  W(fun (asl,w) ->
    let convs = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("aligned",_),n),Comb(Const("word",_),Var(_,_)))
          when n = `4096` && type_of(rand(concl th)) = `:int64` ->
            ARM_ADRP_PAGE_CONV th
      | _ -> fail()) asl in
    if convs = [] then ALL_TAC else
    let rule = CONV_RULE(ONCE_DEPTH_CONV(FIRST_CONV convs) THENC
                         ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
    let s = rand w in
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_)
          when c' = c && s' = s -> (try rule th with Failure _ -> th)
      | _ -> th));;

(* ------------------------------------------------------------------------- *)
(* The PLT stub and the contract, with ARM_STEPS_TAC.                        *)
(* ------------------------------------------------------------------------- *)

let ARM_PLT_STUB_TAC execth k =
  ARM_STEPS_TAC execth [k + 1] THEN IMAGE_ADRP_TAC THEN
  ARM_STEPS_TAC execth ((k + 2)--(k + 4));;

let ARM_PLT_CONTRACT_SIM_TAC ?(is_safety_thm=false) execth contract_th =
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
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN
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

let ARM_PLT_CALL_TAC name execth ilist n =
  REMOVE_THEN name (fun th ->
    ARM_PLT_CONTRACT_SIM_TAC execth th ilist n THEN LABEL_TAC name th);;

let ARM_PLT_CT_CALL_TAC name execth ilist allowed n =
  REMOVE_THEN name (fun th ->
    ARM_PLT_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [EXISTS_E2_TAC allowed; LABEL_TAC name th]);;

(* ------------------------------------------------------------------------- *)
(* The PLT stub and the contract, with bstep.                                *)
(* ------------------------------------------------------------------------- *)

(* The stub from the current goal, whose PC is at its adrp, as one block     *)
(* (the goal has aligned 4096 (word pc), so the page of the adrp is          *)
(* word_add (word pc) (word k), and the ldr finds the fact of the GOT slot).  *)

let ARM_BSTEP_PLT_STUB_TAC ?keep execth =
  ARM_BSTEP_TAC ?keep execth (1--4);;

(* The value of t (a term in the state variable s) in the current state, by  *)
(* the facts read c s' = v of that state s'.                                 *)

let arm_bstep_eval (asl:(string*thm) list) (s':term) (t:term) =
  let t' = vsubst [s',`s:armstate`] t in
  let facts = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s1)),_)
        when s1 = s' -> th
    | _ -> fail()) asl in
  if not(vfree_in s' t') then t' else
  let th = PURE_ONCE_REWRITE_CONV facts t' in
  let r = rand(concl th) in
  if vfree_in s' r then
    failwith ("ARM_BSTEP_PLT_CALL_TAC: no value for `" ^ string_of_term t ^
              "` in the current state")
  else r;;

(* The theorem of a contract for the arguments, with its hypotheses proved   *)
(* from the assumptions (nonoverlapping facts), and its pre- and             *)
(* postcondition and frame in the forms that GEN_BSTEP_CALL_TAC uses.        *)

let ARM_CONTRACT_INSTANCE_TAC (th:thm) (ilist:term list) (ttac:thm->tactic) =
  W(fun (asl,w) ->
    let s' = rand w in
    let args = map (arm_bstep_eval asl s') ilist in
    let sth = SPECL args th in
    let sth = CONV_RULE(REWRITE_CONV[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS; ALLPAIRS; ALL;
                    PAIRWISE] THENC
                    DEPTH_CONV VAL_WORD_NUMERAL_CONV) sth in
    if not(is_imp(concl sth)) then ttac sth else
    let hyp_tm = lhand(concl sth) in
    let hth = TAC_PROOF((asl,hyp_tm),
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REPEAT CONJ_TAC THEN
      TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
      NONOVERLAPPING_TAC) in
    ttac (MP sth hth));;

let ARM_BSTEP_PLT_CALL_TAC ?keep execth (th:thm) (ilist:term list) sname =
  ARM_CONTRACT_INSTANCE_TAC th ilist
   (fun cth -> ARM_BSTEP_CALL_TAC ?keep execth cth sname);;

let ARM_BSTEP_PLT_TAC ?keep execth th ilist sname =
  ARM_BSTEP_PLT_STUB_TAC ?keep execth THEN
  ARM_BSTEP_PLT_CALL_TAC ?keep execth th ilist sname;;

(* ------------------------------------------------------------------------- *)
(* The end of a memory-safety proof: the goal                                *)
(* ?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 R W, with the   *)
(* fact read events s = E for events E made of CONS and APPEND on e. The     *)
(* witness is E without e; the concrete events are checked as by             *)
(* DISCHARGE_MEMACCESS_INBOUNDS_TAC, and the events of the callees (the      *)
(* variables chosen at their calls, with their memaccess_inbounds facts) by  *)
(* the containment of their regions.                                         *)
(* ------------------------------------------------------------------------- *)

let MEMSAFE_EVENTS_TAC =
  W(fun (asl,w) ->
    let e2,bod = dest_exists w in
    let evs_eq = lhand bod in
    let lhs_ev,app = dest_eq evs_eq in
    let e = rand app in
    let facts = mapfilter (fun (_,th) ->
        if is_eq(concl th) && lhand(concl th) = lhs_ev then th else fail())
      asl in
    let ev = match facts with th::_ -> rand(concl th) | [] -> lhs_ev in
    let rec split t =
      if t = e then mk_list([],hd(snd(dest_type(type_of e)))) else
      match t with
        Comb(Comb(Const("CONS",_) as c,h),t') -> mk_comb(mk_comb(c,h),split t')
      | Comb(Comb(Const("APPEND",_) as a,x),t') -> mk_comb(mk_comb(a,x),split t')
      | _ -> failwith "MEMSAFE_EVENTS_TAC: events not on e" in
    let wit = split ev in
    EXISTS_TAC wit THEN CONJ_TAC THENL
     [REWRITE_TAC facts THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
      DISCHARGE_MEMACCESS_INBOUNDS_TAC]);;
