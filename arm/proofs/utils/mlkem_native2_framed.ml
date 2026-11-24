(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The safety of the kernels of the library that the ML-KEM API in assembly  *)
(* calls, with the frames of their correctness theorems, as callers need     *)
(* them (their safety theorems have the frame \s s'. true): for those        *)
(* without a stack, from the correctness theorem by mk_safety_spec           *)
(* ~keep_maychanges:true; for those that save D8-D15, that of the core and   *)
(* then of the subroutine with the saving, then with the BTI landing pad.    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let core_safe_of core_correct sub_safe =
  let cvs,cimp = strip_forall(concl core_correct) in
  let chyp,cens = dest_imp cimp in
  let _,cargs = strip_comb cens in
  let cpre = el 1 cargs and cpost = el 2 cargs and cframe = el 3 cargs in
  let s,cpre_b = dest_abs cpre in
  let keep c =
    let h = fst(strip_comb c) in
    (is_const h && (name_of h = "aligned_bytes_loaded" ||
                    name_of h = "C_ARGUMENTS")) ||
    (is_eq c && (try rator(lhand c) = `read PC` with Failure _ -> false)) in
  let fv,sbody = dest_exists(concl sub_safe) in
  let svs,simp = strip_forall sbody in
  let ev = hd svs in
  let _,sens = dest_imp simp in
  let _,sargs = strip_comb sens in
  let spost = el 2 sargs in
  let s2,spost_b = dest_abs spost in
  let exc = find is_exists (conjuncts spost_b) in
  let e2,exb = dest_exists exc in
  let c1,c23 = dest_conj exb in
  let c2,c3 = dest_conj c23 in
  let fh,fargs = strip_comb(rand c2) in
  let fargs' = butlast(butlast fargs) in
  let fv' = mk_var("f_events",
    itlist (fun a t -> mk_fun_ty (type_of a) t) fargs' `:(uarch_event)list`) in
  let c2' = mk_eq(e2,list_mk_comb(fv',fargs')) in
  let mh,margs = strip_comb c3 in
  let nost l =
    let ls = dest_list l in
    mk_list(filter (fun p -> not(free_in `stackpointer:int64` p)) ls,
            type_of(hd ls)) in
  let c3' = list_mk_comb(mh,[e2; nost(el 1 margs); nost(el 2 margs)]) in
  let s3,cpost_b = dest_abs cpost in
  let pcpost = hd(conjuncts cpost_b) in
  let ex' = mk_exists(e2,list_mk_conj[vsubst [s3,s2] c1; c2'; c3']) in
  let pre' = mk_abs(s,list_mk_conj(filter keep (conjuncts cpre_b) @
               [mk_eq(mk_comb(`read events`,s),ev)])) in
  let post' = mk_abs(s3,mk_conj(pcpost,ex')) in
  let ens' = list_mk_comb(fst(strip_comb cens),
                          [hd cargs; pre'; post'; cframe]) in
  let body = mk_imp(chyp,ens') in
  let vs' = ev :: filter (fun v -> free_in v body) cvs in
  mk_exists(fv',list_mk_forall(vs',body));;

let framed_of safe correct =
  let c = concl safe in
  let fv,body = dest_exists c in
  let vs,imp = strip_forall body in
  let hyp,ens = dest_imp imp in
  let cfr = rand(snd(dest_imp(snd(strip_forall(concl correct))))) in
  mk_exists(fv,list_mk_forall(vs,mk_imp(hyp,mk_comb(rator ens,cfr))));;

(* The framed safety of a kernel with the stack: the core by the simulation
 * of the code, then the subroutine with the saving of D8-D15, then with
 * the BTI landing pad
 *)

let FRAMED_STACK_KERNEL core_correct sub_safe sub_correct exec nsteps
                        mc tmc =
  let ctm = core_safe_of core_correct sub_safe in
  let pubs = fst(strip_forall(snd(dest_exists ctm))) in
  let cth = prove(ctm,
    PROVE_SAFETY_SPEC_TAC ~public_vars:pubs exec) in
  let sth = prove(framed_of sub_safe sub_correct,
    ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:nsteps exec cth
      `[D8; D9; D10; D11; D12; D13; D14; D15]` 64 THEN
    DISCHARGE_SAFETY_PROPERTY_TAC) in
  cth,sth,ARM_ADD_IBT_RULE mc tmc sth;;

let framed_kernel_safe name correct exec =
  let spec,pubs = mk_safety_spec ~keep_maychanges:true
                   (assoc name subroutine_signatures) correct exec in
  prove(spec,PROVE_SAFETY_SPEC_TAC ~public_vars:pubs exec);;
