(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the constant-time and memory safety proofs of the functions of  *)
(* the AVX-512 version of the x86 mlkem_native2 that call others: the        *)
(* theorems of the callees as assumptions, their calls as steps of the       *)
(* simulation, statements that are correctness and safety in one ("FULL"),   *)
(* and the discharge of the safety property. A copy of                       *)
(* utils/mlkem_native2_safety.ml for the AVX2 version.                       *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_avx512_noise.ml";;

(* ------------------------------------------------------------------------- *)
(* A callee's safety theorem |- ?f_events. !e x1 ... xn. P e as an           *)
(* assumption in the form !e x1 ... xn e_tail. P (APPEND e_tail e), as by    *)
(* ASSUME_CALLEE_SAFETY_TAILED_TAC but without its MESON call, which is too  *)
(* deep for theorems with many variables (that of mlkem_getnoise_avx512).    *)
(* ------------------------------------------------------------------------- *)

let SAFETY_TAILED_RULE th =
  let f,body = dest_exists(concl th) in
  let vs = fst(strip_forall body) in
  let e = hd vs and xs = tl vs in
  let et = mk_var("e_tail",type_of e) in
  let app = list_mk_icomb "APPEND" [et; e] in
  let th1 = GENL (e::xs @ [et]) (SPECL (app::xs) (ASSUME body)) in
  CHOOSE (f,th) (EXISTS (mk_exists(f,concl th1),f) th1);;

let ASSUME_CALLEE_TAILED_TAC th name =
  ASSUME_CALLEE_SAFETY_TAC (SAFETY_TAILED_RULE th) name;;

(* ------------------------------------------------------------------------- *)
(* Unique names for the variables that become metavariables: e_tail of the   *)
(* callee at each call, and e2 of the discharge at the end of a branch. Two  *)
(* metavariables of the same name, one instantiated before the other is      *)
(* made, give the justification wrong instantiations when the tactics are    *)
(* composed by THEN.                                                         *)
(* ------------------------------------------------------------------------- *)

let native2_fresh_counter = ref 0;;

let native2_fresh_var s ty =
  incr native2_fresh_counter;
  mk_var(s^"_"^string_of_int(!native2_fresh_counter),ty);;

let FRESH_TAIL_RULE th =
  let vs = fst(strip_forall(concl th)) in
  try let et = find (fun v -> name_of v = "e_tail") vs in
      let et' = native2_fresh_var "e_tail" (type_of et) in
      GENL (map (fun v -> if v = et then et' else v) vs)
           (INST [et',et] (SPEC_ALL th))
  with Failure _ -> th;;

let FRESH_E2_TAC (asl,w as gl) =
  if is_exists w then
    let v,_ = dest_exists w in
    CONV_TAC(GEN_ALPHA_CONV (native2_fresh_var "e2" (type_of v))) gl
  else ALL_TAC gl;;

let NATIVE2_DISCHARGE_FRESH_TAC =
  FRESH_E2_TAC THEN NATIVE2_DISCHARGE_SAFETY_TAC;;

let NATIVE2_DISCHARGE_FRESH_NORM_TAC normtac =
  FRESH_E2_TAC THEN NATIVE2_DISCHARGE_SAFETY_NORM_TAC normtac;;

(* ------------------------------------------------------------------------- *)
(* A call at state k by the theorem with the label in the assumptions (put   *)
(* back after), transformed by f (e.g. specialized but for e_tail) and with  *)
(* the variables ilist (in terms of s); the events may use vars and the      *)
(* functions of the templates (named f_ev...).                               *)
(* ------------------------------------------------------------------------- *)

let fev_vars (asl,w) =
  setify(find_terms (fun t -> is_var t &&
    (let n = name_of t in String.length n >= 4 && String.sub n 0 4 = "f_ev"))
    (list_mk_conj(w :: map (concl o snd) asl)));;

let NATIVE2_SAFE_THM_TAC exec vars label (offset,submc) f ilist k gl =
  let vs = vars @ fev_vars gl in
  REMOVE_THEN label (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_avx512_image_mc,exec,offset,submc,FRESH_TAIL_RULE(f th))
     ilist (k+1)
    THENL [EXISTS_E2_TAC (ref vs); LABEL_TAC label th]) gl;;

(*** A function of the image by its theorem with all the variables but
 *** e_tail given (args), rewritten with thms and the addresses normalized
 ***)

let NATIVE2_SAFE_IMAGE_TAC exec vars thms label args k gl =
  NATIVE2_SAFE_THM_TAC exec vars label (0,mlkem_native2_avx512_image_mc)
   (fun th -> CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
               (REWRITE_RULE thms (SPECL (`e:(uarch_event)list` :: args) th)))
   [] k gl;;

(* ------------------------------------------------------------------------- *)
(* The FULL form of a correctness statement tm: the events added to the      *)
(* precondition, and to the postcondition as a function of fargs within the  *)
(* regions rd (read) and wr (written); and the same without the code         *)
(* (bytes_loaded) in the postcondition, as the simulation needs to take the  *)
(* lemma as a step.                                                          *)
(* ------------------------------------------------------------------------- *)

let full_tm_of tm fargs rd wr =
  let vs,bod = strip_forall tm in
  let hyp,ens = dest_imp bod in
  let ensc,args = strip_comb ens in
  let sem = el 0 args and pre = el 1 args and post = el 2 args
  and frame = el 3 args in
  let sv,prebody = dest_abs pre and sv',postbody = dest_abs post in
  let postbody = vsubst [sv,sv'] postbody in
  let ev = `e:(uarch_event)list` in
  let fty = itlist (fun a ty -> mk_fun_ty (type_of a) ty) fargs
                   `:(uarch_event)list` in
  let fev = mk_var("f_events",fty) in
  let ty = `:int64#num` in
  let evc = vsubst [list_mk_comb(fev,fargs),`FEV:(uarch_event)list`;
                    mk_list(rd,ty),`RD:(int64#num)list`;
                    mk_list(wr,ty),`WR:(int64#num)list`; sv,`s:x86state`]
   `exists e2. read events s = APPEND e2 e /\ e2 = FEV /\
               memaccess_inbounds e2 RD WR` in
  let pre' = mk_abs(sv,list_mk_conj(conjuncts prebody @
                         [vsubst [sv,`s:x86state`] `read events s = e`]))
  and post' = mk_abs(sv,list_mk_conj(conjuncts postbody @ [evc])) in
  mk_exists(fev,list_mk_forall(ev::vs,
    mk_imp(hyp,list_mk_comb(ensc,[sem;pre';post';frame]))));;

let full_step_tm_of tm fargs rd wr =
  let tm' = full_tm_of tm fargs rd wr in
  let f,bod = dest_exists tm' in
  let vs,imp = strip_forall bod in
  let hyp,ens = dest_imp imp in
  let ensc,args = strip_comb ens in
  let sv,pb = dest_abs(el 2 args) in
  let code t =
    try fst(dest_const(fst(strip_comb t))) = "bytes_loaded"
    with Failure _ -> false in
  let pb' = list_mk_conj(filter (not o code) (conjuncts pb)) in
  mk_exists(f,list_mk_forall(vs,mk_imp(hyp,
    list_mk_comb(ensc,[el 0 args; el 1 args; mk_abs(sv,pb'); el 3 args]))));;
