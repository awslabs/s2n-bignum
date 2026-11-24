(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proofs relative to the contracts of their callees, for x86-64: the x86    *)
(* base, then common/relative.ml, which explains the scheme.                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/relative.ml";;

(* X86_CORE_PROMOTE and ADD_IBT_RULE (x86/proofs/x86.ml) use prove through  *)
(* x86_rule_prove                                                            *)
x86_rule_prove := prove;;
