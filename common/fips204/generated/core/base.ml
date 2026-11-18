(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Load both ML-DSA specifications into one HOL Light session, from the      *)
(* repository root: the compiler-generated one (common/fips204/generated,    *)
(* see core/compiler/README.md) and the handwritten one of                   *)
(* common/fips204/fips204.ml with its properties. The generated file first   *)
(* checks that none of its variable names is a constant, so it is loaded     *)
(* first.                                                                    *)
(* ========================================================================= *)

loadt "common/fips204/generated/core/compiler/fips_hol_prelude.ml";;
type_invention_error := true;;
loadt "common/fips204/generated/fips204_generated.ml";;
loadt "common/fips204/generated/core/compiler/fips204_obligations.ml";;
type_invention_error := false;;

needs "common/fips204/fips204.ml";;
needs "common/fips204/properties/fips204_properties.ml";;
needs "common/fips204/properties/terminates.ml";;
