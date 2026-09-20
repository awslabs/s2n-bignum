(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(*
 * Controls shared by the random instruction-semantic campaigns.
 *
 * By default, a campaign runs for 2400 seconds of wall-clock time and
 * has no case-count limit. The environment variables below provide
 * deterministic duration, case-count, and random-seed controls.
 *
 * The complete runtime configuration is documented in common/cosim.ml.
 *)

let sematest_getenv name =
  try Some (Sys.getenv name) with Not_found -> None;;

let sematest_seconds default =
  match sematest_getenv "S2N_BIGNUM_SEMATEST_SECONDS" with
  | None -> default
  | Some s ->
      let seconds = float_of_string s in
      if seconds <= 0.0 then
        failwith "S2N_BIGNUM_SEMATEST_SECONDS must be positive";
      seconds;;

let sematest_case_limit () =
  match sematest_getenv "S2N_BIGNUM_SEMATEST_CASES" with
  | None -> None
  | Some s ->
      let cases = int_of_string s in
      if cases <= 0 then
        failwith "S2N_BIGNUM_SEMATEST_CASES must be positive";
      Some cases;;

let sematest_random_init () =
  match sematest_getenv "S2N_BIGNUM_SEMATEST_SEED" with
  | None -> Random.self_init ()
  | Some s -> Random.init (int_of_string s);;

let sematest_finished seconds cases start_time count =
  Unix.gettimeofday () -. start_time > seconds ||
  match cases with
  | None -> false
  | Some limit -> count >= limit;;
