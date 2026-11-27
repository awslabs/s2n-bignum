(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0 *)

(* A proof normally shares a compilation unit with its base. Re-export the
   names from each top-level [open] at its original position so that opening
   Proof_base in another unit reproduces the final name resolution order.
   Leave nested structures and the HOL inliner's two prelude opens alone. *)
open Parsetree

let export item =
  match item.pstr_desc with
  | Pstr_open ({ popen_expr = { pmod_desc = Pmod_ident { txt = Longident.Lident _; _ };
                                pmod_attributes = []; _ };
                 popen_attributes = []; _ } as o) ->
      { item with pstr_desc = Pstr_include
          { pincl_mod = o.popen_expr; pincl_loc = o.popen_loc;
            pincl_attributes = o.popen_attributes } }
  | Pstr_open _ -> failwith "unsupported top-level open in shared proof base"
  | _ -> item

let structure _ = function
  | ({ pstr_desc = Pstr_open _; _ } as hol) ::
    ({ pstr_desc = Pstr_open _; _ } as loader) :: rest ->
      hol :: loader :: List.map export rest
  | _ -> failwith "unexpected HOL inliner prelude"

let () = Ast_mapper.run_main (fun _ -> { Ast_mapper.default_mapper with structure })
