(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0 *)

(* Re-export the names from each source-level [open] at its original
   position so that descendant units see the same final bindings.
   Leave nested structures alone. *)
open Parsetree

let export item =
  match item.pstr_desc with
  | Pstr_open ({ popen_expr = { pmod_desc = Pmod_ident { txt = Longident.Lident _; _ };
                                pmod_attributes = []; _ };
                 popen_attributes = []; _ } as o) ->
      { item with pstr_desc = Pstr_include
          { pincl_mod = o.popen_expr; pincl_loc = o.popen_loc;
            pincl_attributes = o.popen_attributes } }
  | Pstr_open _ -> failwith "unsupported top-level open in shared proof module"
  | _ -> item

(* The compiler prepends these opens in order, before the original source.
   They make ancestor bindings visible here without exporting them again. *)
let rec structure imports items =
  match imports, items with
  | [], rest -> List.map export rest
  | name :: names, ({ pstr_desc = Pstr_open
        { popen_expr = { pmod_desc = Pmod_ident { txt = Longident.Lident id; _ }; _ }; _ };
                      _ } as item) :: rest when name = id ->
      item :: structure names rest
  | _ -> failwith "unexpected shared module prelude"

let () = Ast_mapper.run_main (fun ancestors ->
  { Ast_mapper.default_mapper with
    structure = (fun _ -> structure ("Hol_lib" :: "Hol_loader" :: ancestors)) })
