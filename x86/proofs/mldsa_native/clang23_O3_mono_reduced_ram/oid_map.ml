(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The pointer table of mld_get_hash_oid in the clang 23 build. The static   *)
(* array oid_map of 12 pointers to the 16-byte OID records is not in the     *)
(* read-only data of the image, as it is in the gcc builds, but in           *)
(* .data.rel.ro at 0x27df0, after the end of the image (see layout.ml): its  *)
(* entries are filled by the dynamic loader, which relocates the 12          *)
(* R_X86_64_RELATIVE entries to the records, at 16 * k from                  *)
(* rodata_mld_get_hash_oid87_oid_map. The code of                            *)
(* prepare_domain_separation_prefix (also where it is inlined) reads the     *)
(* table with a RIP-relative LEA at pc + oid_map_ptrs, so the statements     *)
(* assume the relocated contents, as for the GOT slots of the libc           *)
(* functions, and that the table does not overlap what the function writes.  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/layout.ml";;

let oid_map_ptrs = define `oid_map_ptrs = 0x27df0`;;
