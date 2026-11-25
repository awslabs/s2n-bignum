(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The slots of libsnappy.so (snappy 1.3.1, gcc 12 -O2, see                  *)
(* arm/snappy/README.md) that the dynamic loader relocates, with the values  *)
(* that it writes there when it loads the binary at the base pc, the address *)
(* of each imported symbol "sym" being imp "sym". 49 relocations. Generated  *)
(* by tools/elf_relocs.py (which explains the format) from the binary with   *)
(* SHA-256 40fdb95ecc036b431be3e62869fa2b4f9f8504c5fc1c69cc3b65374a3a849c86. *)
(* Do not edit it by hand.                                                   *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* The relocations, as offset, type, symbol + addend:                        *)
(*                                                                           *)
(*   0x1fbb0  R_AARCH64_RELATIVE   0x30f0                                    *)
(*   0x1fbb8  R_AARCH64_RELATIVE   0x30a0                                    *)
(*   0x1fbd0  R_AARCH64_RELATIVE   0x5870                                    *)
(*   0x1fbd8  R_AARCH64_RELATIVE   0x5890                                    *)
(*   0x1fbe0  R_AARCH64_RELATIVE   0x5850                                    *)
(*   0x1fbe8  R_AARCH64_RELATIVE   0x5860                                    *)
(*   0x1fbf0  R_AARCH64_RELATIVE   0x58e0                                    *)
(*   0x1fc18  R_AARCH64_ABS64      __cxa_pure_virtual + 0x0                  *)
(*   0x1fc20  R_AARCH64_ABS64      __cxa_pure_virtual + 0x0                  *)
(*   0x1fc28  R_AARCH64_ABS64      __cxa_pure_virtual + 0x0                  *)
(*   0x1fc50  R_AARCH64_ABS64      __cxa_pure_virtual + 0x0                  *)
(*   0x1fc58  R_AARCH64_RELATIVE   0x75a0                                    *)
(*   0x1fc60  R_AARCH64_RELATIVE   0x76c0                                    *)
(*   0x1fc68  R_AARCH64_RELATIVE   0x75b0                                    *)
(*   0x1fc80  R_AARCH64_RELATIVE   0x7754                                    *)
(*   0x1fc88  R_AARCH64_RELATIVE   0x7770                                    *)
(*   0x1fc90  R_AARCH64_RELATIVE   0x75c0                                    *)
(*   0x1fc98  R_AARCH64_RELATIVE   0x75d0                                    *)
(*   0x1fca0  R_AARCH64_RELATIVE   0x75e0                                    *)
(*   0x1fcb8  R_AARCH64_RELATIVE   0x77c4                                    *)
(*   0x1fcc0  R_AARCH64_RELATIVE   0x77e0                                    *)
(*   0x1fcc8  R_AARCH64_RELATIVE   0x7610                                    *)
(*   0x1fcd0  R_AARCH64_RELATIVE   0x75f4                                    *)
(*   0x1fcd8  R_AARCH64_RELATIVE   0x7650                                    *)
(*   0x1fce0  R_AARCH64_RELATIVE   0x7600                                    *)
(*   0x1ff40  R_AARCH64_JUMP_SLOT  _Znam + 0x0                               *)
(*   0x1ff48  R_AARCH64_JUMP_SLOT  memcpy + 0x0                              *)
(*   0x1ff50  R_AARCH64_JUMP_SLOT  _ZNSt7__cxx1112basic_stringIcSt11char_tra *)
(*   0x1ff58  R_AARCH64_JUMP_SLOT  _ZNSt7__cxx1112basic_stringIcSt11char_tra *)
(*   0x1ff60  R_AARCH64_JUMP_SLOT  _ZSt17__throw_bad_allocv + 0x0            *)
(*   0x1ff68  R_AARCH64_JUMP_SLOT  _ZSt20__throw_length_errorPKc + 0x0       *)
(*   0x1ff70  R_AARCH64_JUMP_SLOT  memset + 0x0                              *)
(*   0x1ff78  R_AARCH64_JUMP_SLOT  __cxa_finalize + 0x0                      *)
(*   0x1ff80  R_AARCH64_JUMP_SLOT  _ZdlPv + 0x0                              *)
(*   0x1ff88  R_AARCH64_JUMP_SLOT  _Znwm + 0x0                               *)
(*   0x1ff90  R_AARCH64_JUMP_SLOT  memmove + 0x0                             *)
(*   0x1ff98  R_AARCH64_JUMP_SLOT  _ZdaPv + 0x0                              *)
(*   0x1ffa0  R_AARCH64_JUMP_SLOT  _ZSt24__throw_out_of_range_fmtPKcz + 0x0  *)
(*   0x1ffa8  R_AARCH64_JUMP_SLOT  __gmon_start__ + 0x0                      *)
(*   0x1ffb0  R_AARCH64_JUMP_SLOT  __cxa_pure_virtual + 0x0                  *)
(*   0x1ffc0  R_AARCH64_RELATIVE   0x1fbc0                                   *)
(*   0x1ffc8  R_AARCH64_RELATIVE   0x1fca8                                   *)
(*   0x1ffd0  R_AARCH64_GLOB_DAT   __cxa_finalize + 0x0                      *)
(*   0x1ffd8  R_AARCH64_RELATIVE   0x1fc70                                   *)
(*   0x1ffe0  R_AARCH64_RELATIVE   0x58d0                                    *)
(*   0x1ffe8  R_AARCH64_GLOB_DAT   _ITM_deregisterTMCloneTable + 0x0         *)
(*   0x1fff0  R_AARCH64_GLOB_DAT   __gmon_start__ + 0x0                      *)
(*   0x1fff8  R_AARCH64_GLOB_DAT   _ITM_registerTMCloneTable + 0x0           *)
(*   0x20000  R_AARCH64_RELATIVE   0x20000                                   *)

let snappy_libsnappy_gcc12_O2_relocated = new_definition
 `snappy_libsnappy_gcc12_O2_relocated (pc:num) (imp:string->int64) =
   [(word (pc + 0x1fbb0):int64, word (pc + 0x30f0):int64);
    (word (pc + 0x1fbb8):int64, word (pc + 0x30a0):int64);
    (word (pc + 0x1fbd0):int64, word (pc + 0x5870):int64);
    (word (pc + 0x1fbd8):int64, word (pc + 0x5890):int64);
    (word (pc + 0x1fbe0):int64, word (pc + 0x5850):int64);
    (word (pc + 0x1fbe8):int64, word (pc + 0x5860):int64);
    (word (pc + 0x1fbf0):int64, word (pc + 0x58e0):int64);
    (word (pc + 0x1fc18):int64, imp "__cxa_pure_virtual":int64);
    (word (pc + 0x1fc20):int64, imp "__cxa_pure_virtual":int64);
    (word (pc + 0x1fc28):int64, imp "__cxa_pure_virtual":int64);
    (word (pc + 0x1fc50):int64, imp "__cxa_pure_virtual":int64);
    (word (pc + 0x1fc58):int64, word (pc + 0x75a0):int64);
    (word (pc + 0x1fc60):int64, word (pc + 0x76c0):int64);
    (word (pc + 0x1fc68):int64, word (pc + 0x75b0):int64);
    (word (pc + 0x1fc80):int64, word (pc + 0x7754):int64);
    (word (pc + 0x1fc88):int64, word (pc + 0x7770):int64);
    (word (pc + 0x1fc90):int64, word (pc + 0x75c0):int64);
    (word (pc + 0x1fc98):int64, word (pc + 0x75d0):int64);
    (word (pc + 0x1fca0):int64, word (pc + 0x75e0):int64);
    (word (pc + 0x1fcb8):int64, word (pc + 0x77c4):int64);
    (word (pc + 0x1fcc0):int64, word (pc + 0x77e0):int64);
    (word (pc + 0x1fcc8):int64, word (pc + 0x7610):int64);
    (word (pc + 0x1fcd0):int64, word (pc + 0x75f4):int64);
    (word (pc + 0x1fcd8):int64, word (pc + 0x7650):int64);
    (word (pc + 0x1fce0):int64, word (pc + 0x7600):int64);
    (word (pc + 0x1ff40):int64, imp "_Znam":int64);
    (word (pc + 0x1ff48):int64, imp "memcpy":int64);
    (word (pc + 0x1ff50):int64, imp "_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE6resizeEmc":int64);
    (word (pc + 0x1ff58):int64, imp "_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE9_M_appendEPKcm":int64);
    (word (pc + 0x1ff60):int64, imp "_ZSt17__throw_bad_allocv":int64);
    (word (pc + 0x1ff68):int64, imp "_ZSt20__throw_length_errorPKc":int64);
    (word (pc + 0x1ff70):int64, imp "memset":int64);
    (word (pc + 0x1ff78):int64, imp "__cxa_finalize":int64);
    (word (pc + 0x1ff80):int64, imp "_ZdlPv":int64);
    (word (pc + 0x1ff88):int64, imp "_Znwm":int64);
    (word (pc + 0x1ff90):int64, imp "memmove":int64);
    (word (pc + 0x1ff98):int64, imp "_ZdaPv":int64);
    (word (pc + 0x1ffa0):int64, imp "_ZSt24__throw_out_of_range_fmtPKcz":int64);
    (word (pc + 0x1ffa8):int64, imp "__gmon_start__":int64);
    (word (pc + 0x1ffb0):int64, imp "__cxa_pure_virtual":int64);
    (word (pc + 0x1ffc0):int64, word (pc + 0x1fbc0):int64);
    (word (pc + 0x1ffc8):int64, word (pc + 0x1fca8):int64);
    (word (pc + 0x1ffd0):int64, imp "__cxa_finalize":int64);
    (word (pc + 0x1ffd8):int64, word (pc + 0x1fc70):int64);
    (word (pc + 0x1ffe0):int64, word (pc + 0x58d0):int64);
    (word (pc + 0x1ffe8):int64, imp "_ITM_deregisterTMCloneTable":int64);
    (word (pc + 0x1fff0):int64, imp "__gmon_start__":int64);
    (word (pc + 0x1fff8):int64, imp "_ITM_registerTMCloneTable":int64);
    (word (pc + 0x20000):int64, word (pc + 0x20000):int64)]`;;
