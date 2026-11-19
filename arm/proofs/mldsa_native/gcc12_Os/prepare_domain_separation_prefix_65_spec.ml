(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The domain separation prefix: the statement. This is the code for         *)
(* mldsa65_prepare_domain_separation_prefix (the external API function       *)
(* mld_prepare_domain_separation_prefix in sign.c, for ML-DSA-65) from       *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which checks the lengths of the context and of   *)
(* the pre-hash, jumps on hashalg through a table of offsets to the check of *)
(* the length of the pre-hash, writes the first two bytes, copies the        *)
(* context with memcpy, finds the OID in a table with a loop, copies it with *)
(* inlined loads and stores, and copies the pre-hash with memcpy. It is      *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_domain_separation_prefix and mld_domain_separation_prefix_length of   *)
(* common/mldsa_native_prefix.ml, using the contract memcpy_full_contract of *)
(* utils/mldsa_native_libc.ml for memcpy, and shown to be constant time and  *)
(* memory safe. The context and the pre-hash may be anything (NULL) if their *)
(* lengths are 0, and the pre-hash is not used for pure ML-DSA.              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memcpy:

    mldsa65_prepare_domain_separation_prefix:
       +0x0: cmp     x4, #0xff
       +0x4: b.hi    <mldsa65_prepare_domain_separation_prefix+0x128>
       +0x8: stp     x19, x20, [sp, #-48]!
       +0xc: mov     x19, x4
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: mov     x21, x0
      +0x18: mov     w22, w5
      +0x1c: stp     x23, x30, [sp, #32]
      +0x20: mov     x23, x1
      +0x24: mov     x1, x3
      +0x28: cbz     w5, <mldsa65_prepare_domain_separation_prefix+0xec>
      +0x2c: mov     x20, x2
      +0x30: sub     w2, w5, #0x1
      +0x34: cmp     w2, #0xb
      +0x38: b.hi    <mldsa65_prepare_domain_separation_prefix+0x130>
      +0x3c: adrp    x0, <page>
      +0x40: add     x0, x0, #0x35c
      +0x44: ldrb    w0, [x0, w2, uxtw]
      +0x48: adr     x2, <addr>
      +0x4c: add     x0, x2, w0, sxtb #2
      +0x50: br      x0
      +0x54: cmp     x20, #0x1c
      +0x58: b.ne    <mldsa65_prepare_domain_separation_prefix+0x130>
      +0x5c: mov     w0, #0x1
      +0x60: strb    w0, [x21]
      +0x64: strb    w19, [x21, #1]
      +0x68: cbz     x19, <mldsa65_prepare_domain_separation_prefix+0x78>
      +0x6c: mov     x2, x19
      +0x70: add     x0, x21, #0x2
      +0x74: bl      <memcpy@plt>
      +0x78: adrp    x0, <page>
      +0x7c: add     x0, x0, #0x368
      +0x80: mov     x1, #0x0
      +0x84: lsl     x2, x1, #4
      +0x88: ldr     w3, [x2, x0]
      +0x8c: cmp     w22, w3
      +0x90: b.ne    <mldsa65_prepare_domain_separation_prefix+0x118>
      +0x94: add     x2, x2, #0x4
      +0x98: add     x1, x19, #0x2
      +0x9c: add     x4, x0, x2
      +0xa0: add     x3, x21, x1
      +0xa4: ldr     x0, [x0, x2]
      +0xa8: str     x0, [x21, x1]
      +0xac: ldur    w0, [x4, #7]
      +0xb0: stur    w0, [x3, #7]
      +0xb4: add     x0, x19, #0xd
      +0xb8: mov     x2, x20
      +0xbc: mov     x1, x23
      +0xc0: add     x0, x21, x0
      +0xc4: add     x20, x20, #0xd
      +0xc8: bl      <memcpy@plt>
      +0xcc: add     x0, x20, x19
      +0xd0: b       <mldsa65_prepare_domain_separation_prefix+0x108>
      +0xd4: cmp     x20, #0x20
      +0xd8: b       <mldsa65_prepare_domain_separation_prefix+0x58>
      +0xdc: cmp     x20, #0x30
      +0xe0: b       <mldsa65_prepare_domain_separation_prefix+0x58>
      +0xe4: cmp     x20, #0x40
      +0xe8: b       <mldsa65_prepare_domain_separation_prefix+0x58>
      +0xec: strb    wzr, [x0]
      +0xf0: strb    w4, [x0, #1]
      +0xf4: cbz     x4, <mldsa65_prepare_domain_separation_prefix+0x104>
      +0xf8: mov     x2, x19
      +0xfc: add     x0, x21, #0x2
     +0x100: bl      <memcpy@plt>
     +0x104: add     x0, x19, #0x2
     +0x108: ldp     x21, x22, [sp, #16]
     +0x10c: ldp     x23, x30, [sp, #32]
     +0x110: ldp     x19, x20, [sp], #48
     +0x114: ret
     +0x118: add     x1, x1, #0x1
     +0x11c: cmp     x1, #0xc
     +0x120: b.ne    <mldsa65_prepare_domain_separation_prefix+0x84>
     +0x124: b       <mldsa65_prepare_domain_separation_prefix+0xb4>
     +0x128: mov     x0, #0x0
     +0x12c: ret
     +0x130: mov     x0, #0x0
     +0x134: b       <mldsa65_prepare_domain_separation_prefix+0x108>

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_prepare_domain_separation_prefix";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* The two tables that the function reads, which have no names in            *)
(* layout.ml: the 12 offsets of the jump on hashalg - 1, whose address the   *)
(* ADRP at adrp1 and the ADD two instructions later compute, and the table   *)
(* oid_map of mld_get_hash_oid, of 12 entries of 16 bytes (hashalg as 4      *)
(* bytes, the OID, and a byte of padding), from the ADRP at adrp2 and the    *)
(* ADD after it.                                                             *)
(* ------------------------------------------------------------------------- *)

let () =
  let f = "mldsa65_prepare_domain_separation_prefix" in
  let tgt a b =
    mld_prefix_adrp_add_target mldsa_native_libmldsa_gcc12_Os_mc a b in
  let a1 = layout(f ^ "_adrp1") and a2 = layout(f ^ "_adrp2") in
  install_layout (layout_objects
   [f ^ "_jump_table",tgt a1 (a1 + 4),12;
    f ^ "_oid_map",tgt a2 (a2 + 4),192]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memcpy. The context at ctx and the *)
(* pre-hash at ph are the bytes C and P, as numbers, and h is the value of   *)
(* the low 32 bits of hashalg (an int in C): the function returns            *)
(* mld_domain_separation_prefix_length h ctxlen phlen, and when that is not  *)
(* 0 it has written the prefix at prefix, which has room for the longest     *)
(* one, MLD_DOMAIN_SEPARATION_MAX_BYTES = 2 + 255 + 11 + 64 = 332 bytes.     *)
(* The stack is the 64 bytes of the function.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 48),48)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 48),48))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                    word(pc + mldsa65_prepare_domain_separation_prefix) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(ph,phlen)) s = P)
               (\s. read PC s = returnaddress /\
                    let h = val(word_zx hashalg:int32) in
                    let len = mld_domain_separation_prefix_length h ctxlen
                               phlen in
                    C_RETURN s = word len /\
                    (~(len = 0)
                     ==> read (memory :> bytes(prefix,len)) s =
                         num_of_bytelist
                          (mld_domain_separation_prefix h
                            (bytelist_of_num ctxlen C)
                            (bytelist_of_num phlen P))))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths and hashalg only,     *)
(* with all accesses within the prefix, the context, the pre-hash, the       *)
(* stack, the GOT entry of memcpy, the region (ea,el) that memcpy may read   *)
(* and the two tables, and the writes within the prefix and the stack.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
                returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 48),48)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 48),48))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                    word(pc + mldsa65_prepare_domain_separation_prefix) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(ph,phlen)) s = P /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (let h = val(word_zx hashalg:int32) in
                    let len = mld_domain_separation_prefix_length h ctxlen
                               phlen in
                    C_RETURN s = word len /\
                    (~(len = 0)
                     ==> read (memory :> bytes(prefix,len)) s =
                         num_of_bytelist
                          (mld_domain_separation_prefix h
                            (bytelist_of_num ctxlen C)
                            (bytelist_of_num phlen P)))) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events prefix ph phlen ctx ctxlen hashalg mc pc
                              (word_sub stackpointer (word 48)) returnaddress /\
                       memaccess_inbounds e2
                        [prefix,332; ctx,ctxlen; ph,phlen;
                         word_sub stackpointer (word 48),48;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_oid_map),192]
                        [prefix,332; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e prefix ph phlen ctx ctxlen hashalg pc stackpointer
                returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 48),48)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 48),48))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                    word(pc + mldsa65_prepare_domain_separation_prefix) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events prefix ph phlen ctx ctxlen hashalg mc pc
                              (word_sub stackpointer (word 48)) returnaddress /\
                       memaccess_inbounds e2
                        [prefix,332; ctx,ctxlen; ph,phlen;
                         word_sub stackpointer (word 48),48;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_oid_map),192]
                        [prefix,332; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
