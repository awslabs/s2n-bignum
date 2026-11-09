(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The domain separation prefix: the statement. This is the code for         *)
(* mldsa44_prepare_domain_separation_prefix (the external API function       *)
(* mld_prepare_domain_separation_prefix in sign.c, for ML-DSA-44) from       *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
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
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memcpy:

    mldsa44_prepare_domain_separation_prefix:
       +0x0: cmp     x4, #0xff
       +0x4: b.hi    <mldsa44_prepare_domain_separation_prefix+0x60>
       +0x8: stp     x19, x21, [sp, #-64]!
       +0xc: mov     x19, x4
      +0x10: mov     x21, x0
      +0x14: str     x30, [sp, #32]
      +0x18: cbz     w5, <mldsa44_prepare_domain_separation_prefix+0x44>
      +0x1c: stp     x22, x23, [sp, #16]
      +0x20: mov     x23, x1
      +0x24: sub     w1, w5, #0x1
      +0x28: mov     x0, #0x0
      +0x2c: cmp     w1, #0xb
      +0x30: b.ls    <mldsa44_prepare_domain_separation_prefix+0x68>
      +0x34: ldp     x22, x23, [sp, #16]
      +0x38: ldr     x30, [sp, #32]
      +0x3c: ldp     x19, x21, [sp], #64
      +0x40: ret
      +0x44: strb    wzr, [x0]
      +0x48: strb    w4, [x21, #1]
      +0x4c: cbnz    x4, <mldsa44_prepare_domain_separation_prefix+0x84>
      +0x50: add     x0, x19, #0x2
      +0x54: ldr     x30, [sp, #32]
      +0x58: ldp     x19, x21, [sp], #64
      +0x5c: ret
      +0x60: mov     x0, #0x0
      +0x64: ret
      +0x68: adrp    x0, <page>
      +0x6c: mov     x22, x2
      +0x70: add     x0, x0, #0x200
      +0x74: ldrb    w0, [x0, w1, uxtw]
      +0x78: adr     x1, mldsa44_prepare_domain_separation_prefix+0x84
      +0x7c: add     x0, x1, w0, sxtb #2
      +0x80: br      x0
      +0x84: mov     x1, x3
      +0x88: mov     x2, x4
      +0x8c: add     x0, x0, #0x2
      +0x90: bl      <memcpy@plt>
      +0x94: b       <mldsa44_prepare_domain_separation_prefix+0x50>
      +0x98: cmp     x2, #0x20
      +0x9c: b.ne    <mldsa44_prepare_domain_separation_prefix+0x110>
      +0xa0: mov     w0, #0x1
      +0xa4: strb    w0, [x21]
      +0xa8: strb    w19, [x21, #1]
      +0xac: cbnz    x19, <mldsa44_prepare_domain_separation_prefix+0x180>
      +0xb0: adrp    x1, <page>
      +0xb4: add     x4, x1, #0x210
      +0xb8: mov     w3, #0x0
      +0xbc: nop
      +0xc0: ldr     w0, [x4]
      +0xc4: cmp     w5, w0
      +0xc8: b.eq    <mldsa44_prepare_domain_separation_prefix+0x134>
      +0xcc: add     w3, w3, #0x1
      +0xd0: add     x4, x4, #0x10
      +0xd4: cmp     w3, #0xc
      +0xd8: b.ne    <mldsa44_prepare_domain_separation_prefix+0xc0>
      +0xdc: add     x0, x19, #0xd
      +0xe0: mov     x1, x23
      +0xe4: mov     x2, x22
      +0xe8: add     x0, x21, x0
      +0xec: bl      <memcpy@plt>
      +0xf0: add     x0, x22, #0xd
      +0xf4: ldp     x22, x23, [sp, #16]
      +0xf8: add     x0, x0, x19
      +0xfc: ldr     x30, [sp, #32]
     +0x100: ldp     x19, x21, [sp], #64
     +0x104: ret
     +0x108: cmp     x2, #0x1c
     +0x10c: b.eq    <mldsa44_prepare_domain_separation_prefix+0xa0>
     +0x110: ldp     x22, x23, [sp, #16]
     +0x114: mov     x0, #0x0
     +0x118: b       <mldsa44_prepare_domain_separation_prefix+0x54>
     +0x11c: cmp     x2, #0x40
     +0x120: b.eq    <mldsa44_prepare_domain_separation_prefix+0xa0>
     +0x124: b       <mldsa44_prepare_domain_separation_prefix+0x110>
     +0x128: cmp     x2, #0x30
     +0x12c: b.eq    <mldsa44_prepare_domain_separation_prefix+0xa0>
     +0x130: b       <mldsa44_prepare_domain_separation_prefix+0x110>
     +0x134: mov     x0, #0x4
     +0x138: add     x1, x1, #0x210
     +0x13c: add     x3, x0, w3, uxtw #4
     +0x140: add     x0, x19, #0x2
     +0x144: add     x4, x1, x3
     +0x148: add     x2, x21, x0
     +0x14c: ldr     x1, [x1, x3]
     +0x150: str     x1, [x21, x0]
     +0x154: mov     x1, x23
     +0x158: ldur    w0, [x4, #7]
     +0x15c: stur    w0, [x2, #7]
     +0x160: add     x0, x19, #0xd
     +0x164: mov     x2, x22
     +0x168: add     x0, x21, x0
     +0x16c: bl      <memcpy@plt>
     +0x170: add     x0, x22, #0xd
     +0x174: ldp     x22, x23, [sp, #16]
     +0x178: add     x0, x0, x19
     +0x17c: b       <mldsa44_prepare_domain_separation_prefix+0xfc>
     +0x180: mov     x1, x3
     +0x184: mov     x2, x19
     +0x188: add     x0, x21, #0x2
     +0x18c: str     w5, [sp, #60]
     +0x190: bl      <memcpy@plt>
     +0x194: ldr     w5, [sp, #60]
     +0x198: b       <mldsa44_prepare_domain_separation_prefix+0xb0>

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_prepare_domain_separation_prefix";
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
  let f = "mldsa44_prepare_domain_separation_prefix" in
  let tgt a b =
    mld_prefix_adrp_add_target mldsa_native_libmldsa_gcc12_O2_mc a b in
  let a1 = layout(f ^ "_adrp1") and a2 = layout(f ^ "_adrp2") in
  install_layout (layout_objects
   [f ^ "_jump_table",tgt a1 (a1 + 8),12;
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

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 64),64)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_prepare_domain_separation_prefix) /\
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
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths and hashalg only,     *)
(* with all accesses within the prefix, the context, the pre-hash, the       *)
(* stack, the GOT entry of memcpy, the region (ea,el) that memcpy may read   *)
(* and the two tables, and the writes within the prefix and the stack.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
            (word_sub stackpointer (word 64),64)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_prepare_domain_separation_prefix) /\
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
                              (word_sub stackpointer (word 64)) returnaddress /\
                       memaccess_inbounds e2
                        [prefix,332; ctx,ctxlen; ph,phlen;
                         word_sub stackpointer (word 64),64;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_oid_map),192]
                        [prefix,332; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
            (word_sub stackpointer (word 64),64)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_prepare_domain_separation_prefix) /\
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
                              (word_sub stackpointer (word 64)) returnaddress /\
                       memaccess_inbounds e2
                        [prefix,332; ctx,ctxlen; ph,phlen;
                         word_sub stackpointer (word 64),64;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_oid_map),192]
                        [prefix,332; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
