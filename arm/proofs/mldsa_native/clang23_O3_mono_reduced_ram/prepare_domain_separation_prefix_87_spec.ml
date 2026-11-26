(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The domain separation prefix: the statement. This is the code for         *)
(* mldsa87_prepare_domain_separation_prefix (the external API function       *)
(* mld_prepare_domain_separation_prefix in sign.c, for ML-DSA-87) from       *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* as a monolithic build with MLD_CONFIG_REDUCE_RAM (see                     *)
(* mldsa_native/README.md). The code checks the lengths of the context and   *)
(* of the pre-hash, jumps on hashalg through a table of offsets to the check *)
(* of the length of the pre-hash, writes the first two bytes, copies the     *)
(* context with memcpy, loads the address of the OID of hashalg from a table *)
(* of 12 pointers, copies the OID with an 8-byte and a 4-byte load and       *)
(* store, and copies the pre-hash with memcpy. The table of pointers is      *)
(* outside the bytes of the image (it holds relocated addresses), so the     *)
(* statement assumes that its entry k points to entry k of oid_map, as the   *)
(* code of the image has it. It is verified in the whole image (see          *)
(* libmldsa.ml) against mld_domain_separation_prefix and                     *)
(* mld_domain_separation_prefix_length of common/mldsa_native_prefix.ml,     *)
(* using the contract memcpy_full_contract of utils/mldsa_native_libc.ml for *)
(* memcpy, and shown to be constant time and memory safe. The context and    *)
(* the pre-hash may be anything (NULL) if their lengths are 0, and the       *)
(* pre-hash is not used for pure ML-DSA.                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memcpy:

    mldsa87_prepare_domain_separation_prefix:
       +0x0: cmp     x4, #0xff
       +0x4: b.ls    <mldsa87_prepare_domain_separation_prefix+0x10>
       +0x8: mov     x0, xzr
       +0xc: b       <mldsa87_prepare_domain_separation_prefix+0x10c>
      +0x10: cmp     w5, #0xc
      +0x14: b.hi    <mldsa87_prepare_domain_separation_prefix+0x8>
      +0x18: mov     w8, w5
      +0x1c: adrp    x9, <page>
      +0x20: add     x9, x9, #0x65a
      +0x24: adr     x10, <mldsa87_prepare_domain_separation_prefix+0x34>
      +0x28: ldrb    w11, [x9, x8]
      +0x2c: add     x10, x10, x11, lsl #2
      +0x30: br      x10
      +0x34: cmp     x2, #0x20
      +0x38: b.ne    <mldsa87_prepare_domain_separation_prefix+0x8>
      +0x3c: b       <mldsa87_prepare_domain_separation_prefix+0x60>
      +0x40: cmp     x2, #0x1c
      +0x44: b.ne    <mldsa87_prepare_domain_separation_prefix+0x8>
      +0x48: b       <mldsa87_prepare_domain_separation_prefix+0x60>
      +0x4c: cmp     x2, #0x40
      +0x50: b.ne    <mldsa87_prepare_domain_separation_prefix+0x8>
      +0x54: b       <mldsa87_prepare_domain_separation_prefix+0x60>
      +0x58: cmp     x2, #0x30
      +0x5c: b.ne    <mldsa87_prepare_domain_separation_prefix+0x8>
      +0x60: stp     x30, x23, [sp, #-48]!
      +0x64: stp     x22, x21, [sp, #16]
      +0x68: stp     x20, x19, [sp, #32]
      +0x6c: cmp     w5, #0x0
      +0x70: strb    w4, [x0, #1]
      +0x74: cset    w8, ne
      +0x78: strb    w8, [x0]
      +0x7c: cbz     x4, <mldsa87_prepare_domain_separation_prefix+0xb8>
      +0x80: mov     x19, x0
      +0x84: add     x0, x0, #0x2
      +0x88: mov     x20, x1
      +0x8c: mov     x1, x3
      +0x90: mov     x21, x2
      +0x94: mov     x2, x4
      +0x98: mov     x22, x4
      +0x9c: mov     w23, w5
      +0xa0: bl      <memcpy>
      +0xa4: mov     x0, x19
      +0xa8: mov     w5, w23
      +0xac: mov     x1, x20
      +0xb0: mov     x2, x21
      +0xb4: mov     x4, x22
      +0xb8: cbz     w5, <mldsa87_prepare_domain_separation_prefix+0xfc>
      +0xbc: adrp    x8, <page>
      +0xc0: add     x8, x8, #0xdd8
      +0xc4: add     x10, x0, x4
      +0xc8: add     x8, x8, w5, sxtw #3
      +0xcc: add     x0, x10, #0xd
      +0xd0: mov     x19, x2
      +0xd4: mov     x20, x4
      +0xd8: ldur    x8, [x8, #-8]
      +0xdc: ldur    w9, [x8, #11]
      +0xe0: ldur    x8, [x8, #4]
      +0xe4: stur    w9, [x10, #9]
      +0xe8: stur    x8, [x10, #2]
      +0xec: bl      <memcpy>
      +0xf0: add     x8, x19, x20
      +0xf4: add     x0, x8, #0xd
      +0xf8: b       <mldsa87_prepare_domain_separation_prefix+0x100>
      +0xfc: add     x0, x4, #0x2
     +0x100: ldp     x20, x19, [sp, #32]
     +0x104: ldp     x22, x21, [sp, #16]
     +0x108: ldp     x30, x23, [sp], #48
     +0x10c: mov     x1, #0x0
     +0x110: mov     x2, #0x0
     +0x114: mov     x3, #0x0
     +0x118: mov     x4, #0x0
     +0x11c: mov     x5, #0x0
     +0x120: mov     x8, #0x0
     +0x124: mov     x9, #0x0
     +0x128: mov     x10, #0x0
     +0x12c: mov     x11, #0x0
     +0x130: ret     

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_prepare_domain_separation_prefix";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* The two tables that the function reads, which have no names in layout.ml: *)
(* the 12 offsets of the jump on hashalg - 1, whose address the ADRP at      *)
(* adrp1 and the ADD two instructions later compute, and the 12 pointers to  *)
(* the entries of the table oid_map of mld_get_hash_oid (96 bytes), from the *)
(* ADRP at adrp2 and the ADD after it. The pointers are in .data.rel.ro,     *)
(* after the image, and the loader relocates them, so the statements assume  *)
(* that pointer k is the address of entry k of oid_map                       *)
(* (rodata_mld_get_hash_oid87_oid_map), an entry of 16 bytes (hashalg as 4   *)
(* bytes, the OID, and a byte of padding).                                   *)
(* ------------------------------------------------------------------------- *)

let () =
  let f = "mldsa87_prepare_domain_separation_prefix" in
  let tgt a b =
    mld_prefix_adrp_add_target mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc a b in
  let a1 = layout(f ^ "_adrp1") and a2 = layout(f ^ "_adrp2") in
  install_layout (layout_objects
   [f ^ "_jump_table",tgt a1 (a1 + 4),13;
    f ^ "_oid_ptrs",tgt a2 (a2 + 4),96]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memcpy. The context at ctx and the *)
(* pre-hash at ph are the bytes C and P, as numbers, and h is the value of   *)
(* the low 32 bits of hashalg (an int in C): the function returns            *)
(* mld_domain_separation_prefix_length h ctxlen phlen, and when that is not  *)
(* 0 it has written the prefix at prefix, which has room for the longest     *)
(* one, MLD_DOMAIN_SEPARATION_MAX_BYTES = 2 + 255 + 11 + 64 = 332 bytes.     *)
(* The stack is the 64 bytes of the function.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs),96);
            (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 64),64)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs),96);
            (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s =
                    word(pc + mldsa87_prepare_domain_separation_prefix) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa87_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
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

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths and hashalg only,     *)
(* with all accesses within the prefix, the context, the pre-hash, the       *)
(* stack, the GOT entry of memcpy, the region (ea,el) that memcpy may read   *)
(* and the two tables, and the writes within the prefix and the stack.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
                returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs),96);
            (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 64),64)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs),96);
            (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s =
                    word(pc + mldsa87_prepare_domain_separation_prefix) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa87_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
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
                          mldsa87_prepare_domain_separation_prefix_jump_table),
                         13;
                         word(pc +
                          mldsa87_prepare_domain_separation_prefix_oid_ptrs),
                         96;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [prefix,332; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e prefix ph phlen ctx ctxlen hashalg pc stackpointer
                returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs),96);
            (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 64),64)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs),96);
            (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s =
                    word(pc + mldsa87_prepare_domain_separation_prefix) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa87_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
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
                          mldsa87_prepare_domain_separation_prefix_jump_table),
                         13;
                         word(pc +
                          mldsa87_prepare_domain_separation_prefix_oid_ptrs),
                         96;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [prefix,332; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
