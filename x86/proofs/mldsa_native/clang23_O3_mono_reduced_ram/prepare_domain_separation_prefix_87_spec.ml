(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The domain separation prefix: the statement. This is the code for         *)
(* mldsa87_prepare_domain_separation_prefix (the external API function       *)
(* mld_prepare_domain_separation_prefix in sign.c, for ML-DSA-87) from       *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which checks the  *)
(* lengths of the context and of the pre-hash, jumping on hashalg through a  *)
(* table of offsets to the check of the length of the pre-hash, writes the   *)
(* first two bytes, copies the context with memcpy if it is not empty, reads *)
(* the address of the OID of hashalg from a table of pointers (with no       *)
(* loop), copies the OID with a 4-byte and an 8-byte load and store, and     *)
(* copies the pre-hash with memcpy. It is verified in the whole image (see   *)
(* libmldsa.ml) against mld_domain_separation_prefix and                     *)
(* mld_domain_separation_prefix_length of common/mldsa_native_prefix.ml,     *)
(* using the contract memcpy_full_contract of utils/mldsa_native_libc.ml for *)
(* memcpy, and shown to be constant time and memory safe. The context and    *)
(* the pre-hash may be anything (NULL) if their lengths are 0, and the       *)
(* pre-hash is not used for pure ML-DSA.                                     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/oid_map.ml";;

(*** The code in the image, and the PLT stub for memcpy:

    mldsa87_prepare_domain_separation_prefix:
       +0x0: cmp     $0xff,%r8
       +0x7: jbe     <mldsa87_prepare_domain_separation_prefix+0x10>
       +0x9: xor     %eax,%eax
       +0xb: jmp     <mldsa87_prepare_domain_separation_prefix+0xdf>
      +0x10: cmp     $0xc,%r9d
      +0x14: ja      <mldsa87_prepare_domain_separation_prefix+0x9>
      +0x16: mov     %r8,%rax
      +0x19: mov     %r9d,%r8d
      +0x1c: lea     0x8c85(%rip),%r10
      +0x23: movslq  (%r10,%r8,4),%r8
      +0x27: add     %r10,%r8
      +0x2a: jmp     *%r8
      +0x2d: cmp     $0x20,%rdx
      +0x31: jne     <mldsa87_prepare_domain_separation_prefix+0x9>
      +0x33: jmp     <mldsa87_prepare_domain_separation_prefix+0x4b>
      +0x35: cmp     $0x1c,%rdx
      +0x39: jne     <mldsa87_prepare_domain_separation_prefix+0x9>
      +0x3b: jmp     <mldsa87_prepare_domain_separation_prefix+0x4b>
      +0x3d: cmp     $0x40,%rdx
      +0x41: jne     <mldsa87_prepare_domain_separation_prefix+0x9>
      +0x43: jmp     <mldsa87_prepare_domain_separation_prefix+0x4b>
      +0x45: cmp     $0x30,%rdx
      +0x49: jne     <mldsa87_prepare_domain_separation_prefix+0x9>
      +0x4b: push    %rbp
      +0x4c: push    %r15
      +0x4e: push    %r14
      +0x50: push    %r12
      +0x52: push    %rbx
      +0x53: test    %r9d,%r9d
      +0x56: setne   (%rdi)
      +0x59: mov     %al,0x1(%rdi)
      +0x5c: test    %rax,%rax
      +0x5f: je      <mldsa87_prepare_domain_separation_prefix+0x91>
      +0x61: lea     0x2(%rdi),%r8
      +0x65: mov     %rdi,%rbx
      +0x68: mov     %r8,%rdi
      +0x6b: mov     %rsi,%r14
      +0x6e: mov     %rcx,%rsi
      +0x71: mov     %rdx,%r15
      +0x74: mov     %rax,%rdx
      +0x77: mov     %rax,%r12
      +0x7a: mov     %r9d,%ebp
      +0x7d: call    <memcpy>
      +0x82: mov     %ebp,%r9d
      +0x85: mov     %rbx,%rdi
      +0x88: mov     %r14,%rsi
      +0x8b: mov     %r15,%rdx
      +0x8e: mov     %r12,%rax
      +0x91: test    %r9d,%r9d
      +0x94: je      <mldsa87_prepare_domain_separation_prefix+0xd3>
      +0x96: movslq  %r9d,%rcx
      +0x99: lea     0xb650(%rip),%r8
      +0xa0: mov     -0x8(%r8,%rcx,8),%rcx
      +0xa5: mov     0xb(%rcx),%r8d
      +0xa9: mov     %r8d,0x9(%rdi,%rax,1)
      +0xae: mov     0x4(%rcx),%rcx
      +0xb2: mov     %rcx,0x2(%rdi,%rax,1)
      +0xb7: add     %rax,%rdi
      +0xba: add     $0xd,%rdi
      +0xbe: mov     %rdx,%rbx
      +0xc1: mov     %rax,%r14
      +0xc4: call    <memcpy>
      +0xc9: lea     (%rbx,%r14,1),%rax
      +0xcd: add     $0xd,%rax
      +0xd1: jmp     <mldsa87_prepare_domain_separation_prefix+0xd7>
      +0xd3: add     $0x2,%rax
      +0xd7: pop     %rbx
      +0xd8: pop     %r12
      +0xda: pop     %r14
      +0xdc: pop     %r15
      +0xde: pop     %rbp
      +0xdf: xor     %ecx,%ecx
      +0xe1: xor     %edi,%edi
      +0xe3: xor     %edx,%edx
      +0xe5: xor     %esi,%esi
      +0xe7: xor     %r8d,%r8d
      +0xea: xor     %r9d,%r9d
      +0xed: xor     %r10d,%r10d
      +0xf0: ret     

    plt_memcpy:
       +0x0: jmp     *got_memcpy(%rip)
       +0x6: push    $0x0
       +0xb: jmp     <memcpy@plt-0x10>
 ***)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_prepare_domain_separation_prefix";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memcpy. The context at ctx and the *)
(* pre-hash at ph are the bytes C and P, as numbers, and h is the value of   *)
(* the low 32 bits of hashalg (an int in C): the function returns            *)
(* mld_domain_separation_prefix_length h ctxlen phlen, and when that is not  *)
(* 0 it has written the prefix at prefix, which has room for the longest     *)
(* one, MLD_DOMAIN_SEPARATION_MAX_BYTES = 2 + 255 + 11 + 64 = 332 bytes. The *)
(* stack is the 48 bytes below the return address: the five registers that   *)
(* the function saves and the return address of each call of memcpy. The     *)
(* function reads the 13 offsets of the jump on hashalg,                     *)
(* mldsa87_prepare_domain_separation_prefix_switch1_table, in the image, and *)
(* the table oid_map of mld_get_hash_oid: 12 pointers at pc + oid_map_ptrs,  *)
(* outside the image (see oid_map.ml), which the dynamic loader sets to the  *)
(* entries of rodata_mld_get_hash_oid87_oid_map in the image, as the         *)
(* precondition states. Each entry has 16 bytes: hashalg as 4 bytes, the     *)
(* OID, and a byte of padding.                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (word(pc + oid_map_ptrs),96); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 48),48); (stackpointer,8)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 48),48))
           [(word pc,libmldsa_size); (word(pc + oid_map_ptrs),96); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa87_prepare_domain_separation_prefix) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(ph,phlen)) s = P)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
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
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths and hashalg only,     *)
(* with all accesses within the prefix, the context, the pre-hash, the       *)
(* stack, the slot of the return address, the GOT entry of memcpy, the       *)
(* region (ea,el) that memcpy may read and the two tables, and the writes    *)
(* within the prefix and the stack.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
                returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (word(pc + oid_map_ptrs),96); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 48),48); (stackpointer,8)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 48),48))
           [(word pc,libmldsa_size); (word(pc + oid_map_ptrs),96); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa87_prepare_domain_separation_prefix) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(ph,phlen)) s = P /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
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
                         word_sub stackpointer (word 48),48; stackpointer,8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                        mldsa87_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192;
                         word(pc + oid_map_ptrs),96]
                        [prefix,332; word_sub stackpointer (word 48),48]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

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
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (word(pc + oid_map_ptrs),96); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 48),48); (stackpointer,8)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 48),48))
           [(word pc,libmldsa_size); (word(pc + oid_map_ptrs),96); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa87_prepare_domain_separation_prefix) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events prefix ph phlen ctx ctxlen hashalg mc pc
                              (word_sub stackpointer (word 48)) returnaddress /\
                       memaccess_inbounds e2
                        [prefix,332; ctx,ctxlen; ph,phlen;
                         word_sub stackpointer (word 48),48; stackpointer,8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                        mldsa87_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192;
                         word(pc + oid_map_ptrs),96]
                        [prefix,332; word_sub stackpointer (word 48),48]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
