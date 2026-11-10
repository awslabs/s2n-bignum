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

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memcpy:

    mldsa44_prepare_domain_separation_prefix:
       +0x0  xor     eax, eax
       +0x2  cmp     r8, 0xff
       +0x9  ja      join4
       +0xb  push    r14
       +0xd  push    r13
       +0xf  push    r12
      +0x11  mov     r12, rdi
      +0x14  push    rbp
      +0x15  mov     rbp, r8
      +0x18  sub     rsp, 0x18
      +0x1c  test    r9d, r9d
      +0x1f  jne     join3
      +0x21  mov     BYTE PTR [rdi], 0x0
      +0x24  mov     BYTE PTR [r12+0x1], r8b
      +0x29  test    r8, r8
      +0x2c  jne     join14
     join1:
      +0x32  lea     rax, [rbp+0x2]
     join2:
      +0x36  add     rsp, 0x18
      +0x3a  pop     rbp
      +0x3b  pop     r12
      +0x3d  pop     r13
      +0x3f  pop     r14
     ret1:
      +0x41  ret
      +0x42  nop     WORD PTR [rax+rax*1+0x0]
     join3:
      +0x48  cmp     r9d, 0xc
      +0x4c  ja      join10
      +0x52  mov     r13, rdx
      +0x55  mov     eax, r9d
      +0x58  lea     rdx, [rip+0x6fc1]
                     // mldsa44_prepare_domain_separation_prefix_switch1_table
      +0x5f  mov     r14, rsi
      +0x62  movsxd  rax, DWORD PTR [rdx+rax*4]
      +0x66  add     rax, rdx
     switch1:
      +0x69  jmp     rax
      +0x6b  nop     DWORD PTR [rax+rax*1+0x0]
     join4: ret2:
      +0x70  ret
      +0x71  nop     DWORD PTR [rax+0x0]
     join5: switch1_case11: switch1_case2:
     switch1_case6: switch1_case8:
      +0x78  cmp     r13, 0x20
      +0x7c  jne     join10
     join6:
      +0x7e  mov     BYTE PTR [r12], 0x1
      +0x83  mov     BYTE PTR [r12+0x1], bpl
      +0x88  test    rbp, rbp
      +0x8b  jne     join15
     join7:
      +0x91  lea     rcx, [rip+0x6fc8]
                     // rodata_oid_map_0_1
      +0x98  xor     eax, eax
      +0x9a  mov     rdx, rcx
      +0x9d  nop     DWORD PTR [rax]
     loop1: loop1_test1:
      +0xa0  cmp     r9d, DWORD PTR [rdx]
      +0xa3  je      join13
     loop1_next1:
      +0xa5  add     eax, 0x1
      +0xa8  add     rdx, 0x10
     loop1_test2:
      +0xac  cmp     eax, 0xc
     loop1_back:
      +0xaf  jne     loop1
     join8: loop1_exit1:
      +0xb1  lea     rdi, [r12+rbp*1+0xd]
      +0xb6  mov     rdx, r13
      +0xb9  mov     rsi, r14
      +0xbc  call    memcpy
     after_memcpy_1:
      +0xc1  add     rsp, 0x18
      +0xc5  lea     rax, [r13+rbp*1+0xd]
      +0xca  pop     rbp
      +0xcb  pop     r12
      +0xcd  pop     r13
      +0xcf  pop     r14
     ret3:
      +0xd1  ret
      +0xd2  nop     WORD PTR [rax+rax*1+0x0]
     join9: switch1_case1: switch1_case5:
     switch1_case7:
      +0xd8  cmp     r13, 0x1c
      +0xdc  je      join6
     join10: switch1_case0:
      +0xde  xor     eax, eax
      +0xe0  jmp     join2
      +0xe5  nop     DWORD PTR [rax]
     join11: switch1_case10: switch1_case12:
     switch1_case4:
      +0xe8  cmp     r13, 0x40
      +0xec  je      join6
      +0xee  xor     eax, eax
      +0xf0  jmp     join2
      +0xf5  nop     DWORD PTR [rax]
     join12: switch1_case3: switch1_case9:
      +0xf8  cmp     r13, 0x30
      +0xfc  je      join6
      +0xfe  xor     eax, eax
     +0x100  jmp     join2
     +0x105  nop     DWORD PTR [rax]
     join13: loop1_exit2:
     +0x108  shl     rax, 0x4
     +0x10c  lea     rdx, [r12+rbp*1+0x2]
     +0x111  lea     rax, [rcx+rax*1+0x4]
     +0x116  mov     rcx, QWORD PTR [rax]
     +0x119  mov     QWORD PTR [rdx], rcx
     +0x11c  mov     eax, DWORD PTR [rax+0x7]
     +0x11f  mov     DWORD PTR [rdx+0x7], eax
     +0x122  jmp     join8
     +0x124  nop     DWORD PTR [rax+0x0]
     join14:
     +0x128  lea     rdi, [rdi+0x2]
     +0x12c  mov     rdx, r8
     +0x12f  mov     rsi, rcx
     +0x132  call    memcpy
     after_memcpy_2:
     +0x137  jmp     join1
     +0x13c  nop     DWORD PTR [rax+0x0]
     join15:
     +0x140  lea     rdi, [r12+0x2]
     +0x145  mov     rdx, rbp
     +0x148  mov     rsi, rcx
     +0x14b  mov     DWORD PTR [rsp+0xc], r9d
     +0x150  call    memcpy
     after_memcpy_3:
     +0x155  mov     r9d, DWORD PTR [rsp+0xc]
     +0x15a  jmp     join7

    plt_memcpy:
       +0x0  jmp     QWORD PTR [rip+0xefd2]
                     // got_memcpy
       +0x6  push    0x0
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_prepare_domain_separation_prefix";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memcpy. The context at ctx and the *)
(* pre-hash at ph are the bytes C and P, as numbers, and h is the value of   *)
(* the low 32 bits of hashalg (an int in C): the function returns            *)
(* mld_domain_separation_prefix_length h ctxlen phlen, and when that is not  *)
(* 0 it has written the prefix at prefix, which has room for the longest     *)
(* one, MLD_DOMAIN_SEPARATION_MAX_BYTES = 2 + 255 + 11 + 64 = 332 bytes. The *)
(* stack is the 64 bytes below the return address: the four registers that   *)
(* the function saves, 24 bytes of which it uses 4 to keep hashalg across    *)
(* the copy of the context, and the return address of each call of memcpy.   *)
(* The two tables that the function reads are in the image: the 13 offsets   *)
(* of the jump on hashalg,                                                   *)
(* mldsa44_prepare_domain_separation_prefix_switch1_table, and the table     *)
(* oid_map of mld_get_hash_oid, rodata_oid_map_0_1, of 12 entries of 16      *)
(* bytes (hashalg as 4 bytes, the OID, and a byte of padding).               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 64),64); (stackpointer,8)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa44_prepare_domain_separation_prefix) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
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
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths and hashalg only,     *)
(* with all accesses within the prefix, the context, the pre-hash, the       *)
(* stack, the slot of the return address, the GOT entry of memcpy, the       *)
(* region (ea,el) that memcpy may read and the two tables, and the writes    *)
(* within the prefix and the stack.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e prefix ph phlen ctx ctxlen hashalg C P pc stackpointer
                returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 64),64); (stackpointer,8)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa44_prepare_domain_separation_prefix) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
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
                              (word_sub stackpointer (word 64)) returnaddress /\
                       memaccess_inbounds e2
                        [prefix,332; ctx,ctxlen; ph,phlen;
                         word_sub stackpointer (word 64),64; stackpointer,8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                        mldsa44_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_1),192]
                        [prefix,332; word_sub stackpointer (word 64),64]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

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
          ALL (nonoverlapping (prefix,332))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el);
            (word_sub stackpointer (word 64),64); (stackpointer,8)] /\
          ALL (nonoverlapping (word_sub stackpointer (word 64),64))
           [(word pc,libmldsa_size); (ctx,ctxlen); (ph,phlen);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa44_prepare_domain_separation_prefix) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [prefix; ph; word phlen; ctx; word ctxlen;
                                 hashalg] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events prefix ph phlen ctx ctxlen hashalg mc pc
                              (word_sub stackpointer (word 64)) returnaddress /\
                       memaccess_inbounds e2
                        [prefix,332; ctx,ctxlen; ph,phlen;
                         word_sub stackpointer (word 64),64; stackpointer,8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc +
                        mldsa44_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_1),192]
                        [prefix,332; word_sub stackpointer (word 64),64]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(prefix,332);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
