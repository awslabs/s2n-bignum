        .text
        .p2align 2
        .globl  shift_copy
        .type   shift_copy, %function
shift_copy:
        stp     x29, x30, [sp, #-48]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        str     x21, [sp, #32]
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        add     x1, x0, #8
        bl      memmove
        mov     x2, x21
        mov     x1, x19
        mov     x0, x20
        ldp     x19, x20, [sp, #16]
        ldr     x21, [sp, #32]
        ldp     x29, x30, [sp], #48
        b       memcpy
        .size   shift_copy, .-shift_copy

        .p2align 2
        .type   answer, %function
answer:
        mov     x0, #42
        ret
        .size   answer, .-answer

        .p2align 2
        .globl  call_slot
        .type   call_slot, %function
call_slot:
        adrp    x16, table
        add     x16, x16, :lo12:table
        ldr     x16, [x16, #16]
        br      x16
        .size   call_slot, .-call_slot

        .p2align 2
        .globl  memcpy_address
        .type   memcpy_address, %function
memcpy_address:
        adrp    x0, :got:memcpy
        ldr     x0, [x0, :got_lo12:memcpy]
        ret
        .size   memcpy_address, .-memcpy_address

        .section .data.rel.ro,"aw"
        .p2align 3
        .type   table, %object
table:
        .quad   0
        .quad   0
        .quad   answer
        .quad   memmove + 8
        .size   table, .-table
