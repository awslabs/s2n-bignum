/*
  This assembly file is a cleaned version of GCC
  output of the following C program:

  static const int x[10] = {2, 4, 6, 8, 10, 12, 14, 16, 18, 20};
  static const int y[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  static const int z = 1;

  int f(uint64_t i) {
    return x[i] + y[i];
  }

  int g(uint64_t i) {
    return f(i + z);
  }
*/

  .intel_syntax noprefix
  .text
  .type f, %function
f:
  // x[i]
 	lea    rcx,[rip + x]
  // y[i]
 	lea    rax,[rip + y]
 	mov    eax,[rdi*4 + rax]
 	add    eax,[rdi*4 + rcx]
 	ret

  .type g, %function
g:
  lea    rax,[rip + z]
  mov    edx,[rax]
  movsxd rdx,edx
  add    rdi,rdx
  call   f
  ret

  .section .rodata
  .type  x, %object
  .size  x, 40
x:
  .long  2
  .long  4
  .long  6
  .long  8
  .long  10
  .long  12
  .long  14
  .long  16
  .long  18
  .long  20

  .type  y, %object
  .size  y, 40
y:
  .long  1
  .long  2
  .long  3
  .long  4
  .long  5
  .long  6
  .long  7
  .long  8
  .long  9
  .long  10

  .type  z, %object
  .size  z, 4
z:
  .long 1

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
