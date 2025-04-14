/*
  This assembly file is a cleaned (and less ABI-compliant) version of GCC
  output of the following
  C program:

  const int x[10] = {2, 4, 6, 8, 10, 12, 14, 16, 18, 20};
  const int y[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  const int z = 1;

  int f(uint64_t i) {
    return x[i] + y[i];
  }

  int g(int64_t i) {
    return f(i + z);
  }
*/

.text
.section  .rodata
  .global  x
  .align  3
  .type  x, %object
  .size  x, 40
x:
  .word  2
  .word  4
  .word  6
  .word  8
  .word  10
  .word  12
  .word  14
  .word  16
  .word  18
  .word  20

  .global  y
  .align  3
  .type  y, %object
  .size  y, 40
y:
  .word  1
  .word  2
  .word  3
  .word  4
  .word  5
  .word  6
  .word  7
  .word  8
  .word  9
  .word  10

  .global  z
  .align  3
  .type  z, %object
  .size  z, 4
z:
  .word  1

.text
  .align  2
  .type  f, %function
f:
  mov x3, x0
  adrp  x10, x
  add  x10, x10, :lo12:x
  mov x1, x3
  ldr  w1, [x10, x1, lsl 2]
  adrp  x11, y
  add  x11, x11, :lo12:y
  mov x2, x3
  ldr  w0, [x11, x2, lsl 2]
  add  w0, w1, w0
  ret

  .type  g, %function
g:
  adrp  x10, z
  add  x10, x10, :lo12:z
  ldr w1, [x10]
  add x0, x1, x0
  b f
