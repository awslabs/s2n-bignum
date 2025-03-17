/*
  This assembly file is a cleaned version of GCC output of the following
  C program:

  const int x[10] = {2, 4, 6, 8, 10, 12, 14, 16, 18, 20};
  const int y[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

  int f(uint64_t i) {
    return x[i] + y[i];
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

.text
  .align  2
  .global  f
  .type  f, %function
f:
  mov x3, x0
  adrp  x0, x
  add  x0, x0, :lo12:x
  mov x1, x3
  ldr  w1, [x0, x1, lsl 2]
  adrp  x0, y
  add  x0, x0, :lo12:y
  mov x2, x3
  ldr  w0, [x0, x2, lsl 2]
  add  w0, w1, w0
  ret
