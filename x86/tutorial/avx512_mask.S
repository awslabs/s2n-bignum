  .intel_syntax noprefix
  .text

  kxnorw k1, k0, k0
  kshiftrw k1, k1, 13
  vmovdqu64 [rdi]{k1}, zmm0
  vpblendmq zmm1{k1}, zmm2, zmm3
