#include "_internal_s2n_bignum.h"

					S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_emontredc_8n_neon)
					S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_emontredc_8n_neon)
					.text
					.balign 4


S2N_BN_SYMBOL(bignum_emontredc_8n_neon):
           stp x19, x20, [sp, #-16]!
           stp x21, x22, [sp, #-16]!
           stp x23, x24, [sp, #-16]!
           stp x25, x26, [sp, #-16]!
           stp x27, x28, [sp, #-16]!
           lsr x0, x0, #2
           mov x26, x0
           subs x12, x0, #1
           bcc end
           mov x28, xzr
           lsl x0, x12, #5

outerloop:
           ldp x17, x19, [x1]
           ldp x20, x21, [x1, #16]
           ldp x8, x9, [x2]
           ldr q0, [x2]
           ldp x10, x11, [x2, #16]
           ldr q1, [x2, #16]

           mul x4, x17, x3
           dup v2.2d, x4
#define in1  v2
#define in2  v0
#define tmp1 v4
#define tmp2 v5
#define tmp3 v6
#define tmp4 v7
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x12, tmp3.d[0]
           adds x17, x17, x12
          mov     x13, tmp3.d[1]
           adcs x19, x19, x13
#undef in1
#undef in2
#define in1  v2
#define in2  v1
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x14, tmp3.d[0]
          mov     x15, tmp3.d[1]
#undef in1
#undef in2

           umulh x12, x4, x8
           umulh x13, x4, x9
           adcs x20, x20, x14
           umulh x14, x4, x10
           adcs x21, x21, x15
           umulh x15, x4, x11
           adc x22, xzr, xzr
           adds x19, x19, x12
           adcs x20, x20, x13
           adcs x21, x21, x14
           adc x22, x22, x15
           mul x5, x19, x3
           dup v2.2d, x5
#define in1  v2
#define in2  v0
#define tmp1 v4
#define tmp2 v5
#define tmp3 v6
#define tmp4 v7
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x12, tmp3.d[0]
          mov     x13, tmp3.d[1]
#undef in1
#undef in2
#define in1  v2
#define in2  v1
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x14, tmp3.d[0]
          mov     x15, tmp3.d[1]
#undef in1
#undef in2

           adds x19, x19, x12
           umulh x12, x5, x8
           adcs x20, x20, x13
           umulh x13, x5, x9
           adcs x21, x21, x14
           umulh x14, x5, x10
           adcs x22, x22, x15
           umulh x15, x5, x11
           adc x23, xzr, xzr
           adds x20, x20, x12
           adcs x21, x21, x13
           adcs x22, x22, x14
           adc x23, x23, x15
           mul x6, x20, x3
           dup v2.2d, x6
#define in1  v2
#define in2  v0
#define tmp1 v4
#define tmp2 v5
#define tmp3 v6
#define tmp4 v7
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x12, tmp3.d[0]
          mov     x13, tmp3.d[1]
#undef in1
#undef in2
#define in1  v2
#define in2  v1
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x14, tmp3.d[0]
          mov     x15, tmp3.d[1]
#undef in1
#undef in2
           adds x20, x20, x12
           umulh x12, x6, x8
           adcs x21, x21, x13
           umulh x13, x6, x9
           adcs x22, x22, x14
           umulh x14, x6, x10
           adcs x23, x23, x15
           umulh x15, x6, x11
           adc x24, xzr, xzr
           adds x21, x21, x12
           adcs x22, x22, x13
           adcs x23, x23, x14
           adc x24, x24, x15
           mul x7, x21, x3
           dup v2.2d, x7
#define in1  v2
#define in2  v0
#define tmp1 v4
#define tmp2 v5
#define tmp3 v6
#define tmp4 v7
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x12, tmp3.d[0]
          mov     x13, tmp3.d[1]
#undef in1
#undef in2
#define in1  v2
#define in2  v1
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x14, tmp3.d[0]
          mov     x15, tmp3.d[1]
#undef in1
#undef in2
           adds x21, x21, x12
           umulh x12, x7, x8
           adcs x22, x22, x13
           umulh x13, x7, x9
           adcs x23, x23, x14
           umulh x14, x7, x10
           adcs x24, x24, x15
           umulh x15, x7, x11
           adc x25, xzr, xzr
           adds x12, x22, x12
           adcs x13, x23, x13
           adcs x14, x24, x14
           adc x15, x25, x15
           stp x4, x5, [x1]
           stp x6, x7, [x1, #16]
           ldr q0, [x1]
           ldr q1, [x1, #16]
           cbz x0, madddone
           mov x27, x0
maddloop:
          add x2, x2, #32
          add x1, x1, #32
          ldp x8, x9, [x2]
          ldp x10, x11, [x2, #16]
          ldr q2, [x2]
          ldr q3, [x2, #16]
#define in1  v0
#define in2  v2
#define tmp1 v4
#define tmp2 v5
#define tmp3 v6
#define tmp4 v7
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x17, tmp3.d[0]
          mov     x22, tmp3.d[1]
#undef in1
#undef in2
          umulh x16,x4,x8

#define in1  v1
#define in2  v3
          uzp1    tmp1.4s, in2.4s, in1.4s
          rev64   tmp3.4s, in2.4s
          uzp1    tmp4.4s, in1.4s, in1.4s
          mul     tmp2.4s, tmp3.4s, in1.4s
          uaddlp  tmp3.2d, tmp2.4s
          shl     tmp3.2d, tmp3.2d, #32
          umlal   tmp3.2d, tmp4.2s, tmp1.2s
          mov     x23, tmp3.d[0]
          mov     x24, tmp3.d[1]
#undef in1
#undef in2
          adds x22,x22,x16
          umulh x16,x5,x9
          adcs x23,x23,x16
          umulh x16,x6,x10
          adcs x24,x24,x16
          umulh x16,x7,x11
          adc x25,x16,xzr
          ldp x20,x21,[x1]
          adds x12,x12,x20
          adcs x13,x13,x21
          ldp x20,x21,[x1,#16]
          adcs x14,x14,x20
          adcs x15,x15,x21
          adc x16,xzr,xzr
          adds x19,x22,x17
          adcs x22,x23,x22
          adcs x23,x24,x23
          adcs x24,x25,x24
          adc x25,xzr,x25
          adds x20,x22,x17
          adcs x21,x23,x19
          adcs x22,x24,x22
          adcs x23,x25,x23
          adcs x24,xzr,x24
          adc x25,xzr,x25
          adds x17,x17,x12
          adcs x19,x19,x13
          adcs x20,x20,x14
          adcs x21,x21,x15
          adcs x22,x22,x16
          adcs x23,x23,xzr
          adcs x24,x24,xzr
          adc x25,x25,xzr
          subs x15,x6,x7
          cneg x15,x15,cc
          csetm x12,cc
          subs x13,x11,x10
          cneg x13,x13,cc
          mul x14,x15,x13
          umulh x13,x15,x13
          cinv x12,x12,cc
          adds xzr,x12,#1
          eor x14,x14,x12
          adcs x23,x23,x14
          eor x13,x13,x12
          adcs x24,x24,x13
          adc x25,x25,x12
          subs x15,x4,x5
          cneg x15,x15,cc
          csetm x12,cc
          subs x13,x9,x8
          cneg x13,x13,cc
          mul x14,x15,x13
          umulh x13,x15,x13
          cinv x12,x12,cc
          adds xzr,x12,#1
          eor x14,x14,x12
          adcs x19,x19,x14
          eor x13,x13,x12
          adcs x20,x20,x13
          adcs x21,x21,x12
          adcs x22,x22,x12
          adcs x23,x23,x12
          adcs x24,x24,x12
          adc x25,x25,x12
          subs x15,x5,x7
          cneg x15,x15,cc
          csetm x12,cc
          subs x13,x11,x9
          cneg x13,x13,cc
          mul x14,x15,x13
          umulh x13,x15,x13
          cinv x12,x12,cc
          adds xzr,x12,#1
          eor x14,x14,x12
          adcs x22,x22,x14
          eor x13,x13,x12
          adcs x23,x23,x13
          adcs x24,x24,x12
          adc x25,x25,x12
          subs x15,x4,x6
          cneg x15,x15,cc
          csetm x12,cc
          subs x13,x10,x8
          cneg x13,x13,cc
          mul x14,x15,x13
          umulh x13,x15,x13
          cinv x12,x12,cc
          adds xzr,x12,#1
          eor x14,x14,x12
          adcs x20,x20,x14
          eor x13,x13,x12
          adcs x21,x21,x13
          adcs x22,x22,x12
          adcs x23,x23,x12
          adcs x24,x24,x12
          adc x25,x25,x12
          subs x15,x4,x7
          cneg x15,x15,cc
          csetm x12,cc
          subs x13,x11,x8
          cneg x13,x13,cc
          mul x14,x15,x13
          umulh x13,x15,x13
          cinv x12,x12,cc
          adds xzr,x12,#1
          eor x14,x14,x12
          adcs x21,x21,x14
          eor x13,x13,x12
          adcs x22,x22,x13
          adcs x23,x23,x12
          adcs x24,x24,x12
          adc x25,x25,x12
          subs x15,x5,x6
          cneg x15,x15,cc
          csetm x12,cc
          subs x13,x10,x9
          cneg x13,x13,cc
          mul x14,x15,x13
          umulh x13,x15,x13
          cinv x12,x12,cc
          adds xzr,x12,#1
          eor x14,x14,x12
          adcs x21,x21,x14
          eor x13,x13,x12
          adcs x22,x22,x13
          adcs x13,x23,x12
          adcs x14,x24,x12
          adc x15,x25,x12
          mov x12,x22
          stp x17,x19,[x1]
          stp x20,x21,[x1,#16]
           subs x27, x27, #32
           bne maddloop

madddone:
           ldp x17, x19, [x1, #32]
           ldp x20, x21, [x1, #48]
           adds xzr, x28, x28
           adcs x17, x17, x12
           adcs x19, x19, x13
           adcs x20, x20, x14
           adcs x21, x21, x15
           csetm x28, cs
           stp x17, x19, [x1, #32]
           stp x20, x21, [x1, #48]
           sub x1, x1, x0
           sub x2, x2, x0
           add x1, x1, #32
           subs x26, x26, #1
           bne outerloop
           neg x0, x28

end:
           ldp x27, x28, [sp], #16
           ldp x25, x26, [sp], #16
           ldp x23, x24, [sp], #16
           ldp x21, x22, [sp], #16
           ldp x19, x20, [sp], #16
           ret

