// C reproduction of gcm_init_v8 (ghashv8-armx.pl:93-283), producing the
// v8-format Htable[0..11] that aesv8_gcm_8x_enc_256 consumes. TEST GLUE.
//
// NEON model: a q-register is a 128-bit value held as {lo, hi} (two u64), where
// lo = bytes 0..7 (element [0]), hi = bytes 8..15 (element [1]). The table is
// stored to memory as consecutive 16-byte little-endian {lo,hi} pairs, matching
// how the kernel loads them with ldr/ldp. Each NEON op below is annotated with
// the .pl line it mirrors.

typedef struct { uint64_t lo, hi; } q_t;

// pmull/pmull2: 64x64 -> 128 carryless multiply.
static q_t clmul64(uint64_t a, uint64_t b){
  q_t r = {0,0};
  uint128_t acc = 0;
  for (int i=0;i<64;i++) if ((b>>i)&1) acc ^= ((uint128_t)a)<<i;
  r.lo = (uint64_t)acc; r.hi = (uint64_t)(acc>>64);
  return r;
}
static inline q_t qeor(q_t a, q_t b){ q_t r={a.lo^b.lo, a.hi^b.hi}; return r; }
// vext.8 r, a, b, #8  => low half = a.hi, high half = b.lo
static inline q_t qext8(q_t a, q_t b){ q_t r={a.hi, b.lo}; return r; }
// pmull.p64 uses element [0] (lo) of each operand; pmull2 uses element [1] (hi).
static inline q_t pmull_lo(q_t a, q_t b){ return clmul64(a.lo, b.lo); }
static inline q_t pmull_hi(q_t a, q_t b){ return clmul64(a.hi, b.hi); }

// The 0xc2 reduction constant as built by the asm: vmov.i8 #0xe1; vshl.i64 #57
// => each 64-bit lane = 0xe1 << 57 = 0xc200000000000000. Used as {lo=that, hi=that}
// but only lane[0] participates in pmull.p64 $Xl,$xC2 (i.e. clmul(Xl.lo, 0xc2..)).
#define C2CONST UINT64_C(0xc200000000000000)

// One Montgomery-style reduction step shared by all power computations:
// given a 256-bit product in (Xl, Xh) plus mid Xm already Karatsuba-combined,
// return the reduced 128-bit field element (as the asm's $Xl after 2nd phase).
// Mirrors .pl lines 120-133 (H^2 case) / 155-181 (H^3/4) etc. — identical shape.
static q_t reduce256(q_t Xl, q_t Xm, q_t Xh){
  // Karatsuba post-processing: t1 = ext(Xl,Xh,#8); t2 = Xl^Xh; Xm ^= t1; Xm ^= t2
  q_t t1 = qext8(Xl, Xh);
  q_t t2 = qeor(Xl, Xh);
  Xm = qeor(Xm, t1);
  Xm = qeor(Xm, t2);
  // 1st phase: t2 = pmull(Xl.lo, C2)
  q_t p = clmul64(Xl.lo, C2CONST);
  // Xh.lo = Xm.hi ; Xm.hi = Xl.lo   (vmov lane moves)
  Xh.lo = Xm.hi;
  Xm.hi = Xl.lo;
  // Xl = Xm ^ t2
  Xl = qeor(Xm, p);
  // 2nd phase: t2 = ext(Xl,Xl,#8); Xl = pmull(Xl.lo, C2); t2 ^= Xh; Xl ^= t2
  q_t e = qext8(Xl, Xl);
  Xl = clmul64(Xl.lo, C2CONST);
  e = qeor(e, Xh);
  Xl = qeor(Xl, e);
  return Xl;
}

// From a reduced field element t1 (the asm's $t0/$t1 = "H^k"), produce the
// stored register form Hk = ext8(t1,t1) and the karatsuba pre value tk = t1^Hk.
static q_t to_reg(q_t t1, q_t *pre_out){
  q_t Hk = qext8(t1, t1);
  if (pre_out) *pre_out = qeor(t1, Hk);
  return Hk;
}

// gcm_init_v8: fill Htable (as uint64 pairs) slots 0..11.
static void gcm_init_v8_c(uint64_t Htable[2*16], const uint64_t Hin[2]){
  // load input H into t1 = {lo=Hin[1]? } -- asm: vld1.64 {t1},[x1] loads H[0],H[1]
  // into lanes: t1.lo = H[0], t1.hi = H[1]. But gcm_init is passed H as u64[2]
  // where H[0],H[1] are the byteswapped halves; memory order gives lane0=H[0].
  q_t t1 = { Hin[0], Hin[1] };
  // xC2 lane = 0xc200000000000000 ; t2 = vshr.u64 xC2,#63 => each lane = 1
  // IN = ext8(t1,t1) => {t1.hi, t1.lo}
  q_t IN = qext8(t1, t1);
  // t0 = ext8(t2, xC2, #8) with t2 lanes=1 => t0 = {t2.hi=1, xC2.lo=0xc2..}
  q_t t0 = { 1, C2CONST };
  // t1b = vdup.32 t1[1]: duplicate 32-bit lane #1 of original t1 across; then
  // vshr.s32 #31 broadcasts the carry (sign) bit. t1[1] is bits[32..63] of lane0
  // = bits[32..63] of H[0]. Its top bit (bit63 of H[0]) sign-extended.
  uint64_t carrybit = (Hin[0] >> 63) & 1;
  uint64_t signmask = carrybit ? UINT64_C(0xffffffffffffffff) : 0; // vshr.s32 #31 per 32b lane
  // t2 = vshr.u64 IN,#63 => each lane = top bit of that lane of IN
  q_t t2 = { IN.lo>>63, IN.hi>>63 };
  // t2 &= t0
  t2.lo &= t0.lo; t2.hi &= t0.hi;
  // IN = vshl.i64 IN,#1 (per-lane <<1)
  IN.lo <<= 1; IN.hi <<= 1;
  // t2 = ext8(t2,t2) => swap halves
  t2 = qext8(t2, t2);
  // t0 &= t1(broadcast sign) : t0 lanes &= signmask
  t0.lo &= signmask; t0.hi &= signmask;
  // IN |= t2  (H<<<=1)
  IN.lo |= t2.lo; IN.hi |= t2.hi;
  // H = IN ^ t0   (twisted H)
  q_t H = qeor(IN, t0);
  // H = ext8(H,H)
  H = qext8(H, H);
  // store Htable[0] = H
  Htable[0]=H.lo; Htable[1]=H.hi;

  // ---- H^2 ----
  q_t t0H = qeor(qext8(H,H), H);          // Karatsuba pre: t0 = ext8(H,H)^H
  q_t Xl = clmul64(H.hi, H.hi);           // pmull2 Xl, H,H
  q_t Xh = clmul64(H.lo, H.lo);           // pmull  Xh, H,H
  q_t Xm = clmul64(t0H.lo, t0H.lo);       // pmull  Xm, t0,t0
  q_t t1r = reduce256(Xl, Xm, Xh);        // -> $t1 (H^2 reduced)
  q_t H2pre;                               // packed karatsuba
  q_t H2 = to_reg(t1r, &H2pre);           // H2 = ext8(t1,t1); t1^H2
  // pack Htable[1..2]: Hhl = ext8(t0, (t1^H2)) ; store Hhl then H2
  q_t Hhl = qext8(t0H, H2pre);
  Htable[2]=Hhl.lo; Htable[3]=Hhl.hi;     // Htable[1] slot (offset16)
  Htable[4]=H2.lo;  Htable[5]=H2.hi;      // Htable[2] slot (offset32)

  // helper "pre" for H (t0H already), and for H2 (H2pre)
  // ---- H^3 and H^4 ----
  // H^3 = H*H^2 ; H^4 = H^2*H^2
  q_t Xl3 = clmul64(H.hi, H2.hi),  Xh3 = clmul64(H.lo, H2.lo),  Xm3 = clmul64(t0H.lo, H2pre.lo);
  q_t Xl4 = clmul64(H2.hi,H2.hi),  Xh4 = clmul64(H2.lo,H2.lo),  Xm4 = clmul64(H2pre.lo,H2pre.lo);
  q_t t0_3 = reduce256(Xl3, Xm3, Xh3);    // H^3 reduced ($t0)
  q_t t1_4 = reduce256(Xl4, Xm4, Xh4);    // H^4 reduced ($t1)
  q_t H3 = qext8(t0_3,t0_3), H4 = qext8(t1_4,t1_4);
  q_t p3 = qeor(t0_3,H3),   p4 = qeor(t1_4,H4);
  q_t H34k = qext8(p3, p4);               // pack
  // store order is {H3, H34k, H4} (pack in the MIDDLE), per st1 {v23,v24,v25}
  Htable[6]=H3.lo;   Htable[7]=H3.hi;     // Htable[3] (off48)
  Htable[8]=H34k.lo; Htable[9]=H34k.hi;   // Htable[4] (off64)
  Htable[10]=H4.lo;  Htable[11]=H4.hi;    // Htable[5] (off80)

  // ---- H^5 and H^6 ----
  // asm: pmull2 Xl,H2,H3 ; pmull2 Yl,H3,H3 ; pmull Xh,H2,H3 ; pmull Yh,H3,H3
  //      pmull Xm,t0,t2(=ext8(H2,H2)^H2? actually t2=ext8(H2,H2)^H2) ; Ym,t0,t0
  // where at this point t0 = p3 (H3 pre), t1 = p4 (H4 pre), t2 recomputed:
  q_t t2H2 = qeor(qext8(H2,H2), H2);      // vext t2,H2,H2 ; veor t2,t2,H2  (.pl 185-188/230-233)
  q_t Xl5 = clmul64(H2.hi,H3.hi), Xh5 = clmul64(H2.lo,H3.lo), Xm5 = clmul64(p3.lo, t2H2.lo);
  q_t Xl6 = clmul64(H3.hi,H3.hi), Xh6 = clmul64(H3.lo,H3.lo), Xm6 = clmul64(p3.lo, p3.lo);
  q_t t0_5 = reduce256(Xl5, Xm5, Xh5);
  q_t t1_6 = reduce256(Xl6, Xm6, Xh6);
  q_t H5 = qext8(t0_5,t0_5), H6 = qext8(t1_6,t1_6);
  q_t p5 = qeor(t0_5,H5), p6 = qeor(t1_6,H6);
  q_t H56k = qext8(p5, p6);
  // store order {H5, H56k, H6}
  Htable[12]=H5.lo;   Htable[13]=H5.hi;   // Htable[6] (off96)
  Htable[14]=H56k.lo; Htable[15]=H56k.hi; // Htable[7] (off112)
  Htable[16]=H6.lo;   Htable[17]=H6.hi;   // Htable[8] (off128)

  // ---- H^7 and H^8 ----
  // asm: pmull2 Xl,H2,H5 ; pmull2 Yl,H2,H6 ; pmull Xh,H2,H5 ; pmull Yh,H2,H6
  //      pmull Xm,t0,t2 ; pmull Ym,t1,t2   with t0=p5,t1=p6, t2=ext8(H2,H2)^H2
  q_t Xl7 = clmul64(H2.hi,H5.hi), Xh7 = clmul64(H2.lo,H5.lo), Xm7 = clmul64(p5.lo, t2H2.lo);
  q_t Xl8 = clmul64(H2.hi,H6.hi), Xh8 = clmul64(H2.lo,H6.lo), Xm8 = clmul64(p6.lo, t2H2.lo);
  q_t t0_7 = reduce256(Xl7, Xm7, Xh7);
  q_t t1_8 = reduce256(Xl8, Xm8, Xh8);
  q_t H7 = qext8(t0_7,t0_7), H8 = qext8(t1_8,t1_8);
  q_t p7 = qeor(t0_7,H7), p8 = qeor(t1_8,H8);
  q_t H78k = qext8(p7, p8);
  // store order {H7, H78k, H8}
  Htable[18]=H7.lo;   Htable[19]=H7.hi;   // Htable[9]  (off144)
  Htable[20]=H78k.lo; Htable[21]=H78k.hi; // Htable[10] (off160)
  Htable[22]=H8.lo;   Htable[23]=H8.hi;   // Htable[11] (off176)
}
