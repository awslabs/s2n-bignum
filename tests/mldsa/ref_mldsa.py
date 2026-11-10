# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# A direct Python transcription of the HOL definitions in common/fips204.ml,
# used only to cross-check the specification against NIST ACVP vectors and
# to produce intermediate values for evaluation in HOL. Not optimized,
# except that products in R_q are computed by a convolution.
import hashlib
import numpy as np

Q = 8380417

def br8(i):
    return int(format(i, '08b')[::-1], 2)

# Little-endian numeric view of byte strings
def num(b): return int.from_bytes(bytes(b), 'little')
def tobytes(n, length): return (n % (256 ** length)).to_bytes(length, 'little')

# mldsa_poly: an element of R_q from a coefficient function (list of 256)
def poly(a): return [a(i) % Q for i in range(256)]

# R_q arithmetic on coefficient lists
def radd(f, g): return [(x + y) % Q for x, y in zip(f, g)]
def rsub(f, g): return [(x - y) % Q for x, y in zip(f, g)]
def rmul(f, g):
    h = np.convolve(np.array(f, dtype=np.int64) % Q,
                    np.array(g, dtype=np.int64) % Q)
    h = [int(x) for x in h] + [0]
    return [(h[k] - h[k + 256]) % Q for k in range(256)]
def rdot(u, v):
    acc = [0] * 256
    for a, b in zip(u, v): acc = radd(acc, rmul(a, b))
    return acc

# mldsa_ntt (evaluation at zeta^(2 br8(i) + 1)) and its inverse by the
# explicit inverse formula (sum over the 256 points)
ROOTS = [pow(1753, 2 * br8(i) + 1, Q) for i in range(256)]
def ntt(f):
    return [sum(f[j] * pow(r, j, Q) for j in range(256)) % Q for r in ROOTS]
INV256 = pow(256, -1, Q)
def ntt_inv(a):
    return [INV256 * sum(a[i] * pow(ROOTS[i], -j, Q) for i in range(256)) % Q
            for j in range(256)]

def modpm(a, m):
    r = a % m
    return r if 2 * r <= m else r - m

def norm_lt(b, w):
    return all(abs(modpm(w[i], Q)) < b for i in range(256))

def vec_norm_lt(n, b, v):
    return all(norm_lt(b, v[i]) for i in range(n))

def power2round(r):
    rp = r % Q
    r0 = modpm(rp, 8192)
    return (rp - r0) // 8192, r0

def decompose(g2, r):
    rp = r % Q
    r0 = modpm(rp, 2 * g2)
    if rp - r0 == Q - 1: return 0, r0 - 1
    return (rp - r0) // (2 * g2), r0

def highbits(g2, r): return decompose(g2, r)[0]
def lowbits(g2, r): return decompose(g2, r)[1]
def makehint(g2, z, r): return highbits(g2, r) != highbits(g2, r + z)
def usehint(g2, h, r):
    m = (Q - 1) // (2 * g2)
    r1, r0 = decompose(g2, r)
    if h and 0 < r0: return (r1 + 1) % m
    if h: return (r1 - 1) % m
    return r1

def bitlen(n):
    c = 0
    while not n < 2 ** c: c += 1
    return c

def encode(c, n, f):
    N = sum((f(i) % (2 ** c)) << (c * i) for i in range(n))
    return tobytes(N, (c * n) // 8)

def field(c, b, i): return (num(b) >> (c * i)) % (2 ** c)

def slice_(a, n, b):
    b = bytes(b) + bytes(max(0, a + n - len(b)))
    return b[a:a + n]

def hint_count(h, p): return sum(1 for pp in range(p) if h(pp))

def hintbitpack(k, omega, h):
    pos = [p for p in range(256 * k) if h(p)]
    out = []
    for t in range(omega + k):
        if t < omega:
            out.append(pos[t] % 256 if t < len(pos) else 0)
        else:
            out.append(hint_count(h, 256 * (t - omega + 1)) % 256)
    return bytes(out)

def hint_start(omega, y, i): return 0 if i == 0 else y[omega + i - 1]

def hint_ok(k, omega, y):
    for i in range(k):
        if not (hint_start(omega, y, i) <= y[omega + i] <= omega): return False
    for i in range(k):
        for t in range(hint_start(omega, y, i) + 1, y[omega + i]):
            if not y[t - 1] < y[t]: return False
    for t in range(hint_start(omega, y, k), omega):
        if y[t] != 0: return False
    return True

def hintbitunpack(k, omega, y):
    if not hint_ok(k, omega, y): return None
    def h(p):
        if not p < 256 * k: return False
        i = p // 256
        return any(y[t] == p % 256
                   for t in range(hint_start(omega, y, i), y[omega + i]))
    return h

def H(s, n): return hashlib.shake_256(bytes(s)).digest(n)

def rej_ntt_poly(rho):
    s = hashlib.shake_128(bytes(rho)).digest(3 * 2048)
    out, j = [], 0
    while len(out) < 256:
        c = s[3 * j] + 256 * s[3 * j + 1] + 65536 * (s[3 * j + 2] % 128)
        if c < Q: out.append(c)
        j += 1
    return out

def rej_bounded_poly(eta, rho):
    s = hashlib.shake_256(bytes(rho)).digest(4096)
    out, t = [], 0
    while len(out) < 256:
        b = (s[t // 2] // (16 ** (t % 2))) % 16
        ok = b < 15 if eta == 2 else b < 9
        if ok: out.append(2 - (b % 5) if eta == 2 else 4 - b)
        t += 1
    return [x % Q for x in out]

def expand_a(rho, i, j):
    return ntt_inv(rej_ntt_poly(bytes(rho) + bytes([j, i])))

def expand_mask(g1, rho, kappa, r):
    c = 1 + bitlen(g1 - 1)
    v = H(bytes(rho) + tobytes(kappa + r, 2), 32 * c)
    return poly(lambda i: g1 - field(c, v, i))

def sample_in_ball(tau, rho):
    s = hashlib.shake_256(bytes(rho)).digest(4096)
    signs = num(s[:8])
    c = [0] * 256
    p = 8
    for k in range(tau):
        i = 256 - tau + k
        while not s[p] <= i: p += 1
        j = s[p]
        sg = -1 if (signs >> k) & 1 else 1
        c = [sg if t == j else (c[j] if t == i else c[t]) for t in range(256)]
        p += 1
    return poly(lambda t: c[t])

def keygen_internal(P, xi):
    k, l, eta, tau, lam, g1, g2, omega = P
    seeds = H(bytes(xi) + bytes([k, l]), 128)
    rho, rhop, key = seeds[0:32], seeds[32:96], seeds[96:128]
    A = [[expand_a(rho, i, j) for j in range(l)] for i in range(k)]
    s1 = [rej_bounded_poly(eta, rhop + tobytes(i, 2)) for i in range(l)]
    s2 = [rej_bounded_poly(eta, rhop + tobytes(l + i, 2)) for i in range(k)]
    t = [radd(rdot(A[i], s1), s2[i]) for i in range(k)]
    t1 = lambda n: power2round(t[n // 256][n % 256])[0]
    t0 = lambda n: power2round(t[n // 256][n % 256])[1]
    pk = rho + encode(10, 256 * k, t1)
    c = bitlen(2 * eta)
    s1b = encode(c, 256 * l, lambda n: eta - modpm(s1[n // 256][n % 256], Q))
    s2b = encode(c, 256 * k, lambda n: eta - modpm(s2[n // 256][n % 256], Q))
    t0b = encode(13, 256 * k, lambda n: 4096 - t0(n))
    return pk, rho + key + H(pk, 64) + s1b + s2b + t0b

def sign_attempt(P, A, s1, s2, t0, mu, rhopp, kappa):
    k, l, eta, tau, lam, g1, g2, omega = P
    y = [expand_mask(g1, rhopp, kappa, i) for i in range(l)]
    w = [rdot(A[i], y) for i in range(k)]
    w1 = lambda n: highbits(g2, w[n // 256][n % 256])
    ct = H(bytes(mu) + encode(bitlen((Q - 1) // (2 * g2) - 1), 256 * k, w1),
           lam // 4)
    c = sample_in_ball(tau, ct)
    z = [radd(y[i], rmul(c, s1[i])) for i in range(l)]
    r = [rsub(w[i], rmul(c, s2[i])) for i in range(k)]
    ct0 = [rmul(c, t0[i]) for i in range(k)]
    def h(p):
        if not p < 256 * k: return False
        i, j = p // 256, p % 256
        return makehint(g2, -ct0[i][j], radd(r[i], ct0[i])[j])
    beta = tau * eta
    if (vec_norm_lt(l, g1 - beta, z) and
        all(abs(lowbits(g2, r[i][j])) < g2 - beta
            for i in range(k) for j in range(256)) and
        vec_norm_lt(k, g2, ct0) and
        hint_count(h, 256 * k) <= omega):
        zb = encode(1 + bitlen(g1 - 1), 256 * l,
                    lambda n: g1 - modpm(z[n // 256][n % 256], Q))
        return bytes(ct) + zb + hintbitpack(k, omega, h)
    return None

def sign_mu(P, sk, mu, rnd, maxatt=1000):
    k, l, eta, tau, lam, g1, g2, omega = P
    c = bitlen(2 * eta)
    rho, key = slice_(0, 32, sk), slice_(32, 32, sk)
    s1b = slice_(128, 32 * c * l, sk)
    s2b = slice_(128 + 32 * c * l, 32 * c * k, sk)
    t0b = slice_(128 + 32 * c * (l + k), 416 * k, sk)
    s1 = [poly(lambda j, i=i: eta - field(c, s1b, 256 * i + j))
          for i in range(l)]
    s2 = [poly(lambda j, i=i: eta - field(c, s2b, 256 * i + j))
          for i in range(k)]
    t0 = [poly(lambda j, i=i: 4096 - field(13, t0b, 256 * i + j))
          for i in range(k)]
    rhopp = H(bytes(key) + bytes(rnd) + bytes(mu), 64)
    A = [[expand_a(rho, i, j) for j in range(l)] for i in range(k)]
    for n in range(maxatt):
        s = sign_attempt(P, A, s1, s2, t0, mu, rhopp, l * n)
        if s is not None: return s
    return None

def sign_internal(P, sk, m, rnd):
    return sign_mu(P, sk, H(slice_(64, 64, sk) + bytes(m), 64), rnd)

def verify_mu(P, pk, mu, sg):
    k, l, eta, tau, lam, g1, g2, omega = P
    c = 1 + bitlen(g1 - 1)
    if len(pk) != 32 + 320 * k: return False
    if len(sg) != lam // 4 + 32 * c * l + omega + k: return False
    rho, t1b = slice_(0, 32, pk), slice_(32, 320 * k, pk)
    t1 = [poly(lambda j, i=i: 8192 * field(10, t1b, 256 * i + j))
          for i in range(k)]
    ct = slice_(0, lam // 4, sg)
    zb = slice_(lam // 4, 32 * c * l, sg)
    hb = slice_(lam // 4 + 32 * c * l, omega + k, sg)
    z = [poly(lambda j, i=i: g1 - field(c, zb, 256 * i + j)) for i in range(l)]
    h = hintbitunpack(k, omega, hb)
    if h is None: return False
    cc = sample_in_ball(tau, ct)
    A = [[expand_a(rho, i, j) for j in range(l)] for i in range(k)]
    w = [rsub(rdot(A[i], z), rmul(cc, t1[i])) for i in range(k)]
    w1 = lambda n: usehint(g2, h(n), w[n // 256][n % 256])
    return (vec_norm_lt(l, g1 - tau * eta, z) and
            H(bytes(mu) + encode(bitlen((Q - 1) // (2 * g2) - 1), 256 * k, w1),
              lam // 4) == bytes(ct))

def verify_internal(P, pk, m, sg):
    return verify_mu(P, pk, H(H(pk, 64) + bytes(m), 64), sg)

def keygen(P, xi): return keygen_internal(P, xi)

def sign(P, sk, m, ctx, rnd):
    if 255 < len(ctx): return None
    return sign_internal(P, sk, bytes([0, len(ctx)]) + bytes(ctx) + bytes(m),
                         rnd)

def verify(P, pk, m, sg, ctx):
    if 255 < len(ctx): return None
    return verify_internal(P, pk,
                           bytes([0, len(ctx)]) + bytes(ctx) + bytes(m), sg)

def oid(n): return bytes([0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                          0x04, 0x02, n])

def hash_sign(P, sk, o, ph, ctx, rnd):
    if 255 < len(ctx): return None
    return sign_internal(P, sk, bytes([1, len(ctx)]) + bytes(ctx) + bytes(o) +
                         bytes(ph), rnd)

def hash_verify(P, pk, o, ph, sg, ctx):
    return (len(ctx) <= 255 and
            verify_internal(P, pk, bytes([1, len(ctx)]) + bytes(ctx) +
                            bytes(o) + bytes(ph), sg))

MLDSA44 = (4, 4, 2, 39, 128, 131072, 95232, 80)
MLDSA65 = (6, 5, 4, 49, 192, 524288, 261888, 55)
MLDSA87 = (8, 7, 2, 60, 256, 524288, 261888, 75)
PARAMS = {'ML-DSA-44': MLDSA44, 'ML-DSA-65': MLDSA65, 'ML-DSA-87': MLDSA87}
