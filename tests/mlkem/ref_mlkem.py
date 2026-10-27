# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# A direct Python transcription of the HOL definitions in common/fips203.ml,
# used only to cross-check the specification against NIST ACVP vectors and
# to produce intermediate values for evaluation in HOL. Not optimized.
import hashlib

Q = 3329

def br7(i):
    return int(format(i, '07b')[::-1], 2)

def gamma(i):
    return pow(17, 2 * br7(i) + 1, Q)

# Little-endian numeric view of byte strings
def num(b): return int.from_bytes(bytes(b), 'little')
def tobytes(n, length): return (n % (256 ** length)).to_bytes(length, 'little')

# mlkem_encode d n f / mlkem_decode d b i
def encode(d, n, f):
    N = sum((f[i] % (2 ** d)) << (d * i) for i in range(n))
    return tobytes(N, (d * n) // 8)
def decode(d, b, i):
    x = (num(b) >> (d * i)) % (2 ** d)
    return x % Q if d == 12 else x

def mlround(a, b): return (2 * a + b) // (2 * b)
def compress(d, x): return mlround(2 ** d * x, Q) % (2 ** d)
def decompress(d, y): return mlround(Q * y, 2 ** d)

def poly(a): return [a(i) % Q for i in range(256)]

# R_q arithmetic on coefficient lists
def radd(f, g): return [(x + y) % Q for x, y in zip(f, g)]
def rsub(f, g): return [(x - y) % Q for x, y in zip(f, g)]
def rmul(f, g):
    h = [0] * 512
    for i in range(256):
        if f[i]:
            for j in range(256):
                h[i + j] += f[i] * g[j]
    return [(h[k] - h[k + 256]) % Q for k in range(256)]
def rdot(u, v):
    acc = [0] * 256
    for a, b in zip(u, v): acc = radd(acc, rmul(a, b))
    return acc

# mlkem_ntt (explicit-sum form, theorem MLKEM_NTT_EXPLICIT) and its inverse
def ntt(f):
    return [sum(f[2 * j + (k % 2)] * pow(gamma(k // 2), j, Q)
                for j in range(128)) % Q for k in range(256)]
def ntt_inv(a):
    inv128 = pow(128, -1, Q)
    return [inv128 * sum(a[2 * i + (k % 2)] * pow(gamma(i), -(k // 2), Q)
                         for i in range(128)) % Q for k in range(256)]

def slice_(a, n, b): return bytes(b[a:a + n])

# Section 4.1 functions
def prf(eta, s, b):
    return hashlib.shake_256(bytes(s) + bytes([b])).digest(64 * eta)
def H(s): return hashlib.sha3_256(bytes(s)).digest()
def J(s): return hashlib.shake_256(bytes(s)).digest(32)
def G(c):
    h = hashlib.sha3_512(bytes(c)).digest()
    return h[:32], h[32:]

def sample_ntt(b):
    stream = hashlib.shake_128(bytes(b)).digest(3 * 1024)
    N = num(stream)
    out, j = [], 0
    while len(out) < 256:
        c = (N >> (12 * j)) % 4096
        if c < Q: out.append(c)
        j += 1
    return out

def cbd(eta, b):
    N = num(b)
    bit = lambda t: (N >> t) & 1
    return poly(lambda i: sum(bit(2 * eta * i + j) for j in range(eta))
                        - sum(bit(2 * eta * i + eta + j) for j in range(eta)))

def flat(vec):   # field 256*i+j = coefficient j of element i
    return [vec[n // 256][n % 256] for n in range(256 * len(vec))]

def kpke_keygen(p, d):
    k, eta1, eta2, du, dv = p
    rho, sigma = G(bytes(d) + bytes([k]))
    A = [[ntt_inv(sample_ntt(rho + bytes([j, i]))) for j in range(k)]
         for i in range(k)]
    s = [cbd(eta1, prf(eta1, sigma, i)) for i in range(k)]
    e = [cbd(eta1, prf(eta1, sigma, k + i)) for i in range(k)]
    t = [radd(rdot(A[i], s), e[i]) for i in range(k)]
    ek = encode(12, 256 * k, flat([ntt(ti) for ti in t])) + rho
    dk = encode(12, 256 * k, flat([ntt(si) for si in s]))
    return ek, dk

def kpke_encrypt(p, ek, m, r):
    k, eta1, eta2, du, dv = p
    t = [ntt_inv([decode(12, ek, 256 * i + j) for j in range(256)])
         for i in range(k)]
    rho = slice_(384 * k, 32, ek)
    A = [[ntt_inv(sample_ntt(rho + bytes([j, i]))) for j in range(k)]
         for i in range(k)]
    y = [cbd(eta1, prf(eta1, r, i)) for i in range(k)]
    e1 = [cbd(eta2, prf(eta2, r, k + i)) for i in range(k)]
    e2 = cbd(eta2, prf(eta2, r, 2 * k))
    mu = poly(lambda j: decompress(1, decode(1, m, j)))
    u = [radd(rdot([A[j][i] for j in range(k)], y), e1[i]) for i in range(k)]
    v = radd(radd(rdot(t, y), e2), mu)
    return (encode(du, 256 * k, [compress(du, x) for x in flat(u)]) +
            encode(dv, 256, [compress(dv, x) for x in v]))

def kpke_decrypt(p, dk, c):
    k, eta1, eta2, du, dv = p
    c2 = slice_(32 * du * k, 32 * dv, c)
    u = [poly(lambda j: decompress(du, decode(du, c, 256 * i + j)))
         for i in range(k)]
    v = poly(lambda j: decompress(dv, decode(dv, c2, j)))
    s = [ntt_inv([decode(12, dk, 256 * i + j) for j in range(256)])
         for i in range(k)]
    w = rsub(v, rdot(s, u))
    return encode(1, 256, [compress(1, x) for x in w])

def keygen_internal(p, d, z):
    ek, dk = kpke_keygen(p, d)
    return ek, dk + ek + H(ek) + bytes(z)

def encaps_internal(p, ek, m):
    kk, r = G(bytes(m) + H(ek))
    return kk, kpke_encrypt(p, ek, m, r)

def decaps_internal(p, dk, c):
    k = p[0]
    dk_pke = slice_(0, 384 * k, dk)
    ek_pke = slice_(384 * k, 384 * k + 32, dk)
    h = slice_(768 * k + 32, 32, dk)
    z = slice_(768 * k + 64, 32, dk)
    m1 = kpke_decrypt(p, dk_pke, c)
    kk1, r1 = G(m1 + h)
    kbar = J(z + bytes(c))
    return kk1 if kpke_encrypt(p, ek_pke, m1, r1) == bytes(c) else kbar

PARAMS = {'ML-KEM-512': (2, 3, 2, 10, 4), 'ML-KEM-768': (3, 2, 2, 10, 4),
          'ML-KEM-1024': (4, 2, 2, 11, 5)}

# mlkem_ek_check and mlkem_decaps_check (dk part; ciphertext length aside)
def ek_check(p, ek):
    k = p[0]
    return (len(ek) == 384 * k + 32 and
            encode(12, 256 * k, [decode(12, ek, n) for n in range(256 * k)])
            == slice_(0, 384 * k, ek))

def dk_check(p, dk):
    k = p[0]
    return (len(dk) == 768 * k + 96 and
            H(slice_(384 * k, 384 * k + 32, dk)) ==
            slice_(768 * k + 32, 32, dk))
