# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#
# Python transcriptions of the HOL models in common/snappy (snappy_format.ml:
# the decoder; snappy_compress.ml: the compressors, phase by phase), and
# wrappers for the C API of a libsnappy.so, used by difftest.py to compare
# the models with the library. The library is loaded from $SNAPPY_LIB.

import ctypes, os

# ---- decoder (snappy_format.ml) ----


def varint_from(k, l, i):
    # returns (v, next_index) or None
    if k == 0 or i >= len(l): return None
    b = l[i]
    if k == 1:
        return (b, i+1) if b < 16 else None
    if b < 128: return (b, i+1)
    r = varint_from(k-1, l, i+1)
    if r is None: return None
    return (b - 128 + 128*r[0], r[1])

def varint(l): return varint_from(5, l, 0)

def le(bs):
    return sum(b << (8*j) for j, b in enumerate(bs))

def copy(off, n, out):
    for _ in range(n):
        out.append(out[len(out)-off])

def tag_step(m, l, i, out):
    # returns new index or None; mutates out
    if i >= len(l): return None
    c = l[i]; t = i+1; rem = len(l) - t; x = c // 4
    def lit(ln, j):
        if ln <= len(l) - j and len(out) + ln <= m:
            out.extend(l[j:j+ln]); return j + ln
        return None
    def cp(off, ln, j):
        if 1 <= off <= len(out) and len(out) + ln <= m:
            copy(off, ln, out); return j
        return None
    if c % 4 == 0:
        if x < 60: return lit(x+1, t)
        k = x - 59
        if rem < k: return None
        return lit(le(l[t:t+k]) + 1, t + k)
    if c % 4 == 1:
        if rem < 1: return None
        return cp(256*(x//8) + l[t], x % 8 + 4, t+1)
    if c % 4 == 2:
        if rem < 2: return None
        return cp(le(l[t:t+2]), x+1, t+2)
    if rem < 4: return None
    return cp(le(l[t:t+4]), x+1, t+4)

def decode(l):
    h = varint(l)
    if h is None: return None
    m, i = h
    out = []
    while i < len(l):
        i = tag_step(m, l, i, out)
        if i is None: return None
    return bytes(out) if len(out) == m else None


# ---- compressor (snappy_compress.ml) ----

def L32(I, p): return int.from_bytes(bytes(I[p:p+4]).ljust(4, b'\0'), 'little')
def L64(I, p): return int.from_bytes(bytes(I[p:p+8]).ljust(8, b'\0'), 'little')

def table_size(n):
    if n > 32768: return 32768
    if n < 256: return 256
    t = 1
    while t < n: t *= 2
    return t

def hash1(ts, v): return ((0x1e35a7bd * v) % 2**32) // 2**17 % ts
def hash4(ts, v): return ((2654435761 * v) % 2**32) // 2**18 % ts
def hash8(ts, v): return ((58295818150454627 * v) % 2**64) // 2**50 % ts

def mlen(I, a, b):
    m = 0
    while b + m < len(I) and I[a+m] == I[b+m]: m += 1
    return m

def bytelist_of_num(k, n): return [(n >> (8*j)) & 255 for j in range(k)]

def emit_literal(d):
    n = len(d) - 1
    if n < 60: return [4*n] + list(d)
    count = 1 if n < 256 else 2 if n < 65536 else 3 if n < 2**24 else 4
    return [4*(59+count)] + bytelist_of_num(count, n) + list(d)

def copy64(off, ln):
    if ln < 12 and off < 2048: return [1 + 4*(ln-4) + 32*(off//256), off % 256]
    return [2 + 4*(ln-1), off % 256, off // 256]

def emit_copy(off, ln):
    out = []
    while ln >= 68: out += copy64(off, 64); ln -= 64
    if ln > 64: return out + copy64(off, 60) + copy64(off, ln - 60)
    return out + copy64(off, ln)

def cf1(I):
    n = len(I); ts = table_size(n); T = [0]*ts; out = []
    ip_limit = n - 15
    # state machine
    ph = 5 if n < 15 else 1
    ip = 0; ne = 0; skip = 0; cand = 0; i = 0
    while ph != 0:
        if ph == 1:
            ne = ip; ip = ip + 1
            if ip + 16 <= ip_limit: ph = 6; i = 0
            else: ph = 2; skip = 32
        elif ph == 6:
            dw = L32(I, ip+i); e = hash1(ts, dw); c = T[e]; T[e] = ip + i
            if L32(I, c) == dw: ph = 3; ip = ip + i; cand = c
            elif i == 15: ph = 2; ip = ip + 16; skip = 48
            else: i += 1
        elif ph == 2:
            dw = L32(I, ip); e = hash1(ts, dw); b = skip // 32; nskip = skip + b; nip = ip + b
            if nip > ip_limit: ph = 5; ip = ne
            else:
                c = T[e]; T[e] = ip
                if L32(I, c) == dw: ph = 3; cand = c
                else: ip = nip; skip = nskip
        elif ph == 3:
            out += emit_literal(I[ne:ip]); ph = 4
        elif ph == 4:
            m = 4 + mlen(I, cand+4, ip+4); ip2 = ip + m
            out += emit_copy(ip - cand, m)
            if ip2 >= ip_limit: ph = 5; ip = ip2
            else:
                T[hash1(ts, L32(I, ip2-1))] = ip2 - 1
                e = hash1(ts, L32(I, ip2)); c = T[e]; T[e] = ip2
                ip = ip2
                if L32(I, ip2) == L32(I, c): cand = c
                else: ph = 1
        elif ph == 5:
            if ip < n: out += emit_literal(I[ip:n])
            ph = 0
    return out

def cf2(I):
    n = len(I); ts = table_size(n) // 2; T1 = [0]*ts; T2 = [0]*ts; out = []
    ip_limit = n - 15
    ph = 5 if n < 15 else 1
    ip = 0; ne = 0; skip = 0; cand = 0; ln = 0
    while ph != 0:
        if ph == 1:
            ne = ip; ip += 1; skip = 512; ph = 2
        elif ph == 2:
            d = L64(I, ip); e2 = hash8(ts, d); b = skip // 512; skip += 1; nip = ip + b
            if nip > ip_limit: ph = 5; ip = ne; continue
            c = T2[e2]; T2[e2] = ip
            if L32(I, c) == L32(I, ip):
                cand = c; ln = mlen(I, c+4, ip+4) + 4; ph = 3; continue
            e = hash4(ts, L32(I, ip)); c = T1[e]; T1[e] = ip
            if L32(I, c) == L32(I, ip):
                cand = c; ln = mlen(I, c+4, ip+4) + 4
                e2b = hash8(ts, L64(I, ip+1)); c2 = T2[e2b]; ln2 = mlen(I, c2, ip+1)
                if ln2 > ln:
                    T2[e2b] = ip; cand = c2; ln = ln2; ip += 1
                ph = 3; continue
            ip = nip
        elif ph == 3:
            # backtrack, table updates, literal
            while ip > ne and cand > 0 and I[ip-1] == I[cand-1]:
                ip -= 1; cand -= 1; ln += 1
            T2[hash8(ts, L64(I, ip+1))] = ip + 1
            T2[hash8(ts, L64(I, ip+2))] = ip + 2
            T1[hash4(ts, L32(I, ip+1))] = ip + 1
            if ip > ne: out += emit_literal(I[ne:ip])
            ph = 4
        elif ph == 4:
            out += emit_copy(ip - cand, ln); ip += ln
            if ip >= ip_limit: ph = 5; continue
            if ip > 7:
                T2[hash8(ts, L64(I, ip-7))] = ip - 7
                T2[hash8(ts, L64(I, ip-4))] = ip - 4
            T2[hash8(ts, L64(I, ip-3))] = ip - 3
            T2[hash8(ts, L64(I, ip-2))] = ip - 2
            T1[hash4(ts, L32(I, ip-2))] = ip - 2
            T1[hash4(ts, L32(I, ip-1))] = ip - 1
            e = hash8(ts, L64(I, ip)); c = T2[e]; T2[e] = ip
            if L32(I, ip) == L32(I, c):
                cand = c; ln = mlen(I, c+4, ip+4) + 4; continue
            e = hash4(ts, L32(I, ip)); c = T1[e]; T1[e] = ip
            if L32(I, ip) == L32(I, c):
                cand = c; ln = mlen(I, c+4, ip+4) + 4; continue
            ph = 1
        elif ph == 5:
            if ip < n: out += emit_literal(I[ip:n])
            ph = 0
    return out

def varint_encode(n):
    out = []
    while True:
        if n < 128: out.append(n); return out
        out.append(n % 128 + 128); n //= 128

def compress(I, level):
    n = len(I)
    if n >= 2**32: return []
    out = varint_encode(n)
    for s in range(0, n, 65536):
        frag = list(I[s:s+65536])
        out += cf1(frag) if level == 1 else cf2(frag)
    return out

# ---- the library ----

L = ctypes.CDLL(os.environ['SNAPPY_LIB'])

# libsnappy wrappers
def c_uncompress(l, outlen=None):
    src = bytes(l)
    n = ctypes.c_size_t()
    st = L.snappy_uncompressed_length(src, ctypes.c_size_t(len(src)), ctypes.byref(n))
    hdr = n.value if st == 0 else None
    cap = outlen if outlen is not None else (hdr if hdr is not None else 0)
    buf = ctypes.create_string_buffer(max(cap, 1) + 64)
    ul = ctypes.c_size_t(cap)
    st2 = L.snappy_uncompress(src, ctypes.c_size_t(len(src)), buf, ctypes.byref(ul))
    return st, hdr, st2, (buf.raw[:ul.value] if st2 == 0 else None), ul.value

def c_validate(l):
    src = bytes(l)
    return L.snappy_validate_compressed_buffer(src, ctypes.c_size_t(len(src)))

L.snappy_max_compressed_length.restype = ctypes.c_size_t
L.snappy_max_compressed_length.argtypes = [ctypes.c_size_t]
def c_compress(data, level=1):
    src = bytes(data)
    cap = L.snappy_max_compressed_length(len(src))
    buf = ctypes.create_string_buffer(cap + 1)
    cl = ctypes.c_size_t(cap)
    st = L.snappy_compress_with_level(src, ctypes.c_size_t(len(src)), ctypes.c_int(level), buf, ctypes.byref(cl))
    assert st == 0, st
    return buf.raw[:cl.value]
