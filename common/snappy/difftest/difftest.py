# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#
# Differential tests of the HOL models (as transcribed in snappy_model.py)
# against libsnappy.so:
#
#   SNAPPY_LIB=<libsnappy.so> python3 difftest.py decode <seed> <n> <testdata-dir>
#   SNAPPY_LIB=<libsnappy.so> python3 difftest.py tags <seed> <n>
#   SNAPPY_LIB=<libsnappy.so> python3 difftest.py compress <seed> <n> <testdata-dir>
#   SNAPPY_LIB=<libsnappy.so> python3 difftest.py files <testdata-dir>
#
# "decode" mutates valid streams, "tags" generates random tag sequences
# (copy offsets biased to 0, the output length and one more), "compress"
# compresses varied inputs at levels 1 and 2 and compares the bytes.

import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from snappy_model import *

def check_decode(l):
    d = decode(l)
    st, hdr, st2, out, ul = c_uncompress(l)
    v = c_validate(l)
    h = varint(l)
    assert (st == 0) == (h is not None), bytes(l).hex()
    if h is not None: assert hdr == h[0], bytes(l).hex()
    assert (st2 == 0) == (d is not None), ("uncompress", bytes(l).hex())
    if d is not None: assert out == d, bytes(l).hex()
    assert (v == 0) == (d is not None), ("validate", bytes(l).hex())
    return d is not None

def enc_varint(m):
    enc = []
    while True:
        if m < 128: enc.append(m); return enc
        enc.append(m % 128 + 128); m //= 128

def corpus_of(tdir):
    fs = ['alice29.txt','html','urls.10K','fireworks.jpeg','geo.protodata','paper-100k.pdf']
    datas = [open(os.path.join(tdir, f),'rb').read() for f in fs]
    corpus = []
    for d in datas:
        for _ in range(30):
            a = random.randrange(len(d)); n = random.choice([0,1,3,10,70,300,2000,70000])
            for lv in (1, 2): corpus.append(c_compress(d[a:a+n], lv))
    corpus.append(c_compress(b'a'*100000)); corpus.append(c_compress(bytes(range(256))*300))
    return corpus

def run_decode(n, tdir):
    corpus = corpus_of(tdir)
    for c in corpus: assert check_decode(list(c))
    nv = 0
    for _ in range(n):
        c = list(random.choice(corpus)); k = random.randrange(6)
        if k == 0 and c: c[random.randrange(len(c))] = random.randrange(256)
        elif k == 1 and c: c = c[:random.randrange(len(c))]
        elif k == 2: c = c + [random.randrange(256) for _ in range(random.randrange(1,6))]
        elif k == 3:
            h = varint(c); rest = c[h[1]:] if h else c
            m = random.choice([0,1,2,(h[0] if h else 0)+random.randrange(-3,4)])
            c = enc_varint(max(m,0)) + rest
        elif k == 4: c = [random.randrange(0,80)] + [random.randrange(256) for _ in range(random.randrange(0,40))]
        else: c = [random.randrange(256) for _ in range(random.randrange(0,12))]
        nv += check_decode(c)
    print("decode ok: %d valid streams, %d mutations (%d valid)" % (len(corpus), n, nv))

def gen_tags():
    out = 0; s = []
    for _ in range(random.randrange(1, 200)):
        if random.randrange(10) < 3:
            n = random.choice([1,2,5,16,17,40,60,61,62,100,300])
            if n <= 60: s.append((n-1)*4)
            else:
                ll = n-1; nb = random.choice([1,2,3,4]) if ll < 256 else 2
                s.append((59+nb)*4); s += list(ll.to_bytes(nb,'little'))
            s += [random.randrange(256) for _ in range(n)]; out += n
        else:
            off = random.choice([1, 2, 3, out, out, max(out-1,1), random.randrange(1,out+1) if out else 1]*12 + [0, out+1])
            if out == 0 and random.random() < 0.9: continue
            t = random.choice([1,2,3])
            if t == 1:
                ln = random.randrange(4,12); off = off if off < 2048 else random.randrange(1,2048)
                s += [1 | ((ln-4)<<2) | ((off>>8)<<5), off & 255]
            elif t == 2:
                ln = random.randrange(1,65); off = off if off < 65536 else random.randrange(1,65536)
                s += [2 | ((ln-1)<<2)] + list(off.to_bytes(2,'little'))
            else:
                ln = random.randrange(1,65); s += [3 | ((ln-1)<<2)] + list(off.to_bytes(4,'little'))
            out += ln
    m = random.choice([out]*10+[out-1, out+1, random.randrange(out+1)])
    return enc_varint(max(m,0)) + s

def run_tags(n):
    nv = sum(check_decode(gen_tags()) for _ in range(n))
    print("tags ok: %d sequences (%d valid)" % (n, nv))

def run_compress(n, tdir):
    fs = sorted(os.listdir(tdir))
    datas = [open(os.path.join(tdir, f),'rb').read() for f in fs]
    for _ in range(n):
        k = random.randrange(5)
        if k == 0:
            d = random.choice(datas); a = random.randrange(len(d))
            I = d[a:a+random.choice([0,1,5,14,15,16,17,30,31,32,33,100,255,256,257,1000,5000,65535,65536,65537,140000])]
        elif k == 1: I = bytes(random.randrange(256) for _ in range(random.randrange(0, 300)))
        elif k == 2:
            alpha = bytes(random.sample(range(256), random.randrange(1, 5)))
            I = bytes(random.choice(alpha) for _ in range(random.randrange(0, 3000)))
        elif k == 3: I = random.choice([b'a', b'ab', b'abc', b'\0']) * random.randrange(0, 70000)
        else: d = random.choice(datas); I = d[:random.randrange(len(d))]
        for lv in (1, 2):
            m = bytes(compress(I, lv))
            assert c_compress(I, lv) == m, ("level", lv, I[:64].hex(), len(I))
            assert decode(list(m)) == I
    print("compress ok: %d inputs, levels 1 and 2" % n)

def run_files(tdir):
    for f in sorted(os.listdir(tdir)):
        I = open(os.path.join(tdir, f),'rb').read()
        for lv in (1, 2): assert c_compress(I, lv) == bytes(compress(I, lv)), (f, lv)
    print("files ok")

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'files': run_files(sys.argv[2]); sys.exit(0)
    random.seed(int(sys.argv[2])); n = int(sys.argv[3])
    if cmd == 'decode': run_decode(n, sys.argv[4])
    elif cmd == 'tags': run_tags(n)
    elif cmd == 'compress': run_compress(n, sys.argv[4])
