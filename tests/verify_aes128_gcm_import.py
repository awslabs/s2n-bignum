#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

"""Verify imported AWS-LC C reference bodies and AES128 GCM vectors.

Usage: python3 verify_aes128_gcm_import.py [path/to/aws-lc]
The AWS-LC checkout is a read-only source; no AWS-LC build is required.
"""
import hashlib
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
AWS_LC = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE.parent.parent / "aws-lc"
source = (HERE / "test.c").read_bytes()
marker = re.compile(rb"^// AWS-LC verbatim BEGIN ([A-Za-z0-9_]+): ([^:\n]+):([0-9]+)\n", re.M)
expected = {
    "CRYPTO_load_u32_be", "CRYPTO_store_u32_be", "CRYPTO_load_u64_be",
    "CRYPTO_store_u64_be", "gcm_mul64_nohw", "gcm_init_nohw",
    "gcm_polyval_nohw", "gcm_gmult_nohw", "gcm_ghash_nohw",
    "hw_gcm_encrypt", "CRYPTO_gcm128_encrypt_ctr32",
}
seen = set()
for match in marker.finditer(source):
    name, relative, line = match.groups()
    end = source.index(b"// AWS-LC verbatim END " + name + b"\n", match.end())
    reference = source[match.end():end]
    upstream = (AWS_LC / relative.decode()).read_bytes()
    if not reference or reference not in upstream:
        raise SystemExit("FAIL: edited or absent AWS-LC function " + name.decode())
    at_line = b"".join(upstream.splitlines(keepends=True)[int(line) - 1:])
    if not at_line.startswith(reference):
        raise SystemExit("FAIL: incorrect AWS-LC source line for " + name.decode())
    seen.add(name.decode())
    print("OK: %s %s:%s sha256=%s" % (
        name.decode(), relative.decode(), line.decode(),
        hashlib.sha256(reference).hexdigest()))
if seen != expected:
    raise SystemExit("FAIL: AWS-LC reference function set differs: " + repr(seen ^ expected))
print("All 11 AWS-LC C function bodies are verbatim source substrings.")

# Parse the ten fixed records in the named new KAT function. Matching all six
# fields at the recorded KEY line prevents vector invention or mixed records.
kat_start = source.index(b"int test_known_values_aes128_gcm_enc_alt(void)")
kat_end = source.index(b"  size_t i;", kat_start)
kat_source = source[kat_start:kat_end]
records = re.findall(
    rb'\{\s*(\d+),\s*((?:"[0-9a-fA-F]*"\s*,?\s*){6})\}', kat_source)
if len(records) != 10:
    raise SystemExit("FAIL: expected ten fixed AWS-LC AES128 vectors")
vector_path = AWS_LC / "crypto/cipher_extra/test/aes_128_gcm_tests.txt"
upstream_lines = vector_path.read_text().splitlines()
field_names = ["KEY", "NONCE", "AD", "IN", "CT", "TAG"]
for key_line, quoted in records:
    line = int(key_line)
    if not upstream_lines[line - 1].startswith("KEY:"):
        raise SystemExit("FAIL: vector source line is not KEY: " + str(line))
    fields = {}
    for text in upstream_lines[line - 1:]:
        if not text.strip():
            break
        if ":" in text:
            name, value = text.split(":", 1)
            fields[name] = value.strip().strip('"')
    values = [v.decode() for v in re.findall(rb'"([0-9a-fA-F]*)"', quoted)]
    if values != [fields[name] for name in field_names]:
        raise SystemExit("FAIL: vector fields differ at upstream KEY line " + str(line))
    if len(values[0]) != 32 or not values[3] or len(values[3]) % 32:
        raise SystemExit("FAIL: vector is not nonempty AES128 whole blocks")
    print("OK: AWS-LC AES128 KAT KEY line %d all six fields verbatim, %d bytes" %
          (line, len(values[3]) // 2))
print("All 10 AES128 KAT records match their AWS-LC provenance.")
