#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

"""Verify imported AWS-LC C reference bodies and AES128 GCM vectors.

Usage: python3 verify_aes128_gcm_import.py [path/to/aws-lc]
The AWS-LC checkout is a read-only source; no AWS-LC build is required.
"""
import hashlib
import json
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

# Check the shared whole-block vector suites against their original corpora.
# Match every field and the complete eligible record set, so invented, mixed,
# duplicated or omitted records cannot pass the provenance check.
vector_path = AWS_LC / "crypto/cipher_extra/test/aes_128_gcm_tests.txt"
upstream_lines = vector_path.read_text().splitlines()
field_names = ["KEY", "NONCE", "AD", "IN", "CT", "TAG"]
eligible = {}
for index, text in enumerate(upstream_lines):
    if not text.startswith("KEY:"):
        continue
    fields = {}
    for entry in upstream_lines[index:]:
        if not entry.strip():
            break
        if ":" in entry:
            name, value = entry.split(":", 1)
            fields[name] = value.strip().strip('"')
    if (len(fields.get("KEY", "")) == 32 and
            len(fields.get("TAG", "")) == 32 and fields.get("IN") and
            len(fields["IN"]) % 32 == 0):
        eligible[index + 1] = [fields[name] for name in field_names]
kat_source = (HERE / "known_value_tests_gcm_128.h").read_bytes()
records = re.findall(
    rb"// Vector \d+ \(aes_128_gcm_tests.txt line (\d+)\):[^\n]*\n"
    rb"\s*GCM_KAT\((.*?)\);", kat_source, re.S)
if len(records) != 18 or len(eligible) != 18:
    raise SystemExit("FAIL: expected all 18 whole-block AWS-LC AES128 vectors")
seen_lines = set()
for key_line, quoted in records:
    line = int(key_line)
    values = [v.decode() for v in re.findall(rb'"([0-9a-fA-F]*)"', quoted)]
    if line in seen_lines or values != eligible.get(line):
        raise SystemExit("FAIL: vector fields differ at upstream KEY line " + str(line))
    seen_lines.add(line)
    print("OK: AWS-LC AES128 KAT KEY line %d all six fields verbatim, %d bytes" %
          (line, len(values[3]) // 2))
if seen_lines != set(eligible):
    raise SystemExit("FAIL: AWS-LC whole-block AES128 vector set differs")
print("All 18 shared AES128 KAT records match their AWS-LC provenance.")

wycheproof_path = AWS_LC / (
    "third_party/vectors/upstream/wycheproof/testvectors_v1/aes_gcm_test.json")
wycheproof = json.loads(wycheproof_path.read_text())
eligible = {}
field_names = ["key", "iv", "aad", "msg", "ct", "tag"]
for group in wycheproof["testGroups"]:
    if group["keySize"] != 128 or group["tagSize"] != 128:
        continue
    for test in group["tests"]:
        if test["result"] == "valid" and test["msg"] and len(test["msg"]) % 32 == 0:
            eligible[test["tcId"]] = [test[name] for name in field_names]
wycheproof_source = (HERE / "wycheproof_tests_gcm_128.h").read_bytes()
records = re.findall(
    rb"// Wycheproof tcId (\d+):[^\n]*\n\s*GCM_KAT\((.*?)\);",
    wycheproof_source, re.S)
if len(records) != 21 or len(eligible) != 21:
    raise SystemExit("FAIL: expected all 21 valid whole-block AES128 Wycheproof vectors")
seen_ids = set()
for tc_id, quoted in records:
    tc_id = int(tc_id)
    values = [v.decode() for v in re.findall(rb'"([0-9a-fA-F]*)"', quoted)]
    if tc_id in seen_ids or values != eligible.get(tc_id):
        raise SystemExit("FAIL: Wycheproof fields differ at tcId " + str(tc_id))
    seen_ids.add(tc_id)
    print("OK: AES128 Wycheproof tcId %d all six fields verbatim, %d bytes" %
          (tc_id, len(values[3]) // 2))
if seen_ids != set(eligible):
    raise SystemExit("FAIL: valid whole-block AES128 Wycheproof vector set differs")
print("All 21 shared AES128 Wycheproof records match their upstream provenance.")
