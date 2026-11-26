"""Compile the shared imports in theories.json and the two proofs."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
import os
from pathlib import Path
import sys

sys.path.insert(0, sys.argv[1])  # The hol-d directory
from holbuild import build_modules

out = Path("modules")
out.mkdir()
plan = build_modules("theories.json", "arithmetic", ["even.ml", "odd.ml"],
                     out, os.environ["HOLDIR"], jobs=2)
plan.write(out / "plan.json")
