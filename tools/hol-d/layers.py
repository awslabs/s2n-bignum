"""Ordered HOL imports that proof processes can share through hol-d sessions."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess


PRELUDE = b"open Hol_lib;;\nopen Hol_loader;;\n"


def read_layers(manifest, root):
    """Return the sessions below the named root in parent-before-child order.

    The manifest maps root names to layers. Each layer names its HOL
    `source` and may map child names to further layers."""
    roots = json.loads(Path(manifest).read_text())
    if root not in roots:
        raise ValueError(f'{manifest}: no root {root!r}; choose from {", ".join(roots)}')
    sources = {}
    units = {}

    def visit(session, layer):
        unit = unit_name(session)
        if unit in units:
            raise ValueError(f'{units[unit]} and {session} both compile to {unit}.cmxs')
        units[unit] = session
        sources[session] = layer['source']
        for name, child in layer.get('children', {}).items():
            # Fail before compiling anything if hol-d fork would reject it.
            if not re.fullmatch(r'[A-Za-z0-9_][A-Za-z0-9_.-]*', name):
                raise ValueError(f'{manifest}: invalid session name {name!r} under {session}')
            visit(f'{session}/{name}', child)

    visit('/' + root, roots[root])
    return sources


def parent_of(session):
    return session.rpartition('/')[0] or '/'


def ancestors(session):
    chain = []
    while session != '/':
        chain.append(session)
        session = parent_of(session)
    return chain[::-1]


def module_stem(path):
    # The HOL parser accepts OCaml module names with an uppercase initial
    # followed by lowercase letters, digits or underscores.
    return re.sub('[.-]', '_', path.lower())


def unit_name(session):
    return 'proof_' + module_stem('_'.join(session.split('/')[2:]) or 'base')


def contextual_block(session, sources, scratch, inline):
    """Expand the last needs in its ancestors' context, including its load record."""
    wrapper = scratch / (unit_name(session) + '_imports.ml')
    chain = ancestors(session)
    # inline_load restores the wrapper's source location after every load. The
    # two wrapper lines delimit the entire last expansion, even for nested or
    # repeated loads. Neither the wrapper's locations nor its digest belong
    # in a shared compilation unit.
    marker = b'(* begin shared import *)\n'
    wrapper.write_bytes(b''.join(f'needs "{sources[p]}";;\n'.encode() for p in chain[:-1])
                        + marker + f'needs "{sources[session]}";;\n'.encode())
    expanded = inline(session, wrapper, wrapper.with_suffix('.flat'))
    location = b' "' + os.fsencode(wrapper) + b'"\n'
    begin = f'#{len(chain)}'.encode() + location + marker
    end = f'#{len(chain) + 1}'.encode() + location
    if expanded.count(begin) != 1 or expanded.count(end) != 1:
        raise ValueError(f'{session}: unexpected HOL inliner boundaries in {wrapper}')
    start = expanded.index(begin) + len(begin)
    return expanded[start:expanded.index(end, start)]


def prefix_end(inlined, start, block, pp):
    """Only share identical bytes when the HOL parser finds no intervening code."""
    if not block:
        return None
    offset = inlined.find(block, start)
    if offset < 0:
        return None
    result = subprocess.run(
        ['ocamlc', '-stop-after', 'parsing', '-dparsetree', '-pp', pp + ' -impl',
         '-impl', '/dev/stdin'], input=inlined[start:offset], stderr=subprocess.PIPE)
    ast = result.stderr.strip().removeprefix(b'* HOL-Light syntax in effect *').strip()
    if result.returncode == 0 and ast == b'[]':
        return offset + len(block)
    return None


def match_prefixes(data, sources, block, pp):
    """Map each eligible session to the byte where its proof remainder starts."""
    ends = {'/': len(PRELUDE)}
    for session, source in sources.items():
        parent = parent_of(session)
        if parent not in ends:
            continue
        # The inliner labels every imported file. Use its label to avoid
        # expanding unrelated theories, then compare the full source bytes.
        if parent != '/' and os.fsencode(source + ' *)\n#1 ') not in data:
            continue
        end = prefix_end(data, ends[parent], block(session), pp)
        if end is not None:
            ends[session] = end
    return ends


@dataclass(frozen=True)
class ProofModule:
    parent: str
    path: Path


@dataclass
class BatchPlan:
    # In initialization order. All plugin paths are relative to the module directory.
    layers: dict[str, Path]
    proofs: dict[str, ProofModule]

    def write(self, path):
        data = {'layers': [{'session': p, 'parent': parent_of(p), 'plugin': str(module)}
                           for p, module in self.layers.items()],
                'proofs': [{'source': name, 'parent': module.parent, 'plugin': str(module.path)}
                           for name, module in self.proofs.items()]}
        path.write_text(json.dumps(data, indent=2) + '\n')
