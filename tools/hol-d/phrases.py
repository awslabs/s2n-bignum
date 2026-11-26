"""Recognize a phrase terminator outside HOL quotations, strings and comments."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import re


TOKEN = re.compile(r"""\(\*|\*\)|"(?:\\.|[^"\\])*"?|'(?:\\.|[^'\\\n])'|`|;;|\{([a-z_]*)\||[a-zA-Z_][\w']*|\s+|.""",
                   re.DOTALL)


def split_phrases(source):
    """Return complete top-level phrases and any unfinished suffix."""
    phrases = []
    start = pos = comments = 0
    # Open begin/object/struct/sig blocks. Only module-level struct and sig
    # bodies may contain ";;". Inside begin or object it is a syntax error,
    # so end the phrase there and let OCaml report it instead of waiting.
    blocks = []
    started = False
    while pos < len(source):
        match = TOKEN.match(source, pos)
        token = match[0]
        pos = match.end()
        if match[1] is not None:
            delimiter = "|" + match[1] + "}"
            end = source.find(delimiter, pos)
            if end < 0:
                return phrases, source[start:]
            pos = end + len(delimiter)
            started |= not comments
        elif token == "(*":
            comments += 1
        elif comments:
            if token == "*)":
                comments -= 1
        elif token == "`":
            end = source.find("`", pos)
            if end < 0:
                return phrases, source[start:]
            pos = end + 1
            started = True
        elif token == ";;" and not (blocks and blocks[-1]):
            phrases.append(source[start:pos])
            start = pos
            started = False
            blocks = []
        elif not token.isspace():
            started = True
            if token in ("struct", "sig", "begin", "object"):
                blocks.append(token in ("struct", "sig"))
            elif token == "end" and blocks:
                blocks.pop()
    return phrases, source[start:] if started or comments else ""
