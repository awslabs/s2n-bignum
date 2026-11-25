#!/usr/bin/env python3

# Names for the symbols of an ELF binary that are valid HOL Light and OCaml
# identifiers, shared by elf_layout.py and elf_relocs.py.
#
# A C symbol keeps its name, without leading and trailing underscores
# (memcpy, cxa_finalize, gmon_start), with dots replaced by underscores. A C++ symbol is
# demangled (by c++filt) and its name built from the demangled form:
#
#  - the return type of a function and its parameter list are dropped, as
#    are the namespaces given with --strip-namespace (wherever they occur,
#    also in template arguments), "std::", "__cxx11::", "__gnu_cxx::" and
#    "(anonymous namespace)::"; the remaining parts of the qualified name
#    are joined with "_", without leading underscores, e.g.
#    snappy::ByteArraySource::Peek(unsigned long*) is ByteArraySource_Peek
#    with --strip-namespace snappy;
#  - a constructor is "ctor", a destructor "dtor", and a deleting destructor
#    (D0) "deleting_dtor", e.g. CompressionContext_ctor, Sink_dtor; the
#    base-object versions (C2, D2) are the same functions as the complete
#    ones (C1, D1) when they have the same address, and are otherwise
#    "ctor_base" and "dtor_base";
#  - an operator is "operator_" and a word for it (operator_assign for
#    operator=, operator_new_array for operator new[], ...);
#  - template arguments are appended to the name they belong to, as the
#    names of their types (below), e.g.
#    DecompressAllTags<snappy::SnappyArrayWriter> is
#    SnappyDecompressor_DecompressAllTags_SnappyArrayWriter and
#    DecompressBranchless<char*> is DecompressBranchless_charp;
#  - a local static object of a function f is f_<object>, e.g.
#    LeftShiftOverflows_masks;
#  - the vtable of a class C (the symbol _ZTV...) is ztv_C, and likewise
#    zti_, zts_, ztt_, ztc_ and guard_ for typeinfo, typeinfo names, VTTs,
#    construction vtables and guard variables.
#
# The name of a type is made the same way, without its "const", with "p"
# appended for each "*", "r" for "&" and "rr" for "&&", with "unsigned
# long" as ulong, "unsigned int" as uint, "unsigned char" as uchar,
# "unsigned short" as ushort, "long long" as llong, "signed char" as schar,
# std::basic_string<char, ...> as string, the default arguments
# std::char_traits<...> and std::allocator<...> of a template dropped, and
# a pointer to a function as fnp. E.g. "char const*" is charp and
# "std::__cxx11::basic_string<char, ...>*" is stringp.
#
# If several functions get the same name (overloads), each gets a suffix
# "__" followed by the names of the types of its parameters, joined with
# "_" ("__void" for none), e.g. RawCompress__charp_ulong_charp_ulongp and
# RawCompress__charp_ulong_charp_ulongp_CompressionOptions. A function
# whose name is still the same as another's (e.g. clones such as
# .constprop.0 of the same function) gets the clone suffix, and failing
# that a number in the order of the addresses.

import re, subprocess

CLONE = re.compile(r'((\.(constprop|isra|part|cold|localalias|lto_priv)(\.\d+)?)+)$')

BUILTIN = [('unsigned long long', 'ullong'), ('unsigned long', 'ulong'),
           ('unsigned int', 'uint'), ('unsigned short', 'ushort'),
           ('unsigned char', 'uchar'), ('signed char', 'schar'),
           ('long long', 'llong'), ('long double', 'ldouble'),
           ('short', 'short'), ('long', 'long'), ('int', 'int'), ('char', 'char'),
           ('bool', 'bool'), ('void', 'void'), ('float', 'float'),
           ('double', 'double'), ('wchar_t', 'wchar')]

OPERATORS = [('new[]', 'new_array'), ('delete[]', 'delete_array'),
             ('new', 'new'), ('delete', 'delete'), ('()', 'call'), ('[]', 'index'),
             ('==', 'eq'), ('!=', 'ne'), ('<=', 'le'), ('>=', 'ge'),
             ('<<=', 'shl_assign'), ('>>=', 'shr_assign'),
             ('<<', 'shl'), ('>>', 'shr'), ('<', 'lt'), ('>', 'gt'),
             ('+=', 'add_assign'), ('-=', 'sub_assign'), ('*=', 'mul_assign'),
             ('/=', 'div_assign'), ('%=', 'mod_assign'), ('&=', 'and_assign'),
             ('|=', 'or_assign'), ('^=', 'xor_assign'), ('&&', 'land'),
             ('||', 'lor'), ('++', 'incr'), ('--', 'decr'), ('->*', 'arrow_star'),
             ('->', 'arrow'), ('=', 'assign'), ('+', 'add'), ('-', 'sub'),
             ('*', 'mul'), ('/', 'div'), ('%', 'mod'), ('&', 'and'), ('|', 'or'),
             ('^', 'xor'), ('~', 'not'), ('!', 'lnot'), (',', 'comma')]

# The objects that the compiler makes for a class or an object: the
# vtable symbol _ZTV<class> is ztv_<class>, and so on
SPECIAL = [('vtable for ', 'ztv_'), ('typeinfo name for ', 'zts_'),
           ('typeinfo for ', 'zti_'), ('VTT for ', 'ztt_'),
           ('construction vtable for ', 'ztc_'), ('guard variable for ', 'guard_')]

DEFAULT_ARGS = re.compile(r'^(std::)?(char_traits|allocator|less|hash|equal_to)<')

def demangle_all(names, cxxfilt='c++filt'):
    """The demangled forms of the names (the name itself if it is not
    mangled), in one run of c++filt."""
    names = list(names)
    if not names:
        return {}
    out = subprocess.run([cxxfilt], input='\n'.join(names) + '\n', check=True,
                         capture_output=True, text=True).stdout.split('\n')
    return dict(zip(names, out))

def split_top(s, sep):
    """s split at the occurrences of sep outside <>, () and []."""
    parts = []; depth = 0; cur = ''; i = 0
    while i < len(s):
        c = s[i]
        if s.startswith('operator', i) and depth == 0:
            # operator<, operator() etc.: copy the operator symbol as is
            m = re.match(r'operator\s*(new\[\]|delete\[\]|new|delete|\(\)|\[\]|->\*|->|'
                         r'<<=|>>=|<<|>>|<=|>=|==|!=|&&|\|\||\+\+|--|[-+*/%^&|~!=<>,]=?)',
                         s[i:])
            if m:
                cur += m.group(0); i += len(m.group(0)); continue
        if c in '<([':
            depth += 1
        elif c in '>)]':
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append(cur); cur = ''; i += len(sep); continue
        cur += c; i += 1
    parts.append(cur)
    return parts

def params_split(dem):
    """(head, parameters or None, qualifiers) of a demangled function name;
    the parameter list is the last top-level (...) group."""
    s = dem.strip()
    quals = ''
    m = re.search(r'(\s+(const|volatile|&&|&))+$', s)
    if m and s[:m.start()].endswith(')'):
        quals = m.group(0).strip(); s = s[:m.start()]
    if not s.endswith(')'):
        return s, None, quals
    depth = 0
    for i in range(len(s) - 1, -1, -1):
        if s[i] == ')':
            depth += 1
        elif s[i] == '(':
            depth -= 1
            if depth == 0:
                head = s[:i]
                if head.endswith('operator'):      # operator()(...)
                    continue
                return head, s[i + 1:-1], quals
    return s, None, quals

class Namer:
    def __init__(self, strip_namespaces=()):
        ns = sorted(strip_namespaces, key=len, reverse=True)
        self.strip = [n.rstrip(':') + '::' for n in ns] + \
            ['std::', '__cxx11::', '__gnu_cxx::', '(anonymous namespace)::']

    def unqualify(self, s):
        for n in self.strip:
            s = s.replace(n, '')
        return s

    def type_name(self, t):
        """The name of a type, as in the header."""
        t = self.unqualify(t.strip())
        if re.search(r'\(\*\)', t):
            return 'fnp'
        if t == '...':
            return 'varargs'
        suffix = ''
        while True:
            t = t.strip()
            if t.endswith('&&'):
                suffix = 'rr' + suffix; t = t[:-2]
            elif t.endswith('&'):
                suffix = 'r' + suffix; t = t[:-1]
            elif t.endswith('*'):
                suffix = 'p' + suffix; t = t[:-1]
            elif t.endswith(' const') or t.endswith(' volatile'):
                t = t.rsplit(' ', 1)[0]
            elif t.startswith('const ') or t.startswith('volatile '):
                t = t.split(' ', 1)[1]
            else:
                break
        return self.base_name(t) + suffix

    def base_name(self, t):
        t = t.strip()
        for c, n in BUILTIN:
            if t == c:
                return n
        if t.startswith('basic_string<char'):
            return 'string'
        m = re.match(r'^([^<]*)<(.*)>$', t)
        if m:
            args = [a for a in split_top(m.group(2), ', ')
                    if not DEFAULT_ARGS.match(a.strip())]
            return '_'.join([self.ident(m.group(1))] +
                            [self.type_name(a) for a in args])
        if re.match(r'^-?\d+[a-z]*$', t):           # a value argument
            return t.replace('-', 'm')
        return self.ident(t)

    def ident(self, s):
        s = re.sub(r'[^A-Za-z0-9_]+', '_', s).strip('_')
        return s

    def part_name(self, part, prev, mangled):
        part = part.strip()
        m = re.match(r'^operator\s*(.*)$', part)
        if m:
            op = m.group(1).strip()
            for sym, n in OPERATORS:
                if op == sym:
                    return 'operator_' + n
            return 'operator_' + self.type_name(op)  # a conversion
        if part.startswith('basic_string<char'):
            return 'string'
        targs = []
        m = re.match(r'^([^<]*)<(.*)>$', part)
        if m:
            part = m.group(1)
            targs = [a for a in split_top(m.group(2), ', ')
                     if not DEFAULT_ARGS.match(a.strip())]
        if part.startswith('~'):
            core = 'deleting_dtor' if re.search(r'D0Ev$', mangled) else \
                   'dtor_base' if re.search(r'D2Ev$', mangled) else 'dtor'
        elif prev is not None and part == re.sub(r'<.*', '', prev):
            core = 'ctor_base' if re.search(r'C2E', mangled) else 'ctor'
        else:
            core = self.ident(part)
        return '_'.join([core] + [self.type_name(a) for a in targs])

    def name(self, dem, mangled):
        """(name, parameter names or None) of a demangled symbol."""
        for special, pfx in SPECIAL:
            if dem.startswith(special):
                return pfx + self.name(dem[len(special):], '')[0], None
        head, params, _ = params_split(dem)
        local = None
        # A local static object f(...)::obj: the function, then obj
        m = re.match(r'^(.*\))(::.*)$', head) if params is None else None
        if m:
            fh, fp, _ = params_split(m.group(1)); head = fh; local = m.group(2)[2:]
        if params is not None or local is not None:
            pieces = split_top(head.strip(), ' ')
            head = pieces[-1] if pieces else head
            # "operator new" was kept together by split_top
        head = self.unqualify(head)
        parts = [p for p in split_top(head, '::') if p]
        names = []
        for i, p in enumerate(parts):
            names.append(self.part_name(p, parts[i - 1] if i > 0 else None, mangled))
        if local:
            names.append(self.ident(self.unqualify(local)))
        n = '_'.join(x for x in names if x)
        ps = None
        if params is not None:
            ps = [self.type_name(p) for p in split_top(params, ', ') if p.strip()]
            if ps == ['void']:
                ps = []
        return n, ps

def is_mangled(sym):
    return sym.startswith('_Z')

def c_name(sym):
    return re.sub(r'[^A-Za-z0-9_]', '_', sym.strip('_'))

def hol_names(syms, strip_namespaces=(), c_prefix='', cxxfilt='c++filt',
              same=None):
    """Names for the symbols syms, a list of (address, symbol), as a dict
    from (address, symbol) to name. Symbols at the same address that get
    the same name are the same function. same(a, b) can say whether two
    addresses are the same function (default: equal addresses)."""
    namer = Namer(strip_namespaces)
    bases = {s: CLONE.sub('', s) for _, s in syms}
    dem = demangle_all(sorted(set(b for b in bases.values() if is_mangled(b))), cxxfilt)
    raw = {}
    for a, s in syms:
        b = bases[s]
        if is_mangled(b) and dem.get(b, b) != b:
            n, ps = namer.name(dem[b], b)
        else:
            n, ps = c_prefix + c_name(b), None
        raw[a, s] = (n, ps)
    # Base-object constructors and destructors at the address of the
    # complete ones are those functions
    for (a, s), (n, ps) in list(raw.items()):
        for k in ('ctor_base', 'dtor_base'):
            if n.endswith(k) or ('_' + k + '_') in n:
                alt = n.replace(k, k[:-5])
                if any(a2 == a and n2 == alt for (a2, _), (n2, _) in raw.items()):
                    raw[a, s] = (alt, ps)
    out = {}
    groups = {}
    for (a, s), (n, ps) in raw.items():
        groups.setdefault(n, []).append((a, s))
    for n, members in groups.items():
        addrs = sorted(set(a for a, _ in members))
        if len(addrs) == 1:
            for k in members:
                out[k] = n
            continue
        # Overloads: the types of the parameters
        cand = {}
        for a, s in members:
            ps = raw[a, s][1]
            cand[a, s] = n + '__' + ('_'.join(ps) if ps else 'void') if ps is not None else n
        by = {}
        for k, v in cand.items():
            by.setdefault(v, set()).add(k[0])
        for (a, s), v in cand.items():
            if len(by[v]) > 1:
                m = CLONE.search(s)
                if m:
                    v = v + '_' + c_name(m.group(1))
            out[a, s] = v
        by = {}
        for k, v in out.items():
            if k in members:
                by.setdefault(v, set()).add(k[0])
        for v, aset in by.items():
            if len(aset) > 1:
                for i, a in enumerate(sorted(aset), 1):
                    for k in members:
                        if k[0] == a and out[k] == v:
                            out[k] = '%s_%d' % (v, i)
    for k, v in out.items():
        if not re.match(r'^[A-Za-z][A-Za-z0-9_]*$', v):
            raise ValueError('elf_names: no valid name for %s: %s' % (k[1], v))
    return out
