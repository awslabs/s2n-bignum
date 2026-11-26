# Build with the OCaml switch used for HOLDIR, as for make fork-proofs.
HOLDIR ?= $(HOME)/hol-light
# override: a relative HOLDIR=... on the command line must still become
# absolute, since the recipes run inside build/.
override HOLDIR := $(abspath $(HOLDIR))
HOST = build/node.native
SRC := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
PACKAGES = zarith,unix,dynlink,compiler-libs.native-toplevel

.PHONY: all FORCE
all: $(HOST)

# Record HOLDIR, read by daemon.py, and the toolchain. Rebuild when either
# changes, since mixed toolchains surface later as Dynlink errors.
build/holdir: FORCE
	@mkdir -p build
	@printf '%s\n' "$(HOLDIR)" | cmp -s - $@ || printf '%s\n' "$(HOLDIR)" > $@
build/toolchain: FORCE
	@mkdir -p build
	@printf '%s\n' "$(shell command -v ocamlfind ocamlopt; ocamlfind ocamlopt -version)" | \
	    cmp -s - $@ || printf '%s\n' "$(shell command -v ocamlfind ocamlopt; ocamlfind ocamlopt -version)" > $@

$(HOST): $(SRC)node.ml build/holdir build/toolchain $(HOLDIR)/hol_lib.cmxa
	cd build && ocamlfind ocamlopt -package $(PACKAGES) -I "$(HOLDIR)" -c "$(SRC)node.ml" -o node.cmx
	cd build && ocamlfind ocamlopt -linkall -package $(PACKAGES) -linkpkg \
	    -I "$(HOLDIR)" "$(HOLDIR)/hol_lib.cmxa" node.cmx -o node.tmp
	mv build/node.tmp $(HOST)
