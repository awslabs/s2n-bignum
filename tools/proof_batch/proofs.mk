# Included by arm/Makefile and x86/Makefile after their ordinary targets.
# make -C arm fork-proofs PROOFS="generic/word_min generic/word_max"
# Omit PROOFS to check every proof target and tutorial.
PROOF_JOBS ?= 2
BUILD_JOBS ?= $(PROOF_JOBS)
.PHONY: fork-proofs proof-modules batch-inputs batch-targets proof_timing_targets check-axioms
fork-proofs:
	@python3 ../tools/proof_batch/run.py "$(notdir $(CURDIR))" \
	    --holdir "$(HOLDIR)" --build-jobs "$(BUILD_JOBS)" --jobs "$(PROOF_JOBS)" \
	    $(if $(PROOF_OUTPUT),--output "$(PROOF_OUTPUT)") $(PROOFS)

# Build the architecture, any requested SESSIONS and the selected proof modules.
proof-modules:
	@python3 ../tools/proof_batch/run.py "$(notdir $(CURDIR))" --modules \
	    --holdir "$(HOLDIR)" --build-jobs "$(BUILD_JOBS)" \
	    $(if $(MODULE_DIR),--output "$(MODULE_DIR)") $(foreach s,$(SESSIONS),--session "$(s)") $(PROOFS)

# Conservatively check that no OCaml source redefines check_axioms, which
# every proof footer calls. Only grep's "no matches" exit status passes.
# Logs are not scanned: a failed proof's log may mention check_axioms.
check-axioms:
	@grep -R --include='*.ml' "check_axioms" . ../common/; test $$? -eq 1

# Some proofs also read other routines' objects and tutorial helpers.
BATCH_OBJECTS = $(OBJ) $(WINOBJ) $(UNOPT_OBJ) \
	$(TUTORIAL_OBJ) $(patsubst %.S,%.o,$(wildcard tutorial/*.S))

ifneq ($(filter batch-inputs,$(MAKECMDGOALS)),)
# Rebuild objects after an assembly header change. Stock build rules do not
# track headers, but the batch must never check stale objects.
$(sort $(BATCH_OBJECTS)): $(wildcard ../include/_internal_s2n_bignum*.h)
endif
batch-inputs: check-axioms proofs/subroutine_signatures.ml $(BATCH_OBJECTS)

# ALL_PROOF_LOGS (from the arch Makefile) is what `make proofs` checks and
# what the timing report covers. The batch also checks the tutorials.
proof_timing_targets:
	@printf '%s\n' $(ALL_PROOF_LOGS)
batch-targets:
	@printf '%s\n' $(ALL_PROOF_LOGS) $(TUTORIAL_PROOF_LOGS)
