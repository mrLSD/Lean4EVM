.PHONY: build test lint bypass drift diff machine-diff prepare-oracles check update

# Build the library.
build:
	@lake build --wfail

# Run the regression tests, including the axiom audit.
test:
	@lake test --wfail

# Run the configured library linters.
lint: build
	@lake lint --wfail

# Forbidden verification bypasses must not appear in any Lean source.
bypass:
	@! grep -rnwE "sorry|admit|native_decide|bv_decide|ofReduceBool|implemented_by" --include="*.lean" Lean4EVM Lean4EVMTest Lean4EVM.lean Lean4EVMTest.lean scripts

# Shared declarations of the nominal byte wrappers must stay identical.
drift:
	@python3 scripts/wrapper_drift.py

# Differential test against the EELS reference semantics.
diff: build
	@python3 scripts/eels_diff.py

# Network/dependency preparation is explicit; the gate itself never skips missing oracles.
prepare-oracles:
	@python3 scripts/prepare_oracles.py

# Real pinned EELS handlers/finalizer and unmodified SwiftEVM interpreter sources.
machine-diff: build
	@python3 scripts/machine_diff.py

# Run all local checks.
check: test lint bypass drift diff machine-diff

# Refresh dependencies and the prebuilt Mathlib cache.
update:
	@lake update
	@lake exe cache get
