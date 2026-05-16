---
name: lean4-setup
description: Set up a lean4 repository clone with proper elan toolchains. 
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# Lean 4 Repository Setup

The first time you build in a lean4 repository clone, you need to run
```
cmake --preset release
make -j -C build/release
```

The `cmake` command is not needed on subsequent builds.

## Tests

### Running a Single Test

```bash
cd tests/lean/run
./test_single.sh example_test.lean
```

### Running the Full Test Suite

```bash
make -j -C build/release test ARGS="-j$(nproc)"
```

### Writing Tests

- All new tests should go in `tests/lean/run/`
- These tests don't have expected output files — they run on a success/failure basis
- Use `#guard_msgs` to check for specific messages

## Lean 4 repositories for interactive use

If you are cloning or repairing the leanprover/lean4 repository for a user to work in, you need to do further set up. First, do an initial build according to the instructions above. Then you'll need to pick a toolchain name. If this is the only clone of `lean4` on the machine, just use `lean4`. Otherwise you might use something like `lean4-XYZ`.

Then run the following commands:
```bash
elan toolchain link lean4-XYZ build/release/stage1
elan toolchain link lean4-XYZ-stage0 build/release/stage0
echo lean4-XYZ > lean-toolchain
echo lean4-XYZ > script/lean-toolchain
echo lean4-XYZ > tests/lean-toolchain
echo lean4-XYZ-stage0 > src/lean-toolchain
```

After setting up the toolchains, verify it worked:

```bash
cd tests/lean/run
lean --version  # Should show the commit hash from your clone, not a release version
```

When done with the clone, remove the toolchains:

```bash
elan toolchain uninstall lean4-XYZ
elan toolchain uninstall lean4-XYZ-stage0
```

- The `tests/` directory needs stage1 because tests run against the full Lean system
- The `src/` directory needs stage0 because it's rebuilding the stdlib itself

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.
