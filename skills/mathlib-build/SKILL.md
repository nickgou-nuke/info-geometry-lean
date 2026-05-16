---
name: mathlib-build
description: Building Mathlib
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# Building Mathlib

Fetch the Mathlib olean cache before build:

```bash
lake exe cache get
```

Use `lake exe cache get!` (with `!`) to force re-download if the cache appears corrupt.

When building Mathlib reduce verbosity to save on tokens:

```bash
lake build -q --log-level=info
```

For merge conflict resolution or small fixes build only the affected files: `lake build Mathlib.Foo.Bar -q --log-level=info`.
Often it is fine to leave a complete build to CI. If you need a thorough local build, use `lake build Mathlib MathlibTest Archive Counterexamples && lake exe runLinter`.


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
