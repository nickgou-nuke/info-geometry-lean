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

