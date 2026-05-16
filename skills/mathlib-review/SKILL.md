---
name: mathlib-review
description: Review guidelines for Mathlib PRs. Use when reviewing pull requests, checking code quality, or assessing whether a PR is ready to merge.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# Mathlib PR Review

## Attributes and API

- New definitions should come with associated lemmas and appropriate attributes (`@[simp]`, `@[ext]`, etc.).
- Watch for instance diamonds.
- Prefer bundled morphisms, `FunLike` API for morphism classes, `SetLike` API for subobject classes.

## Style Points Specific to Mathlib

- **Simp squeezing:** Terminal `simp` calls should NOT be squeezed (replaced with `simp only [...]`) unless there's a measured performance problem. Unsqueezed `simp` is more maintainable and doesn't break when lemmas are renamed.
- **Normal forms:** Prefer `s.Nonempty` over alternatives. Use `hne : x ≠ ⊥` in hypotheses (easier to check), `hlt : ⊥ < x` in conclusions (more powerful).
- **Transparency:** Needing `erw`, or `rfl` after `simp`/`rw` usually means the API is missing lemmas.
- **File size:** Consider splitting files that exceed ~1000 lines or cover multiple topics.

## Reference Guides

The full review guide and style references:

- **Review guide:** https://leanprover-community.github.io/contribute/pr-review.html
- **Naming conventions:** https://leanprover-community.github.io/contribute/naming.html
- **Code style:** https://leanprover-community.github.io/contribute/style.html
- **Documentation style:** https://leanprover-community.github.io/contribute/doc.html

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
