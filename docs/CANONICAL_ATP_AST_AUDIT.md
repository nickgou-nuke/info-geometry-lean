# Canonical ATP / AST Audit

Audit date: 2026-06-06.

Local references:

```text
external_refs/Canonical
external_refs/CanonicalLean
```

Upstream context:

```text
https://chasenorman.com/
https://github.com/chasenorman/Canonical
https://github.com/chasenorman/CanonicalLean
```

## Finding

Canonical is primarily an ATP system for dependent type theory, exposed to Lean
through `CanonicalLean` as the `canonical` tactic. It is not a general Lean
style/compliance linter.

It does, however, contain useful AST-adjacent and code-generation infrastructure:

- `CanonicalLean/Canonical/Tactic.lean` defines the `canonical` tactic syntax,
  parses user premises, reads the current Lean goal, and connects the tactic to
  the Canonical search engine.
- `CanonicalLean/Canonical/ToCanonical/Translate.lean` converts elaborated Lean
  `Expr` terms, goals, constants, local hypotheses, and reduction rules into
  Canonical's `Typ` / `Term` / `Spine` IR.
- `CanonicalLean/Canonical/FromCanonical.lean` reconstructs Lean `Expr` terms
  from Canonical terms and attaches metadata used to delaborate generated
  `simp` / `simpa` proof fragments.
- `CanonicalLean/Canonical/Main.lean` runs the external prover, postprocesses
  returned terms, and emits Lean `TryThis` exact-suggestion code.
- `CanonicalLean/Canonical/Refine.lean` provides an RPC/widget path that turns a
  refinement selected in the UI into a formatted `refine ...` tactic string via
  Lean delaboration.
- `Canonical/crates/canonical-compat/src/ir.rs` and
  `Canonical/crates/canonical-compat/src/refine.rs` define the Rust-side IR,
  HTML/refinement interface, assignment operations, and interactive search
  state.

## Implication For This Repo

Canonical can inform three practical lanes:

1. Proof search: try `canonical` on small leaf obligations after native
   mathlib search and before admitting any closure debt.
2. AST/proof-suggestion tooling: reuse its pattern of `Expr -> IR -> Expr ->
   TryThis` for localized proof synthesis experiments.
3. Compliance wrappers: build separate repo-native checks around generated
   suggestions if we use them. The compliance layer must still reject `sorry`,
   `admit`, unowned wrappers, hidden axioms, and theorem-surface drift through
   our normal Lean gates.

Canonical itself should stay in `external_refs/` as source evidence and tool
reference. Do not vendor its tactic or generated proof fragments into owner
files without a kernel-checked local build and ordinary review.
