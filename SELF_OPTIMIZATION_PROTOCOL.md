# Self-Optimization Protocol

> Status: `current authority`
> Audited: 2026-05-28
> Note: Maintained against the UTMOST MANDATE for native Lean proof closure.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md), [PAULI_MANDATE.md](PAULI_MANDATE.md)

This repository allows guarded self-improvement of its code and tooling. It
prohibits graph-driven free play or semantic cheating via vacuous scaffolding.

## UTMOST MANDATE: Native Lean Proof Closure

Effective immediately, all self-optimization must prioritize replacing
witness-gated and external-certificate leftovers with native Lean proofs.

### Prohibited Patterns
- **No Vacuous Laws**: Never create `_law : Prop` fields with `_certificate : law`
  placeholders. This is semantic cheating and obscures actual mathematical
  closure.
- **No Closure by Projection**: Do not call a theorem proved when it merely
  projects a witness, certificate, assumption field, packet field, or arbitrary
  `Prop` carried by a structure.
- **No Placeholder Sockets**: Do not promote anonymous or unformalized sockets
  as complete. Gaps must be recorded as explicit `sorry` debt or named open
  closure debt.
- **No Axiom Laundering**: Do not introduce custom `axiom`s, opaque constants,
  fake instances, `Nonempty` padding, or `True`-shaped predicates to make a
  false or missing theorem compile.
- **No Textual Resolution**: Debt cannot be resolved with wording; progress
  must be structural and kernel-checked.

## Allowed Loop

1. **Inspect**: Analyze the current code for `sorry`, `admit`, `axiom`, witness,
   certificate, `law : Prop`, `Prop := True`, `: True`, and projection-only debt.
2. **Classify**: Separate targets into `proved math`, `open debt`,
   `false/wrong-target`, and `wrapper/vacuous`. Do not patch false targets into
   weaker claims just to make a build pass.
3. **Refactor**: Replace opaque `Prop` laws with concrete mathematical identities,
   explicit definitions, or owner-rooted theorem statements; do not introduce
   axioms to hide missing proofs.
4. **Prove**: Discharge promoted propositions through native Lean derivations in
   the correct owner corridor, rooted in current repo definitions and Mathlib.
5. **Verify**: Build the changed module and the narrowest downstream target.
6. **Audit**: Rerun managed repo checks (`changedVerify`, `dagStatus`) when the
   change widens in scope; report any stale downstream projections honestly.
7. **Finalize**: Keep the change only if it replaces a wrapper with a
   theorem-backed derivation, or if it explicitly demotes fake closure to open
   debt.

## Guardrails

- **Kernel Authority**: Only Lean proof terms checked by the kernel decide truth.
- **Truth-First Design**: Structures must carry explicit mathematical meaning
  (e.g., `det P = norm`) or be labelled as open design debt.
- **Owner-Lane Discipline**: Prove real facts in the existing owner module before
  adding bridge/readout/reexport surfaces.
- **No Axiomatic Leakage**: Audit results with `#print axioms`; custom axioms or
  project-local theorem constants are blockers unless the task explicitly asks
  for an axiom socket.
- **Build Is Necessary, Not Sufficient**: A green build with unresolved `sorry`,
  wrapper projections, or vacuous fields is not mathematical closure.
- **Preserve Integrity**: Do not perform broad cleanups that strip existing
  user-proven lemmas.

## Verification Surface

Use:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
python3 tools/refresh_blueprint_tags.py
```

Use `lake script run dagAll` only when you actually need a full structural
refresh.
