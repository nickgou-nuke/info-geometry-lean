# Riemann hypothesis half-plane reduction

This focused package compiles the canonical repository owner and its declaration
audit using the root Lean and Mathlib pins. It reuses the existing zeta facts
and does not import the external announced RH proof.

The mathematical result is

\[
\text{all-Dirichlet right-half-plane nonvanishing}
\Longrightarrow
\text{zeta right-half-plane nonvanishing}
\Longleftrightarrow \mathrm{RH}.
\]

The half-plane assertions remain explicit hypotheses. The separate epsilon
lemma is an elementary real inequality. See the
[theorem contract](../../docs/RIEMANN_HALF_PLANE_REDUCTION_CONTRACT.md).

## Reproduce

Run from the repository root with the pinned Lean toolchain on `PATH`:

```bash
python3 verification/riemann-half-plane/audit.py
python3 verification/riemann-half-plane/check.py --wfail build
python3 verification/riemann-half-plane/check.py env lean lean/InfoGeometry/Arithmetic/RiemannHypothesisHalfPlaneReductionAudit.lean > /tmp/riemann-half-plane-axioms.log
python3 verification/riemann-half-plane/audit.py --log /tmp/riemann-half-plane-axioms.log
```

For a new checkout, retrieve the pinned Mathlib artifacts with
`python3 verification/riemann-half-plane/check.py exe cache get` before building.
No dependency update is required. The focused manifest retains the root's exact
nine Mathlib-related Git pins.

`check.py` follows the existing shared-lock wrapper and validates both workspace
roots. `audit.py` reuses `verification/real-matrix-split/audit.py` for source
inventory, proof-construct screening, dependency-pin comparison, and checking
that every public declaration has exactly one axiom report. The only permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The focused build covers the new owner, its existing imported owners, and its
audit module. It does not establish a successful root `InfoGeometry.All` build
or verify the external submitted RH/GRH proof. `validation.json` records the
actual local results and independent review scope. The focused GitHub workflow
regenerates build and axiom evidence for the PR revision.
