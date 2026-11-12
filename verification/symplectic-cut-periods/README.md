# Real symplectic cut period validation

This isolated Lake package builds the five mathematical owners imported by
`InfoGeometry.Geometry.SymplecticCutPeriodAll` and their declaration audit.
Source files remain in the canonical `lean/` tree. The nine Git dependency
revisions used here match their entries in the root package, and the Lean
toolchain matches exactly; `audit.py` checks these relationships. Unrelated
root dependencies are outside this focused package.

The intended scope and source provenance are recorded in
[`SYMPLECTIC_CUT_PERIOD_CONTRACT.md`](../../docs/SYMPLECTIC_CUT_PERIOD_CONTRACT.md).
The focus is real Hamiltonian operators and exact real analytic period
identities. This package does not certify full symplectic reduction or the
paper's Gromov–Witten interpretation.

## Reproduction

Run from the repository root, with the pinned toolchain available:

```bash
python3 verification/symplectic-cut-periods/audit.py
python3 verification/symplectic-cut-periods/check.py build
python3 verification/symplectic-cut-periods/check.py env lean lean/InfoGeometry/Geometry/SymplecticCutPeriodAudit.lean > symplectic-cut-axioms.log
python3 verification/symplectic-cut-periods/audit.py --log symplectic-cut-axioms.log
```

`check.py` uses the repository-wide compiler lock and checks workspace
integrity. It does not delete caches, change dependency pins, or bypass a
busy compiler. CI restores pinned Mathlib artifacts and preserves build and
axiom logs even on failure. Its source cache is keyed by the checked sources.

The audit inventory includes every explicitly declared public definition and
theorem in the five owners. Private helper dependencies are inspected
transitively. The validator requires a fresh Lean axiom report containing
exactly the expected names, and rejects axioms beyond `propext`,
`Classical.choice`, and `Quot.sound`. Its source scan rejects proof holes and
unsafe bypasses. These checks complement, rather than replace, semantic review.

## Acceptance status

A source checkpoint alone is not an acceptance certificate. The PR's final
validation record identifies the checked commit, CI result, independent A-A
and QA-A dispositions, and any remaining limitations or unrelated baseline
failures. The existence of this package does not assert a successful build.
