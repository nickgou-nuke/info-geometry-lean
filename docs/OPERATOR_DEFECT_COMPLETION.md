# Operator defect completion — proof-script draft

## Status

These files were authored in this conversation. They have NOT been elaborated by
Lean, compiled against the repository, or subjected to a transitive axiom audit.
The submission runtime has no `lean` or `lake` executable. This change is
submitted as a **draft PR**, pending native elaboration and a transitive axiom
audit in the repository's pinned environment. The GitHub connector is used for
publication; no local repository-wide Lean build is claimed.

The scripts contain proof bodies, with no `sorry`, `admit`, `native_decide`, custom
axiom declarations, unsafe declarations, or partial declarations. This direct
source check is not a kernel verification or a transitive dependency audit.

`tools/sympy/operator_defect_completion/validate_algebra.py` was rerun for this
submission and passed 13 exact algebra checks. Its results are recorded in the
adjacent `algebra_checks.json`. It checks free noncommutative polynomial identities with
the explicit relation p*p=p, a formal linear readout identity, and a noncommuting
full 4x4 rational regression with a non-diagonal idempotent. It does not validate
Lean syntax, elaboration, typeclass inference, or the repository adapter.

## Repository paths

This draft adds the three Lean files at:

- lean/InfoGeometry/OperatorAlgebra/OperatorDefectCompletion.lean
- lean/InfoGeometry/OperatorAlgebra/ZornDefectLieClosure.lean
- lean/InfoGeometry/OperatorAlgebra/OperatorDefectCompletionAudit.lean

Use the repository's pinned environment and shared build-lock wrapper. Check
for existing compiler jobs first; never run concurrent builds or clear caches.
From an initialized repository root:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.OperatorAlgebra.OperatorDefectCompletion \
  InfoGeometry.OperatorAlgebra.ZornDefectLieClosure \
  InfoGeometry.OperatorAlgebra.OperatorDefectCompletionAudit
```

These commands are instructions, not a record of commands successfully run here.
The broad repository build may have its own independent setup requirements.

Reproduce the supplementary checks from the repository root:

```sh
python3 tools/sympy/operator_defect_completion/validate_algebra.py
```

The script requires SymPy and writes `algebra_checks.json` beside itself. These
checks are exact algebra evidence, not a replacement for the Lean build. The
adjacent `source_manifest.json` binds the three draft Lean files by SHA-256.
The audit module prints dependencies of nine selected declarations; it is not
an enforcing all-declaration audit or an already-executed verification receipt.

## Main results encoded

1. For an idempotent linear projection P on any associative algebra, define
   D_P(X,Y) = [X,Y] - P([X,Y]). Then P(D_P)=0. If X and Y are retained and
   D_P is nonzero, D_P lies outside range(P) but inside its native Lie closure.
   Consequently range(P) is strictly smaller than that closure's underlying
   submodule. `LieSubalgebra.lieSpan` supplies the least-closure property.
2. The projected Jacobiator is exactly
   -P([X,D_P(Y,Z)] + [Y,D_P(Z,X)] + [Z,D_P(X,Y)]).
   Ambient associative-operator Jacobi never fails.
3. Peirce reconstruction, exact compression-commutator defects, nilpotence of
   each off-diagonal corner, and [p,[p,D]]=pD(1-p)+(1-p)Dp have proof scripts
   over an arbitrary ring. No division by 2 is needed in these statements.
4. Eigenoperator weights add under brackets. A projection commuting with the
   grading derivation preserves that weight in its defect. This is not a claim
   that every anomaly is odd or that a single nonzero vector spans an entire grade.
5. The Zorn adapter uses the existing real native Zorn left-action identity
   [L_X,L_Y] = L_[X,Y] - 2 D(X,Y). It derives membership of D(X,Y) in the native
   Lie span of the left actions. A nonzero D(X,Y) cannot itself be left
   multiplication, because it kills the unit. The existing U0/U1
   nonmultiplicativity witness therefore forces a strict Lie-closure extension.

## Source basis

Inspected repository snapshot:
`nickgou-nuke/info-geometry-lean@b143075bbf27e75860a1011e04423a0f227b7c41`.

Relevant source owners:

- Algebra/ZornLeftCAR.lean
- Algebra/ZornLeftMultiplicationDefect.lean
- Algebra/ChiralOperatorSymbolProjection.lean
- Clifford/ProjectedCliffordAssociatorDefect.lean
- docs/COUNTEREXAMPLE_INVENTORY_STATUS.md (selected initial range)

Mathlib's associative-Lie implementation was inspected at revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. In particular the reducible
`LieRing.ofAssociativeRing` is enabled as a local instance, rather than assumed
to be a global instance.

The uploaded Seligman paper, pages 20–21 (printed pages 305–306), supplies a
related source example: commutators of multiplication operators belong to the
derivation sector, and the larger operator Lie algebra splits into derivations
and multiplication operators. No exceptional-Lie-algebra classification theorem
is implemented by this draft.

## Scope

The generic file concerns arbitrary associative algebras, including full matrix
and endomorphism algebras. The adapter concerns the repository's real alternative
Zorn carrier. It does not assume that operator-valued Zorn multiplication over
arbitrary noncommutative coefficients is alternative.

No nonlinear oscillator existence, stability, continuum limit, or Yang–Mills
spectral-gap conclusion is asserted by algebraic closure alone. Counterexamples
are preserved as witnesses that the correction terms are necessary.

## Proof-prerequisite order

The intended dependency DAG is:

```text
native associative commutator
  -> linear-projection defect -> projected Jacobiator identity
  -> idempotent projection -> kernel/range separation
  -> native Lie span -> strict extension from a nonzero defect
native ring + idempotent
  -> Peirce decomposition -> double-commutator extraction
native grading derivation + compatible projection
  -> bracket-weight addition -> defect-weight preservation
existing real Zorn left actions + associator identity
  -> half-commutator correction -> generated defect membership
  -> unit-annihilation + preserved U0/U1 witness -> strict Zorn Lie closure
```

This records proof prerequisites, not physical causality and not a new Lean
`PartialOrder` construction. Existing counterexamples and existing owner files
are unchanged. No umbrella imports, workflow definitions, package pins, or
build-gate policies are changed by this draft.
