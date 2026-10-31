# Two-Sheeted Yang–Mills Framework Progress

Status reviewed: 2026-10-31 against `HEAD` `5ef9727eb427d4043cae6f8d09992816064a871a` and the staged worktree.

This note separates the established operator algebra from the still-unproved
bridge to two-sheeted Yang–Mills structures. The repository was searched by
content across tracked files for the Peirce defect owners, their exact theorem
names, the Yang–Mills curvature owners, and the two-sheet Krein colimit
owners. I then traced the definitions, imports, consumers, and current
worktree state in the relevant Lean sources. Filenames, generated inventories,
and explanatory prose were used only to navigate to those sources.

## Established operator-algebra layer

The reusable polynomial is owned by
`InfoGeometry.Core.IdempotentGraphGrassmannian`: for an element `x` of a
unital associative ring, `idempotencyDefect x := x * x - x`. The Peirce spine
defines the two corner projections, their even and odd parts, the boundary
generators, and the quadratic cycles. The
`InfoGeometry.OperatorAlgebra.PeirceDefectBridge` imports those owners and
proves, for an idempotent `P` and arbitrary `X` in an associative ring,

```text
evenGrade P (idempotencyDefect X)
  - idempotencyDefect (evenGrade P X) = genV P X X
```

It also proves `oddGrade P X * oddGrade P X = genV P X X`, the separate
`qgtPlus` and `qgtMinus` corner identities, and that `genV = 0` exactly when
both corner cycles vanish. If `X * X = X`, then
`idempotencyDefect (evenGrade P X) = -genV P X X`. These are ring identities;
the source explicitly does not identify `genV` with analytic flux, positivity,
or tensor separability.

There is a concrete noncommutative witness in
`PeirceDefectMatrixWitness`: the carrier is the full matrix ring
`Matrix (Fin 2) (Fin 2) ℚ`; the cut is idempotent; the symmetric rank-one
matrix state is self-adjoint and idempotent; and the state does not commute
with the cut. The source proves `genV = (1/4) • 1` and that the pinched
idempotency defect is `-(1/4) • 1`, hence nonzero. It also supplies a
noncommuting mixed-operator counterexample to a proposed commutator replacement
and verifies the corrected ordered anticommutator formula.

`PeirceSpine.TwoStateSandwich` proves further ordered
two-chart products, including `(P - N₊) V (P + N₋) = Q₊ - Q₊²` and
`(P - N₊) Σ (P + N₋) = Q₊ + Q₊²`. The checked-in archetype ledger records why
the alternative submitted signs/formulas fail. `PeirceSpine.DefectTower` is an
existing owner for orthogonal defect iteration, support, and corner projection
statements. The staged change in `Unipotent.lean` adds a natural-number
unipotent idempotent tower, proves each finite stage idempotent, and derives
parent/child relations. The Peirce bridge composes this tower with the
pinching-defect theorem and the two-state conjugation invariant.

## Existing two-sheet and Yang–Mills layers

The repository has a separate categorical two-sheet carrier in
`InfoGeometry.Categorical.TwoSheetKreinFilteredColimit`, with a stage-system
consumer in `TwoSheetKreinStageSystem`. The Peirce decomposition is an
idempotent split inside a ring. The categorical two-sheet object is built from
a filtered-colimit interface. The current import graph does not identify these
two constructions.

Yang–Mills results are also separate. `SelfDualConnectionCurvatureYangMillsBridge`
works with matrices of exterior-algebra-valued forms and derives the
self-dual Yang–Mills equation from self-duality and a Bianchi hypothesis.
`YangMillsFiniteBridge` packages finite gauge/QFT/RG data and a positive
spectral-gap field; its constructors derive the stated package properties
from supplied kernel, orthogonality, positivity, and coercivity hypotheses.
The repo-owned native gauge contract additionally describes a derivation
cochain and curvature-variation chain. These owners do not import
`PeirceDefectBridge` or prove that its `genV` is Yang–Mills curvature, action,
current, or a physical energy.

The tracked import umbrellas do wire the Peirce bridge into
`OperatorAlgebra.All` and the Yang–Mills owners into `Canonical.All`. An
umbrella import is not a theorem-level relationship. The all-tracked-file
identifier search found no consumer connecting the Peirce defect bridge to the
Yang–Mills curvature theorem or to the two-sheet Krein colimit stage system.

## Causal order for the next implementation step

```text
associative-ring idempotency defect
  → idempotent Peirce split and ordered boundary cycles
  → even/odd defect identity and matrix witness
  → explicit carrier map from a Yang–Mills curvature/cochain to the Peirce ring
  → proved compatibility of curvature, covariant differential, and Peirce split
  → trace/adjoint hypotheses for any energy or positivity interpretation
  → explicit compatible maps at each two-sheet Krein stage
  → only then a filtered-colimit or continuum statement
```

The first three steps have source-level owners described above. The remaining
arrows are not established by the imports or declarations inspected here. A
valid bridge must name its carrier map, prove its multiplicative or linear
compatibility, preserve operator order, and state the trace, adjoint, and
positivity assumptions actually used. In particular, a nonzero `genV` proves
failure of Peirce-projectability for the given operator. Calling it quantum
entanglement requires a separately specified tensor factorization and a
separability theorem relative to that factorization.

## Worktree and verification boundary

The staged operator-algebra modules and audits were checked with the locked
build command for `PeirceDefectBridgeAudit`, `TwoStateSandwichAudit`, the
`PeirceSpine` umbrella, `Unipotent`, and `PeirceDefectMatrixWitness`; all
targets passed. The imported closure emitted existing linter warnings in
other files. Axiom reports for the new bridge declarations list `propext`;
the separate complementary pairing also uses `Classical.choice` and
`Quot.sound`. The staged proof-proxy gates and OpenGauss screener passed.
`semantic_vacuity_gate.py` reported two `trivial_surface` warnings in older
Steinberg declarations in `Unipotent.lean`; it reported zero findings in the
new Peirce bridge. These checks establish the reported finite ring identities
and tower results only, not the unproved carrier maps above.

## Source map

- `lean/InfoGeometry/Core/IdempotentGraphGrassmannian.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/DefectParity.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceDefectBridge.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceDefectMatrixWitness.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/TwoStateSandwich.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/DefectTower.lean`
- `lean/InfoGeometry/Categorical/TwoSheetKreinFilteredColimit.lean`
- `lean/InfoGeometry/Categorical/TwoSheetKreinStageSystem.lean`
- `lean/InfoGeometry/Canonical/SelfDualConnectionCurvatureYangMillsBridge.lean`
- `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean`
- `docs/YANG_MILLS_NATIVE_GAUGE_CONTRACT.md`
- `docs/PEIRCE_OPERATOR_ARCHETYPES.md`
