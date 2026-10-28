# Chiral matrix trace and partial-phase localization

Input: `Pasted text(20261028-084629).txt`, 2026-10-28.
SHA-256: `2f5d0cf8b4246c7a0678c656ec9ff47bbbc5e8fb2cf06556316e65eea1755423`.
Base: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
Scope/risk: finite matrix algebra, R2. No diagonalization or ambient matrix
commutativity is assumed. The coefficient ring is commutative for matrix trace.

## Intent and owners

The intake's matrix equations are separated from its spectral-triple and index
interpretations. No new `IsDiracSpectralTriple` or proof-field packet is added.

- `NCG/NonCommutativeFredholmIndex.lean` owns matrix commutators and
  anticommutators. `anticommutator_commutator_of_even` already proves oddness
  of the differential; `commutator_sq_of_anticomm_zero` already proves evenness
  of the square. Its trace/cochain statements remain finite algebraic formulas.
- `Core/PeirceGrading.lean` owns native complementary linear projections,
  `commutator_odd`, `odd_mul_odd`, `mem_even_iff`, and reflection parity.
- `QuantumContext/DrazinSpectralKernel.lean` owns `IsDrazinInverse`,
  `spectralProj`, `kernelProj`, their idempotence, and index-one annihilation.
- Mathlib owns `Matrix.trace`, its cyclic identities and separating pairing,
  `Commute`, `IsIdempotentElem`, `IsSelfAdjoint`, `IsStarProjection`,
  `Matrix.toLin'`, `LinearMap.range`, and `LinearMap.ker`.

Existing related owners inspected include `Core/DiracSuperalgebra`,
`Core/DiracPeirceSuperalgebra`, `Core/PeirceTangent`,
`Core/PeirceMatrixTracePairing`, `OperatorAlgebra/FiniteParitySupertrace`,
`NCG/BlockSupermatrixGradedTrace`, `Canonical/DrazinSupercharge`,
`Canonical/FiniteMatrixGibbsParity`, and `GrandUnification/AnomalyInflow`.
The new statements use an arbitrary full matrix weight rather than the
fixed diagonal parity carrier of `FiniteParitySupertrace`.

## Exact targets and corrections

1. Transport commutators and anticommutators across the trace pairing, and
   prove converses using its nondegeneracy. Anticommutator cancellation needs
   no parity assumption on the test matrix.
2. An idempotent's Peirce pinching is self-adjoint under the trace pairing.
   A weight preserves every pinched trace exactly when it commutes with that
   idempotent. Products of idempotent commutators lie in the existing even range.
3. For C=[F,E], prove [F,C*C]=[[F*F,E],C]. A partial phase does not inherit the
   involution conclusion without controlling its support commutator.
4. A tripotent is its own index-one Drazin inverse. Its square is idempotent;
   if self-adjoint, its square is a native star projection and it satisfies
   F*star(F)*F=F. No identification with sign(D) is inferred for a separate D.
5. Chiral anticommutation plus Drazin commutation makes the regular projector's
   weighted trace zero for additively torsion-free coefficients (used only to cancel two).
   The complementary weighted trace equals trace(γ). For index one, identify
   the complementary projector's actual linear-map range with ker(D).

## Dependency order

These edges are source-level proof dependencies, not a separately formalized
partial order or physical time:

- Cyclic trace -> bracket transport -> cancellation and converses.
- Cyclic trace + existing Peirce projections -> trace adjointness -> pinching criterion.
- Existing commutator oddness + odd-times-odd routing -> quadratic evenness.
- Associative multiplication -> phase commutator defect -> support-commuting case.
- Tripotency -> index-one Drazin witness -> kernel range identification.
- Trace anticommutator cancellation + Drazin commutation + cancellation of 2
  -> regular trace vanishing -> complementary trace localization.

## Unproved interpretation boundary

This change does not establish an unbounded spectral triple, bounded transform,
functional-calculus sign of an arbitrary Dirac operator, heat-kernel theorem,
K-theory class/cocycle normalization, Fredholm index, or Atiyah–Singer theorem.
For general Drazin index k, the complementary range is not asserted to equal
ker(D). The characteristic-two parity converse is not asserted.

## Verification

`[kernel_verified]` All 23 new theorem declarations compile in the focused
[run 40661219270](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40661219270),
job `122724431995`. Verified source commit:
`faa9ed159fd45f24d104fee92827198368e9cb19`; checked PR merge:
`80582292bb9f2e5056835a67fcafdc1fd50b5f5a`.

Command: `bash scripts/quality/check-chiral-trace.sh`. Official Lean 4.34.1,
commit `5045d0056413266e57c625dcd7c365b10e377c52`; Lake
`5.0.0-src+5045d00`; pinned mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The shared lock guards serial
compilation of all eight modules in this import closure using fresh project
oleans and the pinned mathlib cache. Root dependency metadata is unchanged.

The automated axiom gate verifies the exact set of 23 declarations. Every
footprint contains only `propext`, `Classical.choice`, and `Quot.sound`.
There are no placeholders, custom axioms, unsafe declarations, or native-decide
proof shortcuts in the new sources. The staged proof-proxy gate passes and the
semantic-vacuity gate reports zero findings.

Three Lean `unusedSectionVars` warnings remain: `[DecidableEq n]` in
`trace_commutator_transport`, `tripotent_support_isStarProjection`, and
`tripotent_partial_isometry`. These are redundant instance parameters, not
proof holes. No linter has been disabled in the new modules.

| Source under `lean/InfoGeometry/NCG/` | Verified SHA-256 |
| --- | --- |
| `ChiralMatrixTrace.lean` | `474be90122cb0b3342b6ed3df65e0f9fbbef0f2be8ad07c3c64b9d75c0221e56` |
| `PartialPhaseLocalization.lean` | `58d6ae42a5a32a06d473e865bb453aa67dd892cad0c0863c16ee5a6842fbea97` |
| `ChiralTraceAudit.lean` | `174944d1804cc0aa0f96b7a6ec32dcaa12b764a6731c6c8fdb7b7d9c671671a1` |

Independent semantic review: PASS. Independent QA retrieved the successful
job logs, checked all axiom reports, matched the three source hashes, and
accepted the finite, focused scope with the warnings above recorded.

`[accepted_limited_scope]` This verifies the new modules and their import
closure, not a full root Lake build or every repository CI job. The isolated
runner uses the exact pins without loading the root package's unrelated path
dependencies. No local Lean installation was present in the fresh workspace;
GitHub Actions supplied the verification environment.

Repository discovery used direct source search and the context-preflight tool.
The latter found no local generated declaration/InfoTree index in this fresh
checkout. No graph freshness or compiler-extracted causal-poset claim is made.
The existing `Canonical/DrazinCoreFlow` lane separately owns generalized-kernel
results over division-ring modules; the new index-one matrix statement uses
commutative-ring coefficients and the smaller `DrazinSpectralKernel` owner.
