# Klein twist and noncommutative block doubling

## Source and theorem contract

Intake: the user's 2026-11-12 mathematical note headed “The Canonical
Mathematical Names & Stream of Pure Mathematical Consciousness”, including the
proposed `BrauerWeylGradedTensorChain` Lean module. This contract records the
mathematical content and corrections; it is not an assertion that the pasted
code had compiled. The source uses
`Σ = [[0,1],[1,0]]`, `Ω = [[0,-1],[1,0]]`,
`Γ = [[1,0],[0,-1]]`, `ι(x) = diag(x,x)`, and `J(x) = diag(x,-x)`.

The implementation extends the existing `SplitAtomDoubling` declarations.
Its `positive` is the source's `Σ`; its `negative` is **minus** the source's
`Ω`. Consequently `positive * negative = -Γ` in the owner convention.
All multiplication below retains the order of arbitrary noncommuting
coefficients. The basic carrier is `Matrix (Fin 2) (Fin 2) A` with `[Ring A]`.

| Source claim | Formal treatment |
| --- | --- |
| Signed generators and chirality | Reuse the existing block operators and prove the chirality compatibility identities. |
| `J(x)J(y) = ι(xy)` | Reuse `twisted_mul`; add mixed multiplication and ordered product transport. |
| Klein twist as tensor untwisting | Distinguish the additive twist from a multiplicative map. Construct `diag(x, σ(x))` as an injective ring homomorphism for any ring endomorphism `σ`, with even and odd specialization. |
| Witt ladder and CAR | Use native matrix units; their algebraic nilpotence and CAR do not need division by two. Existing standard chiral rail operators have the same entries. |
| Clifford pair extension | Prove square and pairwise anticommutator transport for an arbitrary indexed family. This is a relation theorem, not a Clifford algebra classification. |
| Mellin–Walsh inversion | Prove the displayed doubled reconstruction under its exact algebraic scope. Also reconstruct `M` by matrix units without dividing by two. No Mellin transform is defined by this calculation. |
| Recursive chain | Reuse existing tower owners where their carriers agree; distinguish generic ring-valued iteration from the existing real Clifford algebra tower. |

### Existing owners inspected

- `Clifford/SplitAtomDoubling`: `Block2`, `repeated`, `twisted`, `positive`,
  `negative`, `repeatedHom`, `twisted_injective`, `twisted_mul`,
  `head_anticommutator`, and twist anticommutator transport.
- `OperatorAlgebra/ChiralRailPlane`: the standard matrix units, their CAR,
  projector laws, and a noncommutativity witness over any nontrivial ring.
- `Clifford/Cl11Matrix`: the real quadratic form and actual
  `cl11EquivMat` algebra equivalence, using the owner's different basis.
- `Clifford/BottPeriodicity` and `Clifford/Tower`: the actual real graded
  tensor equivalence `clsplit_succ_equiv`.
- `Clifford/Cl11TensorTowerSupergraded`, `Cl11TensorTowerLimit`,
  `Cl11ChiralityGradedCAR`: finite-stage and existing algebraic-colimit
  graded operator constructions. These are distinct from a two-stage identity.
- `Canonical/SplitCliffordMatrixLimitSoldering`: parity-dependent linear
  embeddings and the actual finite-stage involution compatibility.
- `Clifford/Cl55SpinorRepresentationGeneration`:
  `gammaTensorSubalgebra_top` and
  `splitSpinorRepresentation_surjective_of_gammaTensor` establish generation
  and surjectivity for every real finite stage, despite the `Cl55` filename.
- The distinct `src/` lane already has the generic ring-valued `OpMatTower`,
  `towerJWPos`, `towerJWNeg`, and
  `tower_nSite_jordanWigner_clifford_relations` in
  `OperatorAlgebra/PeirceSpine/MetriplecticCausalPlabicKreinYangianPoset`.
  This change does not duplicate that recursive carrier or claim a new check
  of that source-lane module.

The ring-only block section is extracted without renaming declarations into
`Clifford/SplitAtomDoubling/Basic`. The original owner retains its imports,
dimension results, and public declaration names. The extracted statements are
unchanged; unused simplifier arguments were removed from three proofs.

## Necessary mathematical corrections

The displayed signed generators do not generate all of `M₂(ℤ)`: a reduced
word combination has the form

\[
aI+b\Sigma+c\Omega+d\Gamma
=\begin{pmatrix}a+d&b-c\\b+c&a-d\end{pmatrix},
\]

so the two diagonal entries, and separately the two off-diagonal entries,
have equal parity. A universal signed Clifford-to-matrix equivalence over
every ring therefore cannot be inferred from these relations. The null-basis
hyperbolic form and the diagonal form must also be distinguished integrally.

The map `J` is not in general a ring homomorphism: `J(1)=Γ` and its product law has
`ι(xy)` on the right. For an actual grading automorphism `σ`, the map
`x ↦ diag(x,σ(x))` supplies the multiplicative object. The involution
hypothesis is named explicitly whenever a grading property needs it.
An involution alone does not assert an even/odd direct-sum decomposition over
an arbitrary coefficient ring; no such decomposition is assumed here.

The four-term source identity equals `M + M`. In characteristic two this
does not recover `M`. The matrix-unit reconstruction does recover `M` over
every ring. No star operation, Hilbert completion, K-theory periodicity,
or physical interpretation follows merely from these algebraic identities.

## Dependency order

The original block multiplication laws have two independent consumers:

1. `Cl11KleinTwist` proves chirality, the grading-dependent ring embedding,
   matrix-unit CAR, and reconstruction.
2. `Cl11BrauerWeylGenerators` proves arbitrary-family extension, then derives
   the nested four-generator specialization. It imports only the basic owner
   and does not depend on the chirality, graded embedding, or reconstruction
   theorems.

Any tensor-equivalence or colimit claim must cite the separate owner that
constructs its carrier and maps.

## Verification scope

An independent fresh run of the maintained native checker compiled the
complete 12-module repository import closure of all four touched owners,
without reusing repository compilation results. All four touched owners produced
zero compiler warnings. The unchanged imported `SplitQ11` owner produced one
existing deprecation warning.

| Audited owner | Native declarations, including generated declarations |
| --- | ---: |
| `InfoGeometry.Clifford.SplitAtomDoubling.Basic` | 22 |
| `InfoGeometry.Clifford.Cl11KleinTwist` | 47 |
| `InfoGeometry.Clifford.Cl11BrauerWeylGenerators` | 15 |
| `InfoGeometry.Clifford.SplitAtomDoubling` | 4 |
| **Total** | **88** |

The existing declarations moved to `Basic` are not new theorems. Native axiom
inspection rejected unsafe/partial declarations and any axiom outside
`propext`, `Classical.choice`, and `Quot.sound`; those three axioms are the
complete observed footprint.

The independently checked owner-source SHA-256 values are:

| Owner suffix under `lean/InfoGeometry/Clifford/` | SHA-256 |
| --- | --- |
| `SplitAtomDoubling/Basic.lean` | `d50a38e0a2266f3baf1e9a64358d7cf58ba81cb6c78ed239a0298aaefcb2bd1d` |
| `Cl11KleinTwist.lean` | `9becac71df82d0d234bd61ff4132705bb156af7da5229e96b5bbc35e84a97cae` |
| `Cl11BrauerWeylGenerators.lean` | `c084fbcce8641ca7296a7bddb089a86ae4d36e9e2d19db621d177160df9ecc04` |
| `SplitAtomDoubling.lean` | `97f87ef6b5cfcad0c48f05eb58524f6df0c4aa1183d323285a631957bca0bebb` |

Pinned environment: Lean `4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Dependency sources and pins were
not changed. Missing local Mathlib artifacts were compiled from that exact
source under the shared build lock. Graded tensor import preparation required
a higher finite elaboration-heartbeat limit; this did not alter propositions,
proofs, or kernel checks.

Reproducible focused check, from the repository root with the pinned compiler
available and Mathlib's pinned dependencies initialized:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib \
  --target InfoGeometry.Clifford.SplitAtomDoubling.Basic \
  --target InfoGeometry.Clifford.Cl11KleinTwist \
  --target InfoGeometry.Clifford.Cl11BrauerWeylGenerators \
  --target InfoGeometry.Clifford.SplitAtomDoubling \
  --output ../klein-qa
```

The existing Clifford CI workflow now includes these four targets, their
placeholder and strict OpenGauss scans, a four-file semantic scan, and exact
source/evidence-hash reconciliation.

Independent mathematical source review passed. The semantic scan reported
zero errors and seven `trivial_surface` warnings; the reviewer classified
these as genuine support lemmas: three concrete chirality identities, two
conditional specializations of the constructed ring homomorphism, and two
Peirce matrix-unit identifications. None is a vacuous theorem or a substitute
for a missing structural theorem.

The required locked root file and module wrappers were also attempted. Both
returned exit code 1 because the declared local package
`external_refs/homotopy-hypothesis-lean4` is absent. Lake initialized its pinned
LeanCopilot dependency before reaching that blocker; no dependency source or
pin was changed. The focused result is therefore not a root-package or
whole-repository build certificate.
