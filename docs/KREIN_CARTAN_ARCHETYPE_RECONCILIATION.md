# Krein–Cartan archetype reconciliation

Status: source audit in progress; no new kernel or master-build certification.
Starting revision: `20f780b1f`.

## Preserved mathematical intent

The supplied narrative seeks a compatible progression from an indefinite
pairing, through involution-graded operators and nilpotent directions, to
geometric coordinates and pre/post-selected observable ratios. This document
preserves that explicit mathematical intent before any proposed contraction of
duplicate declarations. It does not purport to recover private reasoning.

The progression must consist of maps and compatibility theorems between named
carriers. Similar equations on unrelated carriers do not constitute such maps.

## Existing owners and native abstractions

| Intended construction | Existing owner | Mathematical interface |
|---|---|---|
| Real indefinite pairing and adjoint | `lean/InfoGeometry/Krein/KreinSpace.lean` | Real Hilbert carrier with involutive fundamental symmetry; continuous Hilbert adjoint conjugated by that symmetry |
| Conjugation grading | `lean/InfoGeometry/Krein/CartanDecomposition.lean` | Conjugation of continuous endomorphisms, preserving the native associative Lie bracket |
| Abstract graded bracket | `lean/InfoGeometry/Architecture/CartanLieBracket.lean` | Submodule-based bracket compatibility |
| Native real Clifford matrix equivalence | `lean/InfoGeometry/Clifford/Cl11Matrix.lean` | `CliffordAlgebra`, `QuadraticForm`, `CliffordAlgebra.lift`, and `cl11EquivMat` |
| Doubled-space Clifford representation | `lean/InfoGeometry/Krein/Representation.lean` | `cl11Rep` into continuous real endomorphisms |
| Ring-level opposite-square interference | `lean/InfoGeometry/OperatorAlgebra/CliffordNilpotentInterference.lean` | Square-zero sum and difference of anticommuting generators |
| Existing KAN generator vocabulary | `lean/InfoGeometry/OperatorAlgebra/IwasawaKANTransform.lean` | `IwasawaKANClifford`, `N_plus`, `N_minus`, and parameterized flows |
| Concrete CAR cell | `lean/InfoGeometry/OperatorAlgebra/ChiralRailPlane.lean` | `E_R_standard`, `E_L_standard`, `Γ_standard`, `Ω_standard` |
| Clifford CAR construction | `lean/InfoGeometry/Algebra/Cl11Fermions.lean` | Native rational Clifford algebra and normalized `b`, `bdag` |
| Cuntz chiral composites | `lean/InfoGeometry/Algebra/CuntzChiralSuperchargeRepresentation.lean` | `QPlus`, `QMinus`; composites of Cuntz generators |
| Cuntz source/range and adjoints | `lean/InfoGeometry/Canonical/CuntzChiralPartialIsometries.lean` | Chiral partial-isometry identities |
| Horocycle matrix and pairing | `lean/InfoGeometry/Canonical/IwasawaMaurerCartanBdGBridge.lean` | `mat_dN`, `etaKrein`, `kreinDiracPairing` |
| Plücker quadratic relation | `lean/InfoGeometry/Projective/Quadrics/PluckerKlein.lean` | Six coordinates obtained from an explicit two-vector frame |
| Matrix split-quadratic readout | `lean/InfoGeometry/Canonical/PeirceNullConeKinematicEmbedding.lean` | `channelCoordinates`, `channelQuadratic`, split-octonion transport |
| Exterior incidence geometry | `lean/InfoGeometry/Projective/ExteriorKleinCoordinateIncidence.lean` | `linePlucker` and coordinate/exterior incidence compatibility |
| Real weak-value threshold | `lean/InfoGeometry/Canonical/AAVWeakMeasurementKleinSeamBridge.lean` | `weak_amplification_bound` with explicit positivity conditions |

These are source-discovered interfaces, not newly verified build results.
The mathematical field, signature, basis, and multiplication convention must
be aligned before using an equivalence between different rows.

## Corrections to the supplied narrative

1. `η A η` is involutive conjugation. The Krein adjoint uses `η A† η`.
   The former preserves multiplication order; the latter reverses it.
2. A pseudo-unitarity equation does not identify the entire pseudo-unitary
   group with a spin group. The existing Dirac theorem takes the adjoint–inverse
   equation as a premise; it constructs no group equivalence.
3. Bracket parity yields even/odd projection identities. Differential Cartan
   equations additionally require the connection, differential, and products
   of forms on a common carrier.
4. A nilpotent Cuntz composite is distinct from a Cuntz isometry generator.
   An arbitrary matrix satisfying the same nilpotency relation is not thereby
   a faithful representation of the Cuntz algebra.
5. The determinant-zero locus of a two-by-two matrix and the six-coordinate
   Plücker Klein relation require an explicit geometric correspondence.
6. Transpose defines a bilinear adjoint over a general commutative ring.
   A complex Hermitian interpretation requires conjugate transpose.
7. The initial any-field identity `(num / eps) * eps = 2 + eps` contains no
   limit assertion. In characteristic two its quotient is one for nonzero
   `eps`. Likewise the constant `-4` is not uniformly nonzero.
8. The defined locus `t = 0 ∧ x = 0` is contained in `t = -t`; these predicates
   are not equal. Their names do not construct Tomita–Takesaki modular data or
   a Klein-bottle quotient.
9. Substituting a weak ratio into an independently defined BdG mass parameter
   establishes a property of that chosen model. It does not derive a physical
   condensation mechanism.

## Boundary-preserving implementation plan

Reuse the existing Clifford and CAR objects. Construct and verify explicit
generator images, adjoint compatibility, and coordinate maps. State real
weak-value estimates in the existing pairing and quotient vocabulary. Keep
model identifications visible and prove substantive consequences rather than
adding certificate packets or forwarding theorem collections.

Before replacing any API, search all qualified and unqualified dependents,
record where its content survives, and check affected imports. Preserve the
categorical owners for any later passage across stages.

## Concurrent work and verification constraints

During this audit another writer replaced and staged
`IwasawaCuntzKleinWeakBridge.lean`. Its initial duplicate API findings must be
distinguished from the subsequent candidate. This audit has not overwritten
that candidate.

`manage_task list` is unavailable in this session. Approval for process
inspection plus the shared build lock has been requested before compilation.
Browser-harness requires local Chrome remote debugging before literature
verification can proceed. No claim of exhaustive literature review is made.
