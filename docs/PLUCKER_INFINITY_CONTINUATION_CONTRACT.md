# Operator, grading, and analytic colimit continuation

This contract records the implementation authorized after the source audit of
PR #228. The continuation starts from published head
`d6d7a86cf5cadef212082e879605390f0fafaea8`. The earlier
`PLUCKER_INFINITY_MODULAR_CONTRACT.md` remains the convention owner.

## Mathematical carriers and source-confirmed gaps

1. **Signed reflection.** On native twistors use
   `R (omega, pi) = (-i pi, i omega)`. On Plücker coordinates this is
   `S(P) = (-p23,-p02,-p12,-p03,-p13,-p01)`, and on the existing real six-slice
   `r(a0,ax,ay,az,b0,bz) = (a0,-ax,-ay,-az,-b0,bz)`.
   Prove these commute with `twistorPairPlucker`, `lorentzPlucker`, and the
   actual `PluckerCl55InfinityBridge` embedding. Reuse the existing
   `globalSheetReflectionAlg` and `globalSheetRealSplitPin`; do not identify
   this signed reflection with the plain block swap. In the graph chart the
   coordinate action is `-X⁻¹`, with projective scale `-det X`.

2. **Calibrated CAR representation and five lanes.** The native carrier is
   `Cl55 = CliffordAlgebra Q55`. The matrix instance is the existing
   `MatStage 5`, with its actual creation/annihilation matrices. Lift
   `Gamma(p,q) = sum_i ((p_i-q_i)c_i + (p_i+q_i)a_i)` through the Clifford
   universal property after proving `Gamma(v)^2 = Q55(v) • 1`.
   Calibrate the named native generators, including the additive `5/2`
   difference between native total number and the centered matrix grader.
   `Cl55WittFullLieClosure` already proves the five-lane sum is exactly the
   matrix Lie span of the ten degree-one generators. Its lane ranks are
   `10,5,25,5,10`. Complete independence/internal decomposition and dimension
   using distinct eigenspaces, then transport through the calibrated map.
   The entire Clifford algebra is not five-graded by this number operator:
   `Cl55CreationWordGradeObstruction` already gives a nonzero degree-five word.

3. **Literal exterior contraction.** The generic owner
   `ExteriorContractionOperatorBridge.contractionOp` at the audited base is
   identically zero. Replace its implementation by Mathlib
   `CliffordAlgebra.contractLeft (Q := 0)`, which has the same exterior carrier
   and supports every commutative base ring. Preserve its public type and
   prove nilpotency, anticommutation, vacuum action, one-particle evaluation,
   and the mixed CAR recurrence from the actual operator. Repair consumers
   that unfolded the old zero definition. In `FockNumberOperatorBridge`, add
   the evaluated single-particle action and normalized eigenvalue/idempotence
   laws. These are operator facts, not declarations supplied as assumptions.

4. **Spinor and projective incidence.** Reuse `spinorOuter`, the native Pauli
   determinant, and `PenroseIncidence.incidencePlane`. Prove the determinant
   of a sum of rank-one spinors, little-group rescaling and uniqueness for
   a nonzero matrix. Derive the actual spinor BCFW shift from these identities.
   Specify Witten/native block, transpose, and `i` conventions explicitly.
   Projective-line membership means a common two-plane; the existing
   rank-one `PairwiseCollinear` predicate cannot serve as that condition.
   A Parke--Taylor rational expression can have proved domain, scaling, and
   cyclic laws without thereby being identified with a scattering amplitude.

5. **Four-mode exterior helicity.** Use actual exterior creation/contraction
   and the established spinor representation. The native convention makes
   `creation55` act by contraction and `annihilation55` by wedge. Consequently
   the four-mode exterior Euler operator is the sum of wedge-after-contraction
   terms, with an explicit selected-mode map. Prove its degree/helicity
   action. Keep the exterior ranks `1,4,6,4,1` separate from the five Lie-lane
   ranks. No Fourier equivalence on plain polynomials is assumed.

6. **Analytic KMS correlations on the actual completed state.** Compose
   `FiniteSeedRepresentedRealTime`, `FiniteSeedRepresentedKMS`,
   `ComplexTimeConjugation`, and `FiniteMappedGibbsDensityExponential`.
   For `F(z) = omega(A * alpha_z(B))`, prove entire analyticity, continuity
   on the closed strip, a uniform strip bound, and
   `F(t+i beta) = omega(alpha_t(B) * A)` from the existing Gibbs twist.
   The state is the represented vacuum state of the compatible finite-seed
   Gibbs family on the actual filtered GNS completion. The KMS boundary law
   is a correlation identity, not operator imaginary-time periodicity.

7. **Bilingual analyticity and the inductive boundary.** Reuse
   `Geometry.BilingualAnalyticity` and `FilteredInductiveHestenesAnalyticity`.
   Generalize complex-to-real phase differentiation where the target is an
   operator space, and instantiate the filtered phase cone with the native
   GNS stage embeddings and Hilbert colimit maps. Prove phase compatibility
   and Cauchy--Riemann compatibility of those actual maps. Any Hestenes form
   must be obtained from the stated calibration of the same function;
   an unrelated closed form is not evidence of its analyticity. A supplied
   Stokes backend or closability hypothesis must remain visible until a
   concrete native instance is proved.

8. **Concrete stage Tomita closability.** Discharge the existing closability
   condition for the actual matrix-trace family and the actual finite-seed
   Gibbs family. For the trace, use invariance of the pre-GNS norm under star.
   For Gibbs states, derive faithfulness from the positive invertible density,
   separate the pre-GNS seminorm, and use finite dimensionality of each stage.
   Transport faithfulness below the seed through the injective bonding maps.
   Instantiate the existing categorical real Tomita operator and its modular
   form completion. These are stage closability results: a uniform bound in
   the infinite tower, a global polar decomposition, and a state-derived
   modular logarithm require further theorems and are not asserted here.

9. **Chiral analytic correlations and affine reflection.** Use the proved
   Hermitian image of the native chiral charge as the actual Gibbs Hamiltonian.
   The represented source/sink observables inherit the correlation and closed
   calibrated-form theorems of items 6 and 7. Reuse the existing seed
   representation's injectivity and prove injectivity of the same coherent
   complexification directly from `Matrix.reindexAlgEquiv` and
   `Complex.ofReal_injective`. The native source/sink words then remain nonzero
   in that completed representation when the second mode satisfies `i ≠ 4`.
   Derive vanishing of charged finite
   Gibbs readouts from the commutator identity. On the geometric side, prove
   endpoint stabilizer conjugation and chart preservation for the existing
   Pin action, recording the odd-Pin sign explicitly. Restriction to four
   Lorentz coordinates requires preservation of the embedded six-dimensional
   slice; this is an explicit hypothesis, not a classification of the full
   native infinity stabilizer as the Poincare group.

## Dependency and verification discipline

The finite algebraic owners feed the existing categorical direct limits and
GNS completion. They do not replace those constructions by a scalar or
measure-theoretic proxy. Infinity as a projective section and infinity as an
inductive boundary are related only by explicit maps and compatibility laws.
Neither the alternating infinity form nor a grade-reversing automorphism is
identified with a state-dependent Tomita modular operator by definition.

New owner files are reviewed against this contract before promotion from the
candidate directory. Proof checks are serial, share the build lock, rebuild
changed source dependencies, and audit all newly owned declarations for
nonstandard axioms. Dependent repair scope is traced from changed definitions.
Dependency pins remain unchanged: the documented LeanArchitect incompatibility
still separates strict pinned verification from diagnostic verification with
the explicitly recorded clean alternative revision. The validation receipt
must report that distinction and the exact checked source hashes.

## Integration map

The package entry point remains:

```lean
import InfoGeometry.Twistor.PluckerInfinityModular
```

| Area | Native carrier and API |
| --- | --- |
| Signed conformal reflection | `PluckerSheetReflection`, `PluckerPinEndpointStabilizers`, and `PluckerPinAffineRestriction` connect actual twistor, Plucker, real-six, and Pin actions, with all endpoint signs retained. |
| Calibrated Clifford representation | `Cl55WittCalibratedGamma.wittGamma_square` supplies the Clifford universal property; `Cl55WittCalibratedRepresentation.cl55WittAlgEquiv` calibrates the named generators and the central number shift. |
| Five homogeneous components | `Cl55WittInternalFiveGrading.wittFiveGradeDecomposition` and `Cl55NativeInternalFiveGrading.nativeWittFiveGradeDecomposition` give the decomposition; `native_component_grade` reads each transported component with the original native commutator. |
| Inductive boundary | `Cl55WittCalibratedColimit.cl55WittColimit` is the actual canonical stage inclusion composed with the calibrated map. Its injectivity, bonding, universal-lift, number/chiral-grade, and source/sink laws are exposed separately. `cl55WittUHF` uses the existing BitWord colimit equivalence. |
| Exterior operators | The repaired `ExteriorContractionOperatorBridge` supplies actual contraction. `ExteriorFockOperatorLaws` evaluates mixed CAR, one/two particles, Berezin integration, and the split Clifford square. `FockNumberOperatorBridge` evaluates occupation and its quadratic law. |
| Exterior degree and helicity | `WittenExteriorHelicity` derives the Euler action on the entire homogeneous exterior power. `WittenCl55ExteriorBridge` uses the existing Clifford/exterior calibration, and `WittenExteriorScalarExtension` makes the real-to-complex coefficient map explicit. |
| Spinor geometry | `WittenSpinorHelicity`, `WittenSpinorBCFW`, and `WittenIncidence` provide the rank-one momentum, null-shift, and common-projective-line APIs. `WittenParkeTaylor` is an algebraic rational-expression API; `WittenCollinearityOperator` is an actual polynomial derivation. |
| Analytic operator correlations | `ComplexTimeCorrelation` provides the generic analytic and strip theorems. `FilteredGNSMatrixAnalyticKMS` elaborates their native GNS assembly with a variable compatible state family and an explicit algebraic twisted-cyclicity premise. `FiniteSeedRepresentedAnalyticKMS` specializes it to the actual represented Gibbs state and discharges that premise from the existing Gibbs-colimit identity. |
| Hestenes--Krein language | `ComplexOperatorBilingualAnalyticity` calibrates a form to the same operator-valued function and uses its real derivative. `FilteredGNSHestenesPhaseCone` instantiates the existing cones with the actual GNS stages, transitions, inclusions, and actions. |
| Stage Tomita construction | `MatrixTraceTomitaColimit` and `FiniteSeedGibbsTomitaClosability` instantiate the existing categorical operator and modular-form completion after proving all stage closability obligations. The finite faithful-state and positive-density arguments are reusable helper owners. |
| Chiral consumer | `Cl55ChiralAnalyticKMS` uses the actual Hermitian chiral image as Hamiltonian, proves injectivity and nonzero distinct-mode observables, and applies the KMS and calibrated-form laws to their correlations. |

The executable validation scope and source hashes are recorded in
[`PLUCKER_INFINITY_MODULAR_VALIDATION.json`](PLUCKER_INFINITY_MODULAR_VALIDATION.json).
The trust audit selects imported module owners, including repaired owners and
private/generated declarations. Its declaration counts are distinct from a
count of manually authored source theorems.
