# Operator algebra: owner map and scope

> **Source review:** 2026-11-02 at [214f7bc](https://github.com/nickgou-nuke/info-geometry-lean/tree/214f7bcf733eaf4720913bc2c082936f2480d3fc). This is a navigation map to the
> current declarations and their assumptions, not a build certification.
> Validation of the nilpotent-calculus additions is recorded separately in
> [their theorem contract](../../../docs/PEIRCE_NILPOTENT_COLIMIT_CONTRACT.md).

This directory contains Peirce and Lie–Jordan algebra, square-zero and CAR
constructions, native superoperators, matrix and Hilbert-space results,
algebraic limit transport, and several domain bridges. Start from the owner
of the required statement and inspect its carrier, hypotheses, imports, and
consumers. [All.lean](All.lean) is a broad import umbrella; importing two
families together does not prove a relationship between their carriers.
The repository search procedure is
[REPO_DEEP_SEARCH_PROTOCOL.md](../../../docs/REPO_DEEP_SEARCH_PROTOCOL.md),
and contributor instructions are in [AGENTS.md](../../../AGENTS.md).

## Main owner families

This table is a practical entry map, not an exhaustive theorem inventory.

| Family | Entry points and concrete owners | What to check before reusing a result |
|---|---|---|
| Peirce operator spine | [PeirceSpine.lean](PeirceSpine.lean), [Basic.lean](PeirceSpine/Basic.lean), [Tetraktys.lean](PeirceSpine/Tetraktys.lean), [CyclotomicBridge.lean](PeirceSpine/CyclotomicBridge.lean) | The base is an associative ring with `P*P = P` and corners `P*A*(1-P)`, `(1-P)*C*P`. Star, scalar, or normalization assumptions belong to the specific extension. The [archetype ledger](../../../docs/PEIRCE_OPERATOR_ARCHETYPES.md) records owners and corrected formulas. |
| Lie–Jordan and dissipator identities | [LieJordanDuality.lean](LieJordanDuality.lean), [PeirceLieJordanResolution.lean](PeirceLieJordanResolution.lean), [PeirceDissipatorTrinity.lean](PeirceDissipatorTrinity.lean) | Ring identities and linear endomorphism identities have different interfaces. Reflexive-pair results add `uvu = u`, `vuv = v` to square-zero assumptions; do not infer them from arbitrary corners. |
| Square-zero spectral superoperators | [SquareZeroPairSpectral.lean](SquareZeroPairSpectral.lean), [InnerDerivationSpectra.lean](SquareZeroPairSpectral/InnerDerivationSpectra.lean), [KleinHadamard.lean](SquareZeroPairSpectral/KleinHadamard.lean) | The quadratic coupling `V = uv + vu` is operator-valued. Action formulas and homogenized projector identities retain their `V` factors; scalar eigenvalues, nonzero eigenvectors, or a positive gap need additional results. |
| Square-zero polynomial calculus | [SquareZeroPolynomial.lean](SquareZeroPolynomial.lean), [PolynomialTrace.lean](PeirceSpine/PolynomialTrace.lean) | Native `Polynomial.aeval` in a noncommutative algebra: Taylor truncation requires the base to commute with the direction, whereas a Peirce shear has the separate coefficient `F(1)-F(0)`. The exponential result uses Mathlib's finite `IsNilpotent.exp`. Graded polynomial traces retain exactly their constant coefficient. |
| Peirce superoperators and matrix Hodge kernels | [PeirceSuperoperators.lean](PeirceSuperoperators.lean), [HodgeKernel.lean](PeirceSuperoperators/HodgeKernel.lean), [DoubleCommutator.lean](PeirceSuperoperators/DoubleCommutator.lean) | The Hodge/energy statements use the full finite complex matrix carrier with its Hilbert–Schmidt structure. For example, the Jordan Gram kernel is characterized by simultaneous left/right annihilation; the paired double-commutator owner has its own common-kernel and positivity statements. |
| Opposite-corner coupling | [PeirceCoupling.lean](PeirceCoupling.lean), [Algebra.lean](PeirceCoupling/Algebra.lean), [GramGeometry.lean](PeirceCoupling/GramGeometry.lean), [PeirceCartanColimit.lean](PeirceCartanColimit.lean) | The algebraic starting point has independently chosen opposite corners. Trace, adjoint, Gram, reflection, and direct-limit results add their own assumptions; positivity is not a consequence of a bare ring identity. |
| CAR and Clifford–Dirac operators | [CliffordCAR.lean](CliffordCAR.lean), [CARFermionParity.lean](CARFermionParity.lean), [CliffordDirac.lean](CliffordDirac.lean), [CliffordDirac/Operators.lean](CliffordDirac/Operators.lean) | Keep the concrete CAR carrier distinct from an arbitrary Clifford–Dirac endomorphism algebra. The latter retains mixed commutator defects unless the theorem assumes their vanishing. CAR parity factors anticommute with the corresponding odd generators. |
| Tripotent grades, parity, and kernel restriction | [TripotentParity.lean](PeirceSpine/TripotentParity.lean), [TripotentChiralRestriction.lean](../Core/TripotentChiralRestriction.lean), [NuclearFiveGradeParity.lean](../Physics/NuclearFiveGradeParity.lean) | Grade regrouping is polynomial; grade signs require `T³ = T`. The chiral kernel equivalence additionally requires `ΓT = -TΓ` and `Γ² = 1`. Nuclear block invariance requires the specified grades (or their projectors). These are separate actions on named carriers. |
| Algebraic full-matrix limit transport | [LieJordanPeirceColimit.lean](LieJordanPeirceColimit.lean), [MatrixColimitTransport.lean](PeirceSpine/MatrixColimitTransport.lean), [Cl11TensorTowerLimit.lean](../Clifford/Cl11TensorTowerLimit.lean) | These use the actual stage maps of the algebraic matrix direct limit. An algebraic limit theorem does not by itself supply a norm completion, a state, or a continuum field theory. |
| Matrix restriction and nilpotent colimit calculus | [Cl11ConditionalExpectation.lean](../Canonical/Cl11ConditionalExpectation.lean), [TensorPolynomialTrace.lean](../Canonical/TensorPolynomialTrace.lean), [TensorNilpotentCalculus.lean](../Canonical/TensorNilpotentCalculus.lean) | The existing normalized partial trace is positive and bimodular, with explicit discarded nonzero matrix units. The existing limit trace supports polynomial cancellation and real Cauchy–Schwarz. Coherent idempotents seeded at scalar stage zero are necessarily trivial; use a positive-stage seed for nonzero corners. See the [theorem contract](../../../docs/PEIRCE_NILPOTENT_COLIMIT_CONTRACT.md). |
| Operator Dirichlet and resolvent formulas | [OperatorDirichlet.lean](OperatorDirichlet.lean), [SpineResolvent.lean](OperatorDirichlet/SpineResolvent.lean), [MatrixLegendre.lean](OperatorDirichlet/MatrixLegendre.lean) | Resolvent results state the needed unit/inverse hypotheses; the characteristic value may be the operator `V`. Cyclotomic and Dirichlet labels do not themselves imply analytic zeta-function statements. |
| Complex bounded operators and GNS models | [ComplexBoundedOperators.lean](ComplexBoundedOperators.lean), [HilbertBasisParseval.lean](ComplexBoundedOperators/HilbertBasisParseval.lean), [GNSFiniteSupport.lean](ComplexBoundedOperators/GNSFiniteSupport.lean) | The umbrella exposes Hilbert-basis/Parseval adapters. The finite-support GNS owner uses the commutative algebra `Fin n → ℂ` and an explicit active support; inspect the specific model before transferring a kernel or quotient claim to another carrier. |
| Jones optics and material response | [OperatorialJonesCalculus.lean](OperatorialJonesCalculus.lean), [SusceptibilityHessian.lean](SusceptibilityHessian.lean), [StatisticalChannels.lean](OperatorialJonesCalculus/StatisticalChannels.lean), [HessianResponse.lean](SusceptibilityHessian/HessianResponse.lean) | These include data interfaces as well as theorems. For example, `PolarizationChannel` supplies a channel field, while Hessian regularity is defined by bijectivity of a supplied response operator; a physical evolution law is not inferred from those fields. |
| Affine and Virasoro bridges | [AffineVirasoroBridge.lean](AffineVirasoroBridge.lean), [VirasoroProjectBridge.lean](VirasoroProjectBridge.lean) | The abstract datum supplies modes and a central element. Concrete realization and bracket theorems, including the conditional Heisenberg construction, are described below. |

## Reading algebraic and spectral claims

For the Peirce pair, `genV = N₊*N₋ + N₋*N₊` belongs to the same operator
ring as the generators. In particular, a formula `D(J) = -4 • (genV * J)`
keeps an ordered operator product. It supplies a scalar eigenvalue only after
an additional theorem identifies multiplication by `genV` with the required
scalar action on a specified nonzero element. A physical gap additionally
needs a stated operator, representation, spectrum, and lower-bound theorem.

Likewise, [CyclotomicBridge.lean](PeirceSpine/CyclotomicBridge.lean) proves
A58–A60 as polynomial identities for an idempotent in an arbitrary ring.
The A58/A59 root-of-unity and group relations specialize on the unit shell
`genV P A C = 1`; the general formulas retain the defect and coupling factors.
A60 uses `s3Refl1 - s3Refl2 = -genJ - 2 • genSig` and the negative
`-16 • ((genV * genV) * genSig)` tomography term. These polynomial identities
do not alone prove a faithful group realization.

The `peirce_nf hP` macro in [Basic.lean](PeirceSpine/Basic.lean) combines a
selected `simp only` rewrite set with `abel`. Callers supply the definitions
to unfold beyond that set. Successful use proves the individual goal; a
claim that it decides every ring identity, or that a proposed Knuth–Bendix
completion is complete, would require a separately stated metatheorem.

## Virasoro bridge details and reusable notes

[AffineVirasoroBridge.lean](AffineVirasoroBridge.lean) defines `VirasoroDatum`
as modes and a central element. Its bracket/centrality projection lemmas take
the relevant laws as explicit hypotheses. The concrete
[VirasoroProjectBridge.lean](VirasoroProjectBridge.lean) connects this datum to
the imported [VirasoroAlgebra implementation](../External/Virasoro/VirasoroAlgebra.lean):

- `VirasoroProjectRealizes` identifies the witness's modes and central element
  with the concrete generators. `virasoro_project_has_realized_datum` proves
  existence of that specified witness; `virasoro_project_is_certified` is a
  compatibility theorem name for the same proposition, not a CI status.
- `virasoroProjectVirasoroDatum_central_commutes` and
  `virasoroProjectVirasoroDatum_bracket` prove the concrete bracket laws.
- `heisenbergSugawaraDatum` sets `level = 1`, `dimG = 1`, `hDual = 0`, and
  `centralCharge = 1`; `heisenbergSugawaraDatum_sugawara` verifies the scalar
  central-charge formula for that calibration.
- The stronger `currentHeisenbergVirasoroDatum_bracket` constructs the
  endomorphism-valued Virasoro bracket from a supplied `CurrentHeisenbergRep ℝ V`,
  via [CurrentSugawaraBridge.lean](../Canonical/CurrentSugawaraBridge.lean).
  Retain that representation hypothesis when describing the result.

Two proof-engineering notes from the earlier bridge README remain useful:

1. **Central-term scaling.** When a goal differs by whether scalar
   multiplication sits inside an `if`, try `rw [← smul_ite_zero]` or
   `simp only [smul_ite, smul_zero]`. Compare the actual normalized bracket
   formula first; the current concrete proof also splits on `m + n = 0`.
2. **A witness must identify its implementation.** Follow the concrete
   `VirasoroProjectRealizes` pattern rather than replacing a realization
   statement by a vacuous existential such as `∃ D, True`.

## Validation records

Report build results with the revision, exact targets, command, and outcome.
The former `CERTIFIED`/`STABLE` table is replaced by the theorem-level source
map above because a historical label does not establish a present build.
Follow the root [AGENTS.md](../../../AGENTS.md) for locked build commands and
the scope of proof-hygiene checks. A documentation edit or a source scan does
not substitute for compiling a named target and, when required, inspecting
its declaration axioms.
