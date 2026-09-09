# Binary simplex extension: verified mathematical scope

2026-09-07. This reconstructs a mathematical model from the spectrometry
brainstorm. It does not assert that the experiment realizes every structure.
The intended presentation location is the mathematical backup section.

## The chain

1. **Binary distinction and independence.** A probability vector belongs to
   Mathlib's `stdSimplex`. The product of two such vectors constructs an
   independent joint law. An ordered mismatch has probability p(1-p) for
   equal marginals; either mismatch has probability 2p(1-p). An event and
   its own complement are disjoint, not independent copies.
2. **Amplitudes.** Componentwise nonnegative square roots give an equivalence
   from the finite simplex to the nonnegative unit sphere, including boundary
   points. Products factorize and amplitude overlaps multiply. Complex phases
   and quantum dynamics are additional data. The binary outer product agrees
   with the existing covariance-projection owner.
3. **Quadratic response.** For I(X)=CX-BX², p=BX/C gives
   B I/C²=p(1-p). Under X'=aX, C'=C/a and B'=B/a², p and I are invariant,
   whereas C/B scales by a. Distance is absent from this construction.
4. **Centered moments and thermodynamic duality.** The Bernoulli Massieu
   potential Ψ(θ)=log(1+exp θ) has Ψ'=p and Ψ''=p(1-p). Differentiating the
   variance gives the third centered moment p(1-p)(1-2p). The fourth cumulant
   is the fourth centered moment minus three times the variance squared.
   The existing Amari owner supplies the entropy/Legendre contact identity.
5. **Aitchison geometry.** CLR(p,1-p)=(logit(p)/2,-logit(p)/2).
   Its squared Euclidean distance is half the squared logit difference.
   Its probability-coordinate metric is 1/[2p²(1-p)²], distinct from the
   Fisher coefficient 1/[p(1-p)]. Thus the squared-logit metric studied in
   the brainstorm is twice this binary Aitchison convention.
6. **Negative-log barrier and its dual.** F(x)=-log x on x>0 has convex
   conjugate F*(y)=-1-log(-y) for y<0, attained at x=-1/y. This is proved
   as `IsGreatest` of the native set of primal objective values. The interval
   barrier b(p)=-log p-log(1-p) is the unweighted trace of the diagonal
   surprisal. Shannon entropy is its probability-weighted mean. Its Hessian
   b''=1/p²+1/(1-p)² equals the squared-logit metric minus twice Fisher.
   Its actual Hessian derivative satisfies the self-concordance inequality
   |b'''| ≤ 2 sqrt(b'') b'', using the existing positive-cone owner.
7. **Doubled geometry.** The existing neutral metric and skew form on E×E
   admit the concrete Bernoulli Legendre graph (θ,p(θ)). Its tangent is
   isotropic for the skew form; the metric pullback is 2Ψ''. This is a
   para-Hessian graph calculation, not a nondegenerate symplectic geometry
   on a one-dimensional simplex or a para-hyper-Kähler theorem.
8. **Two mathematical evolutions.** Affine logit motion solves the
   squared-logit metric's coordinate geodesic equation and a stationary
   Hamilton–Jacobi equation with H=2v². A different trajectory,
   p(t)=logistic(θ₀ exp(-t)), realizes the Fisher-gradient entropy field
   p'=-p(1-p)logit(p); its Shannon entropy is monotone. These are distinct
   dynamics, not two names for one evolution.
9. **A constructed metriplectic model.** On (q,r,p), H=(q²+r²)/2 and
   S=-negativeEntropy(p). The canonical skew operator on (q,r) and the
   positive probability mobility give flow (r,-q,-p(1-p)logit(p)). Every law
   of the existing `GenericMetriplecticFlow.System` is proved for these maps.
   Actual curve derivatives identify dH and dS. No entropy-production
   hypothesis is inserted to obtain the second law.
10. **Finite modular time.** For a faithful diagonal probability state,
    σ_t(A)_ij=exp(it(log p_i-log p_j))A_ij is a native algebra equivalence
    with inverse σ_-t and preserves adjoints. Its matrix-valued derivative
    at zero is -i times the existing relative-surprisal log action. CLR
    differences give exactly the same frequencies. Diagonal observables
    are fixed. This is an observable-algebra time parameter, not motion of
    the classical probabilities and not the laboratory clock.

The negative-log potential, its gradient, its Hessian, and the modular
Hamiltonian are different types of objects. A Hessian can define a quadratic
local approximation or a change of tangent coordinates; it is not thereby
equal to -log ρ. “Harmonized” needs such a concrete operation before it names
a theorem. The philosophical question—how much geometry can grow from a
binary distinction—is appropriate discussion, not an additional proof claim.

## Repository search and reuse

`context_preflight.py` was followed by source-content searches across `lean/`
and `proofs/`, including alternate Amari, Madelung, CLR, Souriau, barrier,
para-Hessian, and relative-surprisal terminology. File names were navigation.
The important owners inspected and reused are:

- `Probability/SimplexQuadraticResponse.lean`: response derivative,
  variance, reflection, rapidity, dead-time bounds, radial inversion,
  velocity-field geodesic identity. The overlapping draft was removed;
  the extension imports this owner.
- `Canonical/AmariBinarySimplexBridge.lean`: logistic/logit inverse,
  Massieu/entropy derivatives, Fisher and Legendre contact.
- `Probability/FisherRaoMadelungIsometry.lean`,
  `Canonical/FiniteFisherRaoSquareRoot.lean`,
  `Probability/SquareRootSimplexBridge.lean`: existing amplitude geometry.
- `Krein/FiniteCovarianceMajoranaBlock.lean`: actual binary projection.
- `Probability/AitchisonFinite.lean`: CLR, centered hyperplane, softmax inverse.
- `Topology/FiniteGibbsFisherBridge.lean`: finite mean and centered variance.
- `Geometry/ParaHessianMixedPotential.lean`: native doubled linear maps,
  genuine derivative of the potential, neutral metric and skew form.
- `Thermo/GenericMetriplecticFlow.lean`: finite GENERIC structure and laws.
- `Convex/BipolarLogitBarrierDuality.lean`,
  `Modular/SelfConcordantBarrierTriple.lean`,
  `Analysis/SpectralSurprisalLogDetBridge.lean`: barrier and spectral owners.
- `OperatorAlgebra/FiniteRelativeModularLogBridge.lean`: relative-log operator.

The Souriau foliation, coadjoint-orbit and Souriau/Tomita/BKM dictionary files
also exist, but some results consume orbit, equality, or positivity fields.
Those interfaces were not promoted into proofs of general coadjoint orbits,
Type III modular theory, or infinite-dimensional dynamics. Existing staged
work in them was preserved. The new finite constructions require no such
interpretive fields.

## New source and verification

Eight small owner extensions, under `lean/InfoGeometry/`:

| File | Added content |
|---|---|
| `Probability/SimplexPairingAmplitude.lean` | Native simplex equivalence, independent products, amplitude overlaps |
| `Analysis/QuadraticResponseSimplex.lean` | Coordinate covariance, normalized response, exact maximum characterization |
| `Analysis/LogOddsSimplexGeometry.lean` | Actual metric connection, trajectory derivatives, Hamilton–Jacobi |
| `Probability/BinaryAitchisonMoments.lean` | CLR normalization, centered moments, entropy gradient |
| `Geometry/BinaryLegendreEntropyFlow.lean` | Legendre tangent and explicit entropy-increasing trajectory |
| `Thermo/BinaryEntropyMetriplectic.lean` | Concrete GENERIC instance with proved differential and degeneracy laws |
| `Convex/BinaryBarrierSurprisal.lean` | Barrier/entropy distinction, genuine third derivative, conjugate maximum |
| `Modular/FiniteSimplexModularTime.lean` | Finite adjoint-preserving automorphisms and actual logarithmic generator |

Reproduce the import closure and axiom audit:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Probability.SimplexExtensionAudit
python3 scripts/verify_simplex_response.py
```

`SimplexExtensionAudit.lean` checks the dependencies of all 91 new definitions
and theorems. They use at most `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or custom axiom dependency. The eight owners compile
without new-source warnings and pass the semantic-vacuity gate with warnings
treated as failures. `scripts/verify_simplex_response.json` contains the
deterministic auxiliary CAS checks; Lean proofs do not consume CAS assertions.

Scope of build evidence: the selected import closure succeeds (8,097 Lake
jobs including cached dependencies). This is not a clean audit of every
repository module. Pre-existing dependency linter warnings and Lake manifest
warnings remain; caches and dependency manifests were preserved.
