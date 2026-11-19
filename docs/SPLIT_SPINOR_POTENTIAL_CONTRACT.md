# Split spinor potential: theorem contract

Source: the user's 2026-11-16 construction of a para-Kähler potential on
`Λ W`, followed by its proposed Krein–Dirac and Souriau interpretation.
Base: upstream `main`, `08c34e03f610b452e03422037949196dc7d92d6d`.

## Intake and conventions

The intake proposes all of the following: an exterior spin representation for
`W ⊕ W*`; the even/odd split as a universal Lagrangian polarization; a
Chevalley–Mukai pairing; a quadratic potential; identification of that
potential with a Souriau log partition; a mixed Monge–Ampère volume equation;
spinor-coordinate derivatives as a moment map; a Legendre expression as
entropy; a fundamental-symmetry rescaling as a dissipation mechanism; and a
Landauer bound. The mathematical formulas and physical interpretations are
separate claims. No discarded implication is considered proved.

Keep the vector representation `W ⊕ W*`, its exterior spinor representation
`Λ W`, a polarization of that spinor representation, and a statistical
parameter space distinct. In particular, constructing the first two does not
construct a Mukai identification of the last two.

Use the existing neutral phase-space owner with

* `B ((x,ξ),(y,η)) = ξ(y) + η(x)`;
* `q (x,ξ) = ξ(x)`;
* `K (x,ξ) = (x,-ξ)`;
* `ω (X,Y) = B(KX,Y) = η(x) - ξ(y)`.

The input vector metric is `h = B/2`, so its Clifford relation is `c(X)^2 = q(X)`.
On a separately justified spinor polarization, the flat geometric metric is
`g = B` and the corresponding potential is `Ψ₀ = q = g(X,X)/2`.
Hamiltonians use `ι_(L_A X) ω = d H_A`, where `L_A` is the cotangent lift,
fixing every sign explicitly.

## Existing owners inspected

* `InfoGeometry.Clifford.NeutralPhaseSpaceCore`: actual algebraic dual carrier,
  symmetric and alternating pairings, quadratic normalization, nondegeneracy.
* `InfoGeometry.Canonical.KahlerAtiyahCartanForms`: native exterior creation,
  native Clifford contraction, CAR, and the metric-graph Clifford action.
* `InfoGeometry.Geometry.ParaHessianMixedPotential`: actual Fréchet derivative
  of the flat mixed potential on a real Hilbert carrier, mixed Hessian,
  nondegeneracy and para-Hermitian compatibility.
* `InfoGeometry.Canonical.CartanSouriauMassieuDirectionalCalculus`: finite
  classical Gibbs directional derivatives and covariance, not a continuous
  spinor-orbit Gibbs theorem.
* `InfoGeometry.Canonical.SouriauOnsagerBKMParaKahlerObstruction`: obstruction
  to identifying the positive BKM pairing with a para-Hermitian metric.

These are bounded source inspections. Their source types, not descriptive
filenames, determine what may be reused.

## New owner contracts

### Chevalley and neutral exterior compatibility

Carrier: `Module.End ℝ (ExteriorAlgebra ℝ E)`, arbitrary real module `E`.
Reuse the full `spinorAction` and `abstractSpinorRep` already constructed in
`InfoGeometry.Clifford.ChevalleySpinorBlueprint`. Prove its quadratic-form
normalization, compatibility with native creation/contraction, the full
operator CAR, generator compatibility, and a noncommutation witness.
No duplicate representation or scalar/diagonal replacement of operator products.
Faithfulness, irreducibility, a Mukai pairing, and chirality isotropy are not
claimed by this module.

### Para–Krein obstructions

Reuse `B`, `q`, and `K`. Prove `B(X,KX)=0`, `q(X)=B(X,X)/2`, and the exact
second finite difference of `q`. For an arbitrary real symmetric bilinear
form and a skew-adjoint operator prove the diagonal expectation vanishes.
For an arbitrary nontrivial noncommutative real algebra, prove a positive multiple of
an involution is an involution exactly when the multiplier is one.

### Neutral cotangent Hamiltonian

Carrier: the existing `E × Module.Dual ℝ E`. For arbitrary endomorphisms `A,B`,
construct `L_A(x,ξ)=(Ax,-ξ∘A)` and `H_A(x,ξ)=ξ(Ax)`. Prove skew-adjointness,
the symplectic quadratic formula, the directional derivative, and the ordered
commutator/Poisson compatibility. This is a linear Hamiltonian construction;
it does not construct a Lie group action, an equivariant global group moment
map, or a normalizable Gibbs measure.

### Pullback potential and mixed differential calculus

Carrier: `E × E` for an arbitrary real normed space. Choose the actual parameter
map `(x,y) ↦ x+y`, define `Ψ=f(x+y)`, and prove its native first Fréchet
derivative and mixed second derivative. Extract the symmetric mixed form and
its alternating companion from the actual derivative of `fderiv ℝ f`.
Prove nondegeneracy under explicit left/right separation hypotheses. Prove
the algebraic pullback of the Hessian bilinear form vanishes on opposite
directions and that positive parameter curvature creates negative directions
of the mixed form. The algebraic pullback identity is not itself a theorem
identifying the full second Fréchet derivative.
This is conditional differential calculus, not a construction of a particular
Gibbs model or an assumption-free identification of parameter and spinor spaces.

## Explicitly rejected or conditional implications

1. Mukai chirality cross-pairing holds only for odd `dim W`; an even-dimensional
   example disproves the proposed dimension-independent assertion.
2. `g(X,KX)/2` and `g(X,AX)/2` for real `g`-skew `A` vanish.
3. The matrix of a neutral metric is not the positive Fisher/BKM metric.
4. `J ↦ exp(σ/2) J` destroys `J²=1` unless `σ=0`.
5. Log partition requires a specified state space, measure, Hamiltonian action,
   normalizability domain, and differentiation hypotheses. Coordinate
   gradients alone do not construct a Lie-algebra moment map.
6. A volume equation with the unknown potential on both sides is implicit.
   Its determinant is normalized relative to the reference mixed Hessian.
7. A nondegenerate symplectic Poisson tensor admits only locally constant
   entropy Casimirs. Nontrivial strict metriplectic dynamics needs extra data.
8. A volume deformation does not derive a positive dissipator or a physical
   Landauer theorem. Reservoir, process, and entropy conventions are required.
9. Neither a pure-spinor cone nor its projectivization automatically inherits
   a nondegenerate restriction of the displayed symplectic form.

## Acceptance

Keep Lean and Mathlib pins unchanged. Run the maintained native source-closure
checker under the shared lock, inspect warnings for each new target, and audit
every new declaration. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. Independently review the statement/carrier boundary. Record
actual build coverage; a scoped check is not a whole-repository certificate.
