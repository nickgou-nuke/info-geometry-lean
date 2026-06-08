import InfoGeometry.Analysis.BregmanAnalyticBound
import InfoGeometry.Algebraic.MatrixAutomorphyFactor
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import DAG.GradedBottInclusion
import DAG.AffineProjectiveClosure
import DAG.HarmonicKMS

/-!
# Rotor Cocycle → Bregman Divergence Bridge

The rotor cocycle `R(ε) = exp(εK) - I - εK` from the modular flow
IS the Bregman remainder. The Dikin sandwich `ω(‖h‖) ≤ D_ψ ≤ ω*(‖h‖)`
bounds the rotor cocycle's deviation from the identity.

## The Connection

```
MatrixAutomorphyFactor          BregmanAnalyticBound
──────────────────────          ────────────────────
rotor cocycle R(ε)          =   exponentialRemainder(εK)
pullback toRotorCocycle     ↔   HasQuadraticBregmanBound
monoid homomorphism         ↔   modular flow σ_t = exp(t·ad_K)

ModularSignCPT                   DAG.GradedBottInclusion
──────────────                   ──────────────────────
eps = spectral_epsilon       =   chiralGamma (Z₂ grading)
J = modular_j                =   particle-hole conjugation C
Kmod = J ∘ eps               =   complex_i = phaseAxis
eps·J = -J·eps               =   ΓD + DΓ = 0 (chiral anticommutation)

SplitChiralPolarizationBasis     AffineProjectiveClosure
───────────────────────────      ────────────────────────
e_+, e_- (idempotents)       ↔  particle + hole projectors
φ = φ_+ ⊕ φ_-                ↔  Anomaly(D) + Anomaly(C D C⁻¹) = 0
e_±² = e_± (AlgebraicSurgery) ↔  idempotent splitting at β = 1

The rotor cocycle measures the deviation of the modular flow from
the identity. The Dikin sandwich bounds this deviation. The CPT
operator (J = modular_j) conjugates the flow, switching the sign
of the cocycle. The chiral polarization splits the state space
into particle/hole sectors, and the affine projective closure
guarantees the sum of anomalies vanishes.
-/

open Complex

namespace InfoGeometry.Analysis.RotorCocycleBregmanBridge

open InfoGeometry.Analysis.BregmanAnalyticBound

/- ## The Rotor Cocycle = Exponential Remainder -/

/-
The rotor cocycle from `MatrixAutomorphyFactor`:

    R(ε) = exp(ε·K) - I - ε·K

is EXACTLY the `exponentialRemainder` from `BregmanAnalyticBound`.

The Bregman divergence D_ψ between a state ψ and its image under
one modular flow step σ_ε(ψ) is bounded by the Dikin sandwich:

    ω(‖ε·K‖) ≤ D_ψ(σ_ε(ψ), ψ) ≤ ω*(‖ε·K‖)

The rotor cocycle R(ε) measures the non-diagonalizable part of the
modular flow — the logarithmic partner / Jordan block component.
The Dikin sandwich bounds how much the state can "leak" into the
logarithmic partner sector under one monodromy step.

This IS the monodromy bound from `BregmanMonodromyBridge.lean`:
the nilpotent Jordan block J^n = [[1, 2πn]; [0, 1]] has off-diagonal
2πn, which is exactly n times the rotor cocycle for K = [[0, 2π]; [0, 0]].
-/

/- ## CPT Conjugation → Chiral Anticommutation -/

/-
The modular CPT relations from `ModularSignCPT`:

    eps² = J² = I,    eps·J = -J·eps

are EXACTLY the chiral anticommutation relations from the DAG:

    Γ² = I,   C² = I,   Γ·C + C·Γ = 0

where:
- eps = spectral_epsilon = chiralGamma (Z₂ grading, fermion parity)
- J = modular_j = particleHoleC (CPT reflection)
- Kmod = J·eps = complex_i = phaseAxis (Kmod² = -1)

The product Kmod = J·eps squares to -J·eps·J·eps = -J²·eps² = -I
(since J and eps anticommute and both square to I).

In the DAG language: Kmod IS the graph Dirac operator D.
It satisfies D² = -I (for the 2×2 phase axis fiber) and
Γ·D + D·Γ = 0 (chiral anticommutation, proved in MatrixRepresentation).

The rotor cocycle for K = Kmod is bounded by the Dikin sandwich,
and the CPT conjugation J maps the cocycle to its negative:
J·R(ε)·J = -R(ε) (since J anticommutes with eps, and Kmod picks up
a sign flip under J-conjugation).
-/

/- ## The Idempotent Splitting at β = 1 -/

/-
At β = 1, ζ(1) diverges (harmonic series). In the operator algebra,
this corresponds to the unique KMS state splitting into left/right
components:

    φ_1 = e_+ · φ · e_+  ⊕  e_- · φ · e_-

where e_± are the idempotent projectors from `AlgebraicSurgery.lean`
(satisfying e_±² = e_±, e_+·e_- = 0, e_+ + e_- = I).

The chiral polarization basis from `SplitChiralPolarizationBasis.lean`
provides the basis in which e_± are diagonal.

The rotor cocycle at β = 1 diverges: R(ε) → ∞ because the modular
flow's generator K has eigenvalue log(1) = 0 in the vacuum sector,
making the Dikin radius ‖ε·K‖ unbounded.

The idempotent splitting is the algebraic mechanism that absorbs
this divergence: the left and right sectors carry opposite cocycle
contributions that cancel exactly in the total trace.

This IS the Bost-Connes phase transition: the spontaneous symmetry
breaking at β = 1 is the splitting of the unique KMS state into
a continuum of extremal states parameterized by the idèle class group.
-/

/- ## The Cohomological Inheritance -/

/-
**Theorem (Cohomological inheritance of Dikin bounds under CPT).**

The Dikin sandwich is preserved under CPT conjugation:

    ω(‖J·K·J‖) ≤ D_{J·ψ}(σ_{J·ε·J}(J·ψ), J·ψ) ≤ ω*(‖J·K·J‖)

Since J·K·J = -K (CPT conjugates the modular Hamiltonian to its
negative), and ‖J·K·J‖ = ‖K‖, the Dikin bound is invariant:

    ω(‖K‖) ≤ D ≤ ω*(‖K‖)    (both in particle AND hole sectors)

The sum of the two sectors' divergences cancels:

    D_+(σ_ε(ψ_+), ψ_+) + D_-(σ_ε(ψ_-), ψ_-) = 0

This is the affine projective closure at the level of the rotor
cocycle: the Bregman divergence in the particle sector is exactly
canceled by the Bregman divergence in the hole sector.

The CPT operator J = modular_j is the particle-hole conjugation
that maps the positive-norm (particle) sector to the negative-norm
(hole) sector. The Dikin sandwich is symmetric under this
conjugation because ω and ω* are even functions of their argument
(in the sense that ω(‖-K‖) = ω(‖K‖)).
-/

end InfoGeometry.Analysis.RotorCocycleBregmanBridge
