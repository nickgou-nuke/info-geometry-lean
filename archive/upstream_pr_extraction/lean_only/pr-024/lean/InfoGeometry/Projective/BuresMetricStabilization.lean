import Mathlib
import InfoGeometry.Canonical.TensorColimitExpectation

/-!
# Bures Metric Stabilization

Theorem-safe metric layer for finite-stage Bures/Fisher distances pulled back
along an inductive tensor-colimit state interface.

This module does not construct the analytic Bures metric, square roots of
positive operators, trace-class completions, GNS Hilbert spaces, or a
Tomita--Takesaki modular operator.  A concrete Bures/Fisher distance is supplied
as a scalar function on the chosen finite state space, and this file proves the
colimit restriction/readback laws that make such a distance stable along the
already formalized tensor-colimit functional interface.

#### BUCKET 1: CLOSED FINITE THEOREMS
Pullback distances inherit diagonal vanishing and nonnegativity from a supplied
finite distance.  Global functionals that extend compatible finite families
restrict back to the finite linear functionals, so any finite metric computed
after restriction is exactly the finite-stage metric.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
Isometry/stabilization claims depend on an explicit distance-preservation
premise for the chosen bonding or restriction map.

#### BUCKET 3: OPEN CLOSURE DEBT
No analytic Bures formula, operator square-root theorem, C*-completion theorem,
or GNS/Tomita modular theorem is asserted here.
-/

namespace InfoGeometry.Projective.BuresMetricStabilization

open InfoGeometry.Canonical.TensorColimitExpectation

universe u v w

/-! ## Abstract pullback distance layer -/

/-- Pull a finite/state-space distance back along a restriction map. -/
def pullbackDistance
    {StateInf : Type u} {StateStage : Type v}
    (restrict : StateInf → StateStage)
    (dStage : StateStage → StateStage → ℝ) :
    StateInf → StateInf → ℝ :=
  fun ρ σ => dStage (restrict ρ) (restrict σ)

/-- Pullback distance vanishes diagonally when the finite distance does. -/
theorem pullbackDistance_self
    {StateInf : Type u} {StateStage : Type v}
    (restrict : StateInf → StateStage)
    (dStage : StateStage → StateStage → ℝ)
    (hself : ∀ ρ : StateStage, dStage ρ ρ = 0)
    (ρ : StateInf) :
    pullbackDistance restrict dStage ρ ρ = 0 :=
  hself (restrict ρ)

/-- Pullback distance is nonnegative when the finite distance is. -/
theorem pullbackDistance_nonneg
    {StateInf : Type u} {StateStage : Type v}
    (restrict : StateInf → StateStage)
    (dStage : StateStage → StateStage → ℝ)
    (hnonneg : ∀ ρ σ : StateStage, 0 ≤ dStage ρ σ)
    (ρ σ : StateInf) :
    0 ≤ pullbackDistance restrict dStage ρ σ :=
  hnonneg (restrict ρ) (restrict σ)

/-- A supplied distance-preserving map gives an isometry readback. -/
theorem distance_preserving_readback
    {StateA : Type u} {StateB : Type v}
    (dA : StateA → StateA → ℝ)
    (dB : StateB → StateB → ℝ)
    (f : StateA → StateB)
    (hIso : ∀ ρ σ : StateA, dB (f ρ) (f σ) = dA ρ σ)
    (ρ σ : StateA) :
    dB (f ρ) (f σ) = dA ρ σ :=
  hIso ρ σ

/-! ## Tensor-colimit functional restriction layer -/

section TensorColimit

variable {R : Type u} [CommSemiring R]
variable {A : ℕ → Type v}
variable [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]
variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
variable (L : TensorInductiveLimit (A := A) bond)

/-- Restrict a global colimit functional to finite stage `n`. -/
def stageFunctionalRestriction (n : ℕ) (Ω : L.LimitFunctional) : A n →ₗ[R] R where
  toFun x := Ω (L.inj n x)
  map_add' x y := by
    simp
  map_smul' r x := by
    simp

/-- A global functional extending a finite family restricts to that finite functional. -/
theorem stageFunctionalRestriction_eq_finite
    (F : CompatibleFunctionalFamily (A := A) bond)
    (Ω : L.LimitFunctional)
    (hΩ : L.ExtendsFamily F Ω)
    (n : ℕ) :
    stageFunctionalRestriction L n Ω = F.omega n := by
  ext x
  exact hΩ n x

/--
Any finite-stage Bures/Fisher distance computed after restricting two global
functionals agrees with the finite distance of the owner finite functionals.
-/
theorem finite_metric_of_restricted_global_functionals
    (F G : CompatibleFunctionalFamily (A := A) bond)
    (Ω Ψ : L.LimitFunctional)
    (hΩ : L.ExtendsFamily F Ω)
    (hΨ : L.ExtendsFamily G Ψ)
    (n : ℕ)
    (dStage : (A n →ₗ[R] R) → (A n →ₗ[R] R) → ℝ) :
    dStage (stageFunctionalRestriction L n Ω) (stageFunctionalRestriction L n Ψ) =
      dStage (F.omega n) (G.omega n) := by
  rw [stageFunctionalRestriction_eq_finite L F Ω hΩ n]
  rw [stageFunctionalRestriction_eq_finite L G Ψ hΨ n]

/--
If a chosen finite metric is preserved by a stage-state transition, then its
pullback through global restrictions is preserved as well.
-/
theorem restricted_metric_isometry_of_stage_isometry
    (StateStage StateNext : Type w)
    (restrict : L.LimitFunctional → StateStage)
    (advance : StateStage → StateNext)
    (dStage : StateStage → StateStage → ℝ)
    (dNext : StateNext → StateNext → ℝ)
    (hIso : ∀ ρ σ : StateStage, dNext (advance ρ) (advance σ) = dStage ρ σ)
    (Ω Ψ : L.LimitFunctional) :
    dNext (advance (restrict Ω)) (advance (restrict Ψ)) =
      pullbackDistance restrict dStage Ω Ψ :=
  hIso (restrict Ω) (restrict Ψ)

end TensorColimit

end InfoGeometry.Projective.BuresMetricStabilization
