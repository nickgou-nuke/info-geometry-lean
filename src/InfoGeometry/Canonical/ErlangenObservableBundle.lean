import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.QuantumGeometry.Projective.Basic
import InfoGeometry.QuantumGeometry.Projective.QGT

/-!
# Erlangen Observable Coordinates and Log-Exponential Modular Bundle

This module formalizes:
1. **Coordinates as Observables**: Coordinate sections are self-adjoint operators over the
   projective state manifold (Erlangen geometry base).
2. **The Fundamental Log-Exponential Functor**:
   The groupoid determinant homomorphism (multiplicative 1-cocycle)
     Δ(q, q₁) = Δ(q, q₀) · Δ(q₀, q₁)
   maps under -ln to the extensive thermodynamic energy (additive 1-cocycle):
     V(q, q₁) = V(q, q₀) + V(q₀, q₁)
   with the exact bidirectional equivalence:
     Δ(q, q₀) = exp(-V(q, q₀))  ↔  V(q, q₀) = -ln Δ(q, q₀).
3. **The Conservative 1-Form & Zero Curvature**:
   Path independence of transitions and exact reversibility (First Law).
4. **The Quantum Geometric Tensor on Observable Coordinates**:
   Decomposition into the Riemannian Fisher-Fubini-Study metric and the symplectic Berry curvature.

All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.ErlangenObservableBundle

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.QuantumGeometry.Projective
open scoped InnerProductSpace

universe u

variable {α : Type u} [Fintype α] [Nonempty α]

/-!
=============================================================================
PART 1: The Fundamental Log-Exponential Functor on Projective States
=============================================================================
-/

/-- 
  THEOREM 1: The Multiplicative-to-Additive Logarithmic Map
  The relative modular potential V is the exact negative logarithm of the relative density Δ:
    V(q, q₀)(a) = -ln(Δ(q, q₀)(a))
-/
theorem modularPotential_eq_neg_log_relativeDensity (q q0 : PositiveRay α) (a : α) :
    relativeModularPotential q q0 a = -Real.log (relativeDensity q q0 a) := by
  rw [relativeModularPotential_eq_neg_relativeLogDensity,
      relativeDensity_eq_exp_relativeLogDensity,
      Real.log_exp]

/-- 
  THEOREM 2: The Canonical Exponential Map (The Gibbs Theorem)
  The relative density Δ is the exact exponential of the negative modular potential:
    Δ(q, q₀)(a) = exp(-V(q, q₀)(a))
-/
theorem relativeDensity_eq_exp_neg_modularPotential (q q0 : PositiveRay α) (a : α) :
    relativeDensity q q0 a = Real.exp (-relativeModularPotential q q0 a) := by
  rw [relativeModularPotential_eq_neg_relativeLogDensity, neg_neg]
  exact relativeDensity_eq_exp_relativeLogDensity q q0 a

/-- 
  THEOREM 3 (The Fundamental Functor of Algebraic Thermodynamics):
  The Multiplicative 1-Cocycle Groupoid (Volume / Measure) maps functorially
  to the Additive 1-Cocycle Groupoid (Energy / Generator):
    1. Multiplicative Cocycle: Δ(q, q₁) = Δ(q, q₀) · Δ(q₀, q₁)
    2. Additive Cocycle:       V(q, q₁) = V(q, q₀) + V(q₀, q₁)
    3. Exponential Bridge:     Δ = exp(-V)
    4. Logarithmic Bridge:     V = -ln Δ
-/
theorem fundamental_log_exponential_functor (q q0 q1 : PositiveRay α) (a : α) :
    (relativeDensity q q1 a = relativeDensity q q0 a * relativeDensity q0 q1 a) ∧
    (relativeModularPotential q q1 a = relativeModularPotential q q0 a + relativeModularPotential q0 q1 a) ∧
    (relativeDensity q q1 a = Real.exp (-relativeModularPotential q q1 a)) ∧
    (relativeModularPotential q q1 a = -Real.log (relativeDensity q q1 a)) := by
  refine ⟨relativeDensity_cocycle q q0 q1 a,
          relativeModularPotential_cocycle q q0 q1 a,
          relativeDensity_eq_exp_neg_modularPotential q q1 a,
          modularPotential_eq_neg_log_relativeDensity q q1 a⟩

/-!
=============================================================================
PART 2: Conservative Field, Path Independence and Zero Curvature (d² = 0)
=============================================================================
-/

/-- 
  THEOREM 4 (Path Independence of Thermodynamic Transitions):
  Transitioning between any two states through an intermediate state requires
  identically the same modular potential sum.
-/
theorem path_independence_modular_work (q_start q_mid q_end : PositiveRay α) (a : α) :
    relativeModularPotential q_start q_end a =
      relativeModularPotential q_start q_mid a + relativeModularPotential q_mid q_end a :=
  relativeModularPotential_cocycle q_start q_mid q_end a

/-- 
  THEOREM 5 (Closed Loop Reversibility / First Law of Thermodynamics):
  The cyclic integral of the modular potential around any closed loop vanishes identically:
    V(q, q₀) + V(q₀, q) = 0
-/
theorem closed_loop_zero_curvature (q q0 : PositiveRay α) (a : α) :
    relativeModularPotential q q0 a + relativeModularPotential q0 q a = 0 := by
  have h_cocycle := relativeModularPotential_cocycle q q0 q a
  have h_self : relativeModularPotential q q a = 0 := relativeModularPotential_self q a
  rw [h_self] at h_cocycle
  exact h_cocycle.symm

/-!
=============================================================================
PART 3: Coordinates as Observables in the Quantum Geometry Bundle
=============================================================================
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- A self-adjoint observable coordinate operator on the Hilbert fiber. -/
structure ObservableCoordinate (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : H →L[ℂ] H
  is_self_adjoint : ContinuousLinearMap.adjoint op = op

/-! The scalar expectation is kept complex-valued until self-adjointness is
    used.  This avoids silently treating an arbitrary operator expectation as
    a positive projective coordinate. -/
def observableExpectation
    (ψ : NormalizedState H) (X : ObservableCoordinate H) : ℂ :=
  ⟪X.op ψ.vec, ψ.vec⟫_ℂ

theorem observableExpectation_conj_eq
    (ψ : NormalizedState H) (X : ObservableCoordinate H) :
    starRingEnd ℂ (observableExpectation ψ X) = observableExpectation ψ X := by
  dsimp [observableExpectation]
  calc
    starRingEnd ℂ ⟪X.op ψ.vec, ψ.vec⟫_ℂ =
        ⟪ψ.vec, X.op ψ.vec⟫_ℂ := by
      exact inner_conj_symm (𝕜 := ℂ) ψ.vec (X.op ψ.vec)
    _ = ⟪ψ.vec, (ContinuousLinearMap.adjoint X.op) ψ.vec⟫_ℂ := by
      rw [X.is_self_adjoint]
    _ = ⟪X.op ψ.vec, ψ.vec⟫_ℂ := by
      exact ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) X.op ψ.vec ψ.vec

/-- 
  THEOREM 6 (QGT Decomposition over Observable Coordinates):
  For any state ψ and observable coordinate generators X, Y, the Quantum Geometric Tensor
  canonically splits into the symmetric Fisher-Fubini-Study metric and the antisymmetric
  symplectic Berry curvature.
-/
theorem qgt_observable_coordinate_decomposition
    (ψ : NormalizedState H) (X Y : EndH) :
    (fubiniStudyMetric ψ X Y = (QGT ψ X Y).re) ∧
    (berryCurvature ψ X Y = -2 * (QGT ψ X Y).im) ∧
    (Complex.normSq (QGT ψ X Y) =
       (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2) := by
  refine ⟨rfl, rfl, QGT_normSq_decomposition ψ X Y⟩

theorem typed_observableCoordinate_qgt_decomposition
    (ψ : NormalizedState H)
    (X Y : ObservableCoordinate H) :
    (fubiniStudyMetric ψ X.op Y.op = (QGT ψ X.op Y.op).re) ∧
    (berryCurvature ψ X.op Y.op = -2 * (QGT ψ X.op Y.op).im) ∧
    (Complex.normSq (QGT ψ X.op Y.op) =
      (fubiniStudyMetric ψ X.op Y.op) ^ 2 +
        (1 / 4 : ℝ) * (berryCurvature ψ X.op Y.op) ^ 2) := by
  exact qgt_observable_coordinate_decomposition ψ X.op Y.op

/-- 
  THEOREM 7 (The Universal Uncertainty on Observable Coordinates):
  The metric variance product of two observable coordinates bounds the
  Berry curvature flux from below (Robertson-Schrödinger uncertainty).
-/
theorem observable_coordinate_uncertainty_bound
    (ψ : NormalizedState H) (X Y : EndH) :
    (fubiniStudyMetric ψ X X) * (fubiniStudyMetric ψ Y Y) ≥
      (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 :=
  berry_curvature_uncertainty_bound ψ X Y

/-!
=============================================================================
PART 4: Expectation Coordinates and Modular Flow Velocities
=============================================================================
-/

/-! A supplied normalized fiber-state section and observable-coordinate family
    determine a genuine expectation-value chart on the positive-ray base. -/
def expectationCoordinateMap
    (state : PositiveRay α → NormalizedState H)
    (coordinates : α → ObservableCoordinate H) :
    PositiveRay α → EuclideanSpace ℝ α :=
  fun q => (EuclideanSpace.equiv α ℝ).symm
    (fun i => (observableExpectation (state q) (coordinates i)).re)

omit [Fintype α] [Nonempty α] in
theorem expectationCoordinateMap_apply
    (state : PositiveRay α → NormalizedState H)
    (coordinates : α → ObservableCoordinate H)
    (q : PositiveRay α) (i : α) :
    (expectationCoordinateMap state coordinates q) i =
      (observableExpectation (state q) (coordinates i)).re := by
  rfl

omit [Fintype α] [Nonempty α] in
theorem expectationCoordinateMap_im_eq_zero
    (state : PositiveRay α → NormalizedState H)
    (coordinates : α → ObservableCoordinate H)
    (q : PositiveRay α) (i : α) :
    (observableExpectation (state q) (coordinates i)).im = 0 := by
  have h := observableExpectation_conj_eq (state q) (coordinates i)
  apply Complex.ext_iff.mp at h
  have him : -(observableExpectation (state q) (coordinates i)).im =
      (observableExpectation (state q) (coordinates i)).im := by
    simpa using h.2
  linarith

/-! The modular-flow velocity of an observable is the expectation of its
    commutator with the generator.  The statement is intentionally operator
    valued; no external time parameter or differentiability hypothesis is
    smuggled into this algebraic readout. -/
def modularFlowVelocity
    (ψ : NormalizedState H) (K X : EndH) : ℂ :=
  ⟪(opCommutator K X) ψ.vec, ψ.vec⟫_ℂ

omit [Fintype α] [Nonempty α] in
theorem modularFlowVelocity_eq_expectation_commutator
    (ψ : NormalizedState H) (K X : EndH) :
    modularFlowVelocity ψ K X =
      ⟪(opCommutator K X) ψ.vec, ψ.vec⟫_ℂ := by
  rfl

/-- 🏆 THEOREM: Nonnegativity of the extracted Fubini-Study / Fisher metric:
    g_ψ(X, X) ≥ 0 for any operator generator X. -/
theorem fubiniStudyMetric_nonnegative (ψ : NormalizedState H) (X : EndH) :
    0 ≤ fubiniStudyMetric ψ X X := by
  rw [fubiniStudyMetric_self_eq_normSq]
  exact sq_nonneg ‖projOrth ψ X‖

/-- 🏆 THEOREM: Metric extraction from QGT real part as Riemannian structure:
    g_ψ(X, Y) = Re(Q_ψ(X, Y)). -/
theorem qgt_metric_real_part (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X Y = (QGT ψ X Y).re := rfl

/-- 🏆 THEOREM: Variance of observable coordinate X is the QGT real metric. -/
theorem qgt_real_part_is_variance (ψ : NormalizedState H) (X : EndH) :
    (QGT ψ X X).re = fubiniStudyMetric ψ X X := rfl

end InfoGeometry.Canonical.ErlangenObservableBundle

end noncomputable section

