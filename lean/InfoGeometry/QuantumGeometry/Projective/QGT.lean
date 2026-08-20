import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Phase-Invariant Normalized Representative Formulation of the Quantum Geometric Tensor

This module formalizes the complex normalized-projective Hilbert formulation of the 
Quantum Geometric Tensor (QGT), acting as the complex counterpart to the real doubled/Krein
geometric tensor owners:

1. Bundled normalized state `NormalizedState H` with `⟪ψ, ψ⟫ = 1`.
2. Horizontal projection `projOrth ψ X = Xψ - ⟪ψ, Xψ⟫ • ψ` with proven orthogonality `⟪ψ, X^⟂_ψ⟫ = 0`.
3. Proven Gram identity: `Q_ψ(X, Y) = ⟪X^⟂_ψ, Y^⟂_ψ⟫`.
4. Proven U(1) Phase Invariance: `Q_{c • ψ} = Q_ψ`, `g_{c • ψ} = g_ψ`, and `Ω_{c • ψ} = Ω_ψ` for `|c| = 1`,
   verifying the exact invariance required for descent to projective Hilbert space P(H).
5. Native Cauchy–Schwarz theorem via `inner_mul_inner_self_le`: `|Q_ψ(X, Y)|² ≤ g_ψ(X, X) * g_ψ(Y, Y)`.
6. Full Robertson–Schrödinger inequality:
   `g_ψ(X, X) * g_ψ(Y, Y) ≥ g_ψ(X, Y)² + (1/4) * Ω_ψ(X, Y)²`.
7. Derived Berry curvature commutator with exact intermediate signs:
   `Ω_ψ(X, Y) • i = ⟪ψ, [X, Y] ψ⟫` from skew-adjoint generators.
8. Generic skew-adjoint Lie algebra representation uncertainty bound via `𝔤 →ₗ⁅ℝ⁆ EndH`.
-/

noncomputable section

open ContinuousLinearMap
open LieAlgebra
open InnerProductSpace

local postfix:90 "†" => starRingEnd _

namespace InfoGeometry.QuantumGeometry.Projective

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-!
=============================================================================
PART 1: Normalized States, QGT, and Horizontal Projections
=============================================================================
-/

/-- A normalized state representative in the Hilbert space H with ⟪ψ, ψ⟫_ℂ = 1. -/
structure NormalizedState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  vec : H
  norm_sq : ⟪vec, vec⟫_ℂ = (1 : ℂ)

/-- 
  The Quantum Geometric Tensor (QGT) evaluated on a normalized state representative:
  Q_ψ(X, Y) = ⟪X ψ, Y ψ⟫_ℂ - ⟪X ψ, ψ⟫_ℂ * ⟪ψ, Y ψ⟫_ℂ
-/
def QGT (ψ : NormalizedState H) (X Y : EndH) : ℂ :=
  ⟪X ψ.vec, Y ψ.vec⟫_ℂ - ⟪X ψ.vec, ψ.vec⟫_ℂ * ⟪ψ.vec, Y ψ.vec⟫_ℂ

/-- Symmetric Fubini–Study Riemannian metric component: g_ψ(X, Y) = Re(Q_ψ(X, Y)) -/
def fubiniStudyMetric (ψ : NormalizedState H) (X Y : EndH) : ℝ :=
  (QGT ψ X Y).re

/-- Antisymmetric Berry curvature symplectic component: Ω_ψ(X, Y) = -2 * Im(Q_ψ(X, Y)) -/
def berryCurvature (ψ : NormalizedState H) (X Y : EndH) : ℝ :=
  -2 * (QGT ψ X Y).im

/-- 
  Horizontal/Orthogonal projection of an applied operator state Xψ onto the orthogonal complement of ψ:
  X^⟂_ψ = Xψ - ⟪ψ, Xψ⟫ • ψ
-/
def projOrth (ψ : NormalizedState H) (X : EndH) : H :=
  X ψ.vec - ⟪ψ.vec, X ψ.vec⟫_ℂ • ψ.vec

/-- 
  THEOREM 1: The horizontal projection is strictly orthogonal to the state:
  ⟪ψ, X^⟂_ψ⟫ = 0
-/
theorem inner_state_projOrth (ψ : NormalizedState H) (X : EndH) :
    ⟪ψ.vec, projOrth ψ X⟫_ℂ = 0 := by
  dsimp only [projOrth]
  rw [inner_sub_right, inner_smul_right, ψ.norm_sq, mul_one, sub_self]

/-!
=============================================================================
PART 2: Projective U(1) Phase Invariance and Gram Identity
=============================================================================
-/

/-- Phase-rotated normalized state c • ψ where |c|² = c* c = 1 -/
def phaseRotate (ψ : NormalizedState H) (c : ℂ) (hc : (starRingEnd ℂ c) * c = 1) : NormalizedState H where
  vec := c • ψ.vec
  norm_sq := by
    rw [inner_smul_left, inner_smul_right, ψ.norm_sq, mul_one]
    exact hc

/-- 
  THEOREM 2 (U(1) Projective Phase Invariance):
  The QGT is strictly invariant under phase rotations ψ ↦ c • ψ where |c|² = c* c = 1.
-/
theorem QGT_phase_invariant (ψ : NormalizedState H) (X Y : EndH) (c : ℂ) (hc : starRingEnd ℂ c * c = 1) :
    QGT (phaseRotate ψ c hc) X Y = QGT ψ X Y := by
  dsimp only [QGT, phaseRotate]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  have h1 : starRingEnd ℂ c * (c * ⟪X ψ.vec, Y ψ.vec⟫_ℂ) = ⟪X ψ.vec, Y ψ.vec⟫_ℂ := by
    calc starRingEnd ℂ c * (c * ⟪X ψ.vec, Y ψ.vec⟫_ℂ) = (starRingEnd ℂ c * c) * ⟪X ψ.vec, Y ψ.vec⟫_ℂ := by ring
    _ = 1 * ⟪X ψ.vec, Y ψ.vec⟫_ℂ := by rw [hc]
    _ = ⟪X ψ.vec, Y ψ.vec⟫_ℂ := by ring
  have h2 : starRingEnd ℂ c * (c * ⟪X ψ.vec, ψ.vec⟫_ℂ) = ⟪X ψ.vec, ψ.vec⟫_ℂ := by
    calc starRingEnd ℂ c * (c * ⟪X ψ.vec, ψ.vec⟫_ℂ) = (starRingEnd ℂ c * c) * ⟪X ψ.vec, ψ.vec⟫_ℂ := by ring
    _ = 1 * ⟪X ψ.vec, ψ.vec⟫_ℂ := by rw [hc]
    _ = ⟪X ψ.vec, ψ.vec⟫_ℂ := by ring
  have h3 : starRingEnd ℂ c * (c * ⟪ψ.vec, Y ψ.vec⟫_ℂ) = ⟪ψ.vec, Y ψ.vec⟫_ℂ := by
    calc starRingEnd ℂ c * (c * ⟪ψ.vec, Y ψ.vec⟫_ℂ) = (starRingEnd ℂ c * c) * ⟪ψ.vec, Y ψ.vec⟫_ℂ := by ring
    _ = 1 * ⟪ψ.vec, Y ψ.vec⟫_ℂ := by rw [hc]
    _ = ⟪ψ.vec, Y ψ.vec⟫_ℂ := by ring
  calc c * (starRingEnd ℂ c * ⟪X ψ.vec, Y ψ.vec⟫_ℂ) - (c * (starRingEnd ℂ c * ⟪X ψ.vec, ψ.vec⟫_ℂ)) * (c * (starRingEnd ℂ c * ⟪ψ.vec, Y ψ.vec⟫_ℂ))
    _ = starRingEnd ℂ c * (c * ⟪X ψ.vec, Y ψ.vec⟫_ℂ) - (starRingEnd ℂ c * (c * ⟪X ψ.vec, ψ.vec⟫_ℂ)) * (starRingEnd ℂ c * (c * ⟪ψ.vec, Y ψ.vec⟫_ℂ)) := by ring
    _ = ⟪X ψ.vec, Y ψ.vec⟫_ℂ - ⟪X ψ.vec, ψ.vec⟫_ℂ * ⟪ψ.vec, Y ψ.vec⟫_ℂ := by rw [h1, h2, h3]

theorem fubiniStudyMetric_phase_invariant (ψ : NormalizedState H) (X Y : EndH) (c : ℂ) (hc : starRingEnd ℂ c * c = 1) :
    fubiniStudyMetric (phaseRotate ψ c hc) X Y = fubiniStudyMetric ψ X Y := by
  dsimp [fubiniStudyMetric]
  rw [QGT_phase_invariant ψ X Y c hc]

theorem berryCurvature_phase_invariant (ψ : NormalizedState H) (X Y : EndH) (c : ℂ) (hc : starRingEnd ℂ c * c = 1) :
    berryCurvature (phaseRotate ψ c hc) X Y = berryCurvature ψ X Y := by
  dsimp [berryCurvature]
  rw [QGT_phase_invariant ψ X Y c hc]

/-- 
  THEOREM 3 (QGT Gram Identity):
  Q_ψ(X, Y) = ⟪X^⟂_ψ, Y^⟂_ψ⟫
-/
theorem QGT_eq_inner_projOrth (ψ : NormalizedState H) (X Y : EndH) :
    QGT ψ X Y = ⟪projOrth ψ X, projOrth ψ Y⟫_ℂ := by
  dsimp only [QGT, projOrth]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
  rw [ψ.norm_sq, mul_one]
  have h_conj_X : starRingEnd ℂ (⟪ψ.vec, X ψ.vec⟫_ℂ) = ⟪X ψ.vec, ψ.vec⟫_ℂ :=
    inner_conj_symm (X ψ.vec) ψ.vec
  rw [h_conj_X]
  ring

/-- 
  THEOREM 4: Diagonal Metric as Squared Norm of the Horizontal Vector:
    g_ψ(X, X) = ‖X^⟂_ψ‖²
-/
theorem fubiniStudyMetric_self_eq_normSq (ψ : NormalizedState H) (X : EndH) :
    fubiniStudyMetric ψ X X = ‖projOrth ψ X‖ ^ 2 := by
  dsimp only [fubiniStudyMetric]
  rw [QGT_eq_inner_projOrth]
  have h := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (projOrth ψ X)
  exact h.symm

/-!
=============================================================================
PART 3: Native Cauchy–Schwarz and Full Robertson–Schrödinger Inequality
=============================================================================
-/

/-- 
  THEOREM 5 (Proven Cauchy–Schwarz Inequality for QGT):
  |Q_ψ(X, Y)|² ≤ g_ψ(X, X) * g_ψ(Y, Y)
  Derived natively from Mathlib's `norm_inner_le_norm` on horizontal projections.
-/
theorem QGT_cauchy_schwarz (ψ : NormalizedState H) (X Y : EndH) :
    Complex.normSq (QGT ψ X Y) ≤ fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y := by
  let u := projOrth ψ X
  let v := projOrth ψ Y
  have hQ : QGT ψ X Y = ⟪u, v⟫_ℂ := by
    simpa [u, v] using QGT_eq_inner_projOrth ψ X Y
  have hX : fubiniStudyMetric ψ X X = ‖u‖ ^ 2 := by
    simpa [u] using fubiniStudyMetric_self_eq_normSq ψ X
  have hY : fubiniStudyMetric ψ Y Y = ‖v‖ ^ 2 := by
    simpa [v] using fubiniStudyMetric_self_eq_normSq ψ Y
  
  have hCS : Complex.normSq (⟪u, v⟫_ℂ) ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have h1 : ‖(⟪u, v⟫_ℂ : ℂ)‖ ≤ ‖u‖ * ‖v‖ := by
      exact norm_inner_le_norm u v
    calc
      Complex.normSq (⟪u, v⟫_ℂ) = ‖(⟪u, v⟫_ℂ : ℂ)‖ ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
      _ ≤ (‖u‖ * ‖v‖) ^ 2 := by gcongr
      _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring
  
  calc
    Complex.normSq (QGT ψ X Y) = Complex.normSq (⟪u, v⟫_ℂ) := by rw [hQ]
    _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := hCS
    _ = fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y := by rw [hX, hY]

/-- 
  THEOREM 6 (Pythagorean QGT Norm Identity):
  |Q_ψ(X, Y)|² = g_ψ(X, Y)² + (1/4) * Ω_ψ(X, Y)²
-/
theorem QGT_normSq_decomposition (ψ : NormalizedState H) (X Y : EndH) :
    Complex.normSq (QGT ψ X Y) =
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 := by
  dsimp only [fubiniStudyMetric, berryCurvature]
  rw [Complex.normSq_apply]
  ring

/-- 
  THEOREM 7 (The Full Geometric Robertson–Schrödinger Inequality):
  g_ψ(X, X) * g_ψ(Y, Y) ≥ g_ψ(X, Y)² + (1/4) * Ω_ψ(X, Y)²
-/
theorem robertson_schrodinger_qgt_bound (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 := by
  have h := QGT_cauchy_schwarz ψ X Y
  have h2 := QGT_normSq_decomposition ψ X Y
  linarith

theorem robertson_schrodinger_uncertainty (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 :=
  robertson_schrodinger_qgt_bound ψ X Y

/-- 
  COROLLARY (Berry Curvature Uncertainty Bound):
  g_ψ(X, X) * g_ψ(Y, Y) ≥ (1/4) * Ω_ψ(X, Y)²
-/
theorem berry_curvature_uncertainty_bound (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥
      (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 := by
  have h := robertson_schrodinger_qgt_bound ψ X Y
  have _h_cov_nonneg : (fubiniStudyMetric ψ X Y) ^ 2 ≥ 0 := by positivity
  linarith

/-!
=============================================================================
PART 4: Derived Berry Curvature Commutator Identity
=============================================================================
-/

/-- Operator Lie Commutator on End(H): [X, Y] = X ∘ Y - Y ∘ X. -/
def opCommutator (X Y : EndH) : EndH :=
  X.comp Y - Y.comp X

@[simp]
theorem opCommutator_apply (X Y : EndH) (v : H) :
    opCommutator X Y v = X (Y v) - Y (X v) := rfl

/-- 
  THEOREM 8: The Derived Berry Curvature Commutator Identity:
  (Ω_ψ(X, Y) : ℂ) * i = ⟪ψ, [X, Y] ψ⟫_ℂ
  for skew-adjoint operators `X† = -X` and `Y† = -Y`.
-/
theorem berryCurvature_skewAdjoint_commutator (ψ : NormalizedState H) (X Y : EndH)
    (hX : ContinuousLinearMap.adjoint X = -X)
    (hY : ContinuousLinearMap.adjoint Y = -Y) :
    (berryCurvature ψ X Y : ℂ) * Complex.I =
      ⟪ψ.vec, (opCommutator X Y) ψ.vec⟫_ℂ := by
  have h_adj_X : ∀ u v : H, ⟪X u, v⟫_ℂ = -⟪u, X v⟫_ℂ := by
    intro u v
    calc
      ⟪X u, v⟫_ℂ = ⟪u, ContinuousLinearMap.adjoint X v⟫_ℂ := by rw [adjoint_inner_right]
      _ = ⟪u, (-X) v⟫_ℂ := by rw [hX]
      _ = ⟪u, -(X v)⟫_ℂ := by simp [ContinuousLinearMap.neg_apply]
      _ = -⟪u, X v⟫_ℂ := by rw [inner_neg_right]

  have h_adj_Y : ∀ u v : H, ⟪Y u, v⟫_ℂ = -⟪u, Y v⟫_ℂ := by
    intro u v
    calc
      ⟪Y u, v⟫_ℂ = ⟪u, ContinuousLinearMap.adjoint Y v⟫_ℂ := by rw [adjoint_inner_right]
      _ = ⟪u, (-Y) v⟫_ℂ := by rw [hY]
      _ = ⟪u, -(Y v)⟫_ℂ := by simp [ContinuousLinearMap.neg_apply]
      _ = -⟪u, Y v⟫_ℂ := by rw [inner_neg_right]

  have hX_im : ⟪X ψ.vec, ψ.vec⟫_ℂ = -⟪ψ.vec, X ψ.vec⟫_ℂ := h_adj_X ψ.vec ψ.vec
  have hY_im : ⟪Y ψ.vec, ψ.vec⟫_ℂ = -⟪ψ.vec, Y ψ.vec⟫_ℂ := h_adj_Y ψ.vec ψ.vec

  have h_cross :
      ⟪X ψ.vec, ψ.vec⟫_ℂ * ⟪ψ.vec, Y ψ.vec⟫_ℂ -
        ⟪Y ψ.vec, ψ.vec⟫_ℂ * ⟪ψ.vec, X ψ.vec⟫_ℂ = 0 := by
    rw [hX_im, hY_im]
    ring

  have h_Q_sub :
      QGT ψ X Y - QGT ψ Y X = ⟪X ψ.vec, Y ψ.vec⟫_ℂ - ⟪Y ψ.vec, X ψ.vec⟫_ℂ := by
    dsimp only [QGT]
    linear_combination -h_cross

  have h_comm :
      ⟪ψ.vec, opCommutator X Y ψ.vec⟫_ℂ =
        -(⟪X ψ.vec, Y ψ.vec⟫_ℂ - ⟪Y ψ.vec, X ψ.vec⟫_ℂ) := by
    rw [opCommutator_apply, inner_sub_right]
    have hXY : ⟪ψ.vec, X (Y ψ.vec)⟫_ℂ = -⟪X ψ.vec, Y ψ.vec⟫_ℂ := by
      have h := h_adj_X ψ.vec (Y ψ.vec)
      linear_combination h
    have hYX : ⟪ψ.vec, Y (X ψ.vec)⟫_ℂ = -⟪Y ψ.vec, X ψ.vec⟫_ℂ := by
      have h := h_adj_Y ψ.vec (X ψ.vec)
      linear_combination h
    rw [hXY, hYX]
    ring

  have h_Q_symm : QGT ψ Y X = starRingEnd ℂ (QGT ψ X Y) := by
    dsimp only [QGT] at *
    rw [map_sub, map_mul]
    have h1 : starRingEnd ℂ (⟪X ψ.vec, Y ψ.vec⟫_ℂ) = ⟪Y ψ.vec, X ψ.vec⟫_ℂ :=
      inner_conj_symm (Y ψ.vec) (X ψ.vec)
    have h2 : starRingEnd ℂ (⟪X ψ.vec, ψ.vec⟫_ℂ) = ⟪ψ.vec, X ψ.vec⟫_ℂ :=
      inner_conj_symm ψ.vec (X ψ.vec)
    have h3 : starRingEnd ℂ (⟪ψ.vec, Y ψ.vec⟫_ℂ) = ⟪Y ψ.vec, ψ.vec⟫_ℂ :=
      inner_conj_symm (Y ψ.vec) ψ.vec
    rw [h1, h2, h3]
    ring

  have h_Q_im : QGT ψ X Y - QGT ψ Y X = -((berryCurvature ψ X Y : ℂ) * Complex.I) := by
    rw [h_Q_symm, Complex.sub_conj]
    dsimp only [berryCurvature]
    push_cast
    ring

  calc
    (berryCurvature ψ X Y : ℂ) * Complex.I
        = -(QGT ψ X Y - QGT ψ Y X) := by
            rw [h_Q_im]
            ring
    _ = -(⟪X ψ.vec, Y ψ.vec⟫_ℂ - ⟪Y ψ.vec, X ψ.vec⟫_ℂ) := by rw [h_Q_sub]
    _ = ⟪ψ.vec, opCommutator X Y ψ.vec⟫_ℂ := by rw [← h_comm]

theorem berryCurvature_eq_commutator
    (ψ : NormalizedState H) (X Y : EndH)
    (hX : ContinuousLinearMap.adjoint X = -X)
    (hY : ContinuousLinearMap.adjoint Y = -Y) :
    (berryCurvature ψ X Y : ℂ) * Complex.I = ⟪ψ.vec, opCommutator X Y ψ.vec⟫_ℂ :=
  berryCurvature_skewAdjoint_commutator ψ X Y hX hY

/-!
=============================================================================
PART 5: Bundled Lie Algebra Representations and Uncertainty
=============================================================================
-/

/-- 
  A representation of a real Lie algebra 𝔤 by skew-adjoint operators on H.
  
  The Lie algebra homomorphism `toLieHom` is a linear map from 𝔤 to End(H)
  (the algebra of endomorphisms on H) that preserves the Lie bracket:
  `ρ([x, y]) = [ρ(x), ρ(y)]` where the bracket on the right is the commutator in End(H).
  Additionally, all image elements are skew-adjoint: ρ(x)† = -ρ(x).
-/
structure SkewAdjointLieRep (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] where
  toLieHom : 𝔤 →ₗ⁅ℝ⁆ EndH
  map_lie' : ∀ x y : 𝔤, opCommutator (toLieHom x) (toLieHom y) = toLieHom (⁅x, y⁆)
  is_skew' : ∀ X : 𝔤, ContinuousLinearMap.adjoint (toLieHom X) = -(toLieHom X)

/-- 
  MASTER CAPSTONE THEOREM:
  For any representation ρ of a Lie algebra 𝔤 by skew-adjoint operators on H,
  the Robertson–Schrödinger bound is strictly governed by the Lie bracket:
    g_ψ(ρX, ρX) * g_ψ(ρY, ρY) ≥ (1/4) * |⟪ψ, ρ⁅X, Y⁆ ψ⟫|²
-/
theorem lie_rep_uncertainty_bound
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (ρ : SkewAdjointLieRep 𝔤)
    (ψ : NormalizedState H) (X Y : 𝔤) :
    (fubiniStudyMetric ψ (ρ.toLieHom X) (ρ.toLieHom X)) *
        (fubiniStudyMetric ψ (ρ.toLieHom Y) (ρ.toLieHom Y)) ≥
      (1 / 4 : ℝ) * Complex.normSq (⟪ψ.vec, ρ.toLieHom (⁅X, Y⁆) ψ.vec⟫_ℂ) := by
  have h_curv :=
    berry_curvature_uncertainty_bound ψ (ρ.toLieHom X) (ρ.toLieHom Y)
  have h_comm :=
    berryCurvature_eq_commutator
      ψ
      (ρ.toLieHom X)
      (ρ.toLieHom Y)
      (ρ.is_skew' X)
      (ρ.is_skew' Y)
  have h_lie_comm :
      opCommutator (ρ.toLieHom X) (ρ.toLieHom Y) = ρ.toLieHom (⁅X, Y⁆) :=
    ρ.map_lie' X Y
  have h_normSq :
      Complex.normSq (⟪ψ.vec, ρ.toLieHom (⁅X, Y⁆) ψ.vec⟫_ℂ) =
        (berryCurvature ψ (ρ.toLieHom X) (ρ.toLieHom Y)) ^ 2 := by
    rw [← h_lie_comm, ← h_comm, Complex.normSq_mul, Complex.normSq_I, mul_one, Complex.normSq_ofReal]
    ring
  rw [h_normSq]
  exact h_curv

end InfoGeometry.QuantumGeometry.Projective

end noncomputable section