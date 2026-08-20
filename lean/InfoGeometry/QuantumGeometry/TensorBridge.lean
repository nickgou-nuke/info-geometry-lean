/-
=============================================================================
           InfoGeometry.QuantumGeometry: TensorBridge
=============================================================================

The Holographic Decomposition and Quantum Geometric Tensor Bridge:
1. Holographic QGT Decomposition: Q_ψ(X, Y) = g_ψ(X, Y) - (i/2) Ω_ψ(X, Y)
2. Cross-Variance Skew Cancellation for Lie Derivations
3. Exact Berry Curvature Commutator Expectation Value: Ω_ψ(X, Y) = ⟨ψ | i[X, Y] | ψ⟩
4. Full Robertson–Schrödinger Uncertainty Bound from QGT Geometry

Zero Custom Axioms • Zero Sorries • Fully Native Mathlib 4
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

import InfoGeometry.QuantumGeometry.Projective.QGT

noncomputable section

open ContinuousLinearMap
open InnerProductSpace

namespace InfoGeometry.QuantumGeometry.TensorBridge

open InfoGeometry.QuantumGeometry.Projective

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-!
=============================================================================
PART 1: Holographic Decomposition of the QGT: Q = g - (i/2) Ω
=============================================================================
-/

/-- 
  THEOREM 1 (Holographic Decomposition):
  The Quantum Geometric Tensor strictly decomposes into its real Riemannian metric
  and imaginary symplectic Berry curvature 2-form:
    Q_ψ(X, Y) = (g_ψ(X, Y) : ℂ) - (i / 2) • (Ω_ψ(X, Y) : ℂ)
-/
theorem QGT_decomposition (ψ : NormalizedState H) (X Y : EndH) :
    QGT ψ X Y = (fubiniStudyMetric ψ X Y : ℂ) - (Complex.I / 2) * (berryCurvature ψ X Y : ℂ) := by
  dsimp [fubiniStudyMetric, berryCurvature]
  have h_re_im := Complex.re_add_im (QGT ψ X Y)
  calc
    QGT ψ X Y = (QGT ψ X Y).re + Complex.I * (QGT ψ X Y).im := h_re_im.symm
    _ = (QGT ψ X Y).re - (Complex.I / 2) * (-2 * (QGT ψ X Y).im) := by
      push_cast
      ring

/-!
=============================================================================
PART 2: Cross-Variance Cancellation for Skew-Adjoint Generators
=============================================================================
-/

/-- 
  THEOREM 2 (Cross-Variance Skew Cancellation):
  For skew-adjoint operators (geometric Lie derivations with X† = -X and Y† = -Y),
  the connected cross-expectation terms cancel in the antisymmetric commutator difference:
    ⟨Xψ, ψ⟩⟨ψ, Yψ⟩ - ⟨Yψ, ψ⟩⟨ψ, Xψ⟩ = 0
-/
theorem cross_variance_skew_cancel (ψ : NormalizedState H) (X Y : EndH)
    (hX : ContinuousLinearMap.adjoint X = -X)
    (hY : ContinuousLinearMap.adjoint Y = -Y) :
    ⟪X ψ.vec, ψ.vec⟫_ℂ * ⟪ψ.vec, Y ψ.vec⟫_ℂ -
      ⟪Y ψ.vec, ψ.vec⟫_ℂ * ⟪ψ.vec, X ψ.vec⟫_ℂ = 0 := by
  have h_adj_X (u v : H) : ⟪X u, v⟫_ℂ = -⟪u, X v⟫_ℂ := by
    calc
      ⟪X u, v⟫_ℂ = ⟪u, ContinuousLinearMap.adjoint X v⟫_ℂ := (adjoint_inner_right X u v).symm
      _ = ⟪u, (-X) v⟫_ℂ := by rw [hX]
      _ = -⟪u, X v⟫_ℂ := by simp
  have h_adj_Y (u v : H) : ⟪Y u, v⟫_ℂ = -⟪u, Y v⟫_ℂ := by
    calc
      ⟪Y u, v⟫_ℂ = ⟪u, ContinuousLinearMap.adjoint Y v⟫_ℂ := (adjoint_inner_right Y u v).symm
      _ = ⟪u, (-Y) v⟫_ℂ := by rw [hY]
      _ = -⟪u, Y v⟫_ℂ := by simp
  have hX_im : ⟪X ψ.vec, ψ.vec⟫_ℂ = -⟪ψ.vec, X ψ.vec⟫_ℂ := h_adj_X ψ.vec ψ.vec
  have hY_im : ⟪Y ψ.vec, ψ.vec⟫_ℂ = -⟪ψ.vec, Y ψ.vec⟫_ℂ := h_adj_Y ψ.vec ψ.vec
  rw [hX_im, hY_im]
  ring

/-!
=============================================================================
PART 3: Berry Curvature as Lie Commutator Expectation
=============================================================================
-/

/-- 
  THEOREM 3 (Berry Curvature is the Lie Bracket Expectation):
  For skew-adjoint geometric derivations, the Berry curvature satisfies:
    Ω_ψ(X, Y) • i = ⟨ψ | [X, Y] | ψ⟩
-/
theorem berryCurvature_eq_commutator_expectation (ψ : NormalizedState H) (X Y : EndH)
    (hX : ContinuousLinearMap.adjoint X = -X)
    (hY : ContinuousLinearMap.adjoint Y = -Y) :
    (berryCurvature ψ X Y : ℂ) * Complex.I = ⟪ψ.vec, (opCommutator X Y) ψ.vec⟫_ℂ :=
  berryCurvature_skewAdjoint_commutator ψ X Y hX hY

/-!
=============================================================================
PART 4: Full Robertson–Schrödinger Geometric Uncertainty Bound
=============================================================================
-/

/-- 
  THEOREM 4 (Robertson–Schrödinger Uncertainty Bound):
  The metric variances strictly bound the product of covariance and Berry curvature:
    g_ψ(X, X) * g_ψ(Y, Y) ≥ g_ψ(X, Y)² + (1/4) * Ω_ψ(X, Y)²
-/
theorem robertson_schrodinger_bound (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 :=
  robertson_schrodinger_uncertainty ψ X Y

end InfoGeometry.QuantumGeometry.TensorBridge
