/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ComplexTimeConjugation
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Topology.Order.Compact

/-!
# Bounded complex-time correlations on an existing C⋆ algebra

The observable orbit is the existing noncommutative exponential conjugation.
Scalar correlations are continuous-linear readouts of that orbit.  A proved
twisted identity and a proved density/exponential identification give the KMS
upper boundary.  The concrete finite-seed consumer supplies both proofs.

The closed-strip bound follows from real-time unitarity and compactness of the
imaginary-time interval; it is uniform in the unbounded real-time coordinate.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexTimeCorrelation

open ComplexTimeConjugation

variable {C : Type*} [CStarAlgebra C]

/-- Correlation of two actual observables under complex-time conjugation. -/
def correlation (φ : C →L[ℂ] ℂ) (G A B : C) (z : ℂ) : ℂ :=
  φ (A * alpha G z B)

theorem correlation_analyticAt (φ : C →L[ℂ] ℂ) (G A B : C) (z : ℂ) :
    AnalyticAt ℂ (correlation φ G A B) z := by
  have hmul : AnalyticAt ℂ (fun w : ℂ => A * alpha G w B) z :=
    (analyticAt_const (v := A) (x := z)).mul (alpha_analyticAt G B z)
  exact (φ.analyticAt (A * alpha G z B)).comp
    (f := fun w : ℂ => A * alpha G w B) hmul

theorem correlation_continuous (φ : C →L[ℂ] ℂ) (G A B : C) :
    Continuous (correlation φ G A B) :=
  continuous_iff_continuousAt.mpr fun z =>
    (correlation_analyticAt φ G A B z).continuousAt

theorem correlation_continuousOn_closedStrip
    (φ : C →L[ℂ] ℂ) (G A B : C) (β : ℝ) :
    ContinuousOn (correlation φ G A B) {z : ℂ | z.im ∈ Set.Icc 0 β} :=
  (correlation_continuous φ G A B).continuousOn

theorem correlation_differentiableOn_openStrip
    (φ : C →L[ℂ] ℂ) (G A B : C) (β : ℝ) :
    DifferentiableOn ℂ (correlation φ G A B)
      {z : ℂ | z.im ∈ Set.Ioo 0 β} := by
  intro z _
  exact (correlation_analyticAt φ G A B z).differentiableAt.differentiableWithinAt

theorem correlation_real_boundary
    (φ : C →L[ℂ] ℂ) (G : selfAdjoint C) (A B : C) (t : ℝ) :
    correlation φ (G : C) A B (t : ℂ) =
      φ (A * Unitary.conjStarAlgAut (S := ℂ) (R := C)
        (selfAdjoint.expUnitary (t • G)) B) := by
  rw [correlation, alpha_ofReal_eq_unitary]

/-- The upper boundary is derived from twisted cyclicity, with product order
fixed by `F(A,B,z) = φ(A * α(z,B))`. -/
theorem correlation_upper_boundary_of_twisted
    (φ : C →L[ℂ] ℂ) (G : C) (δ : Cˣ) (β : ℝ)
    (hδ : (δ : C) = NormedSpace.exp ((-β) • G))
    (hδinv : (↑δ⁻¹ : C) = NormedSpace.exp (β • G))
    (htwist : ∀ X Y : C,
      φ (X * Y) = φ (Y * ((δ : C) * X * (↑δ⁻¹ : C))))
    (A B : C) (t : ℝ) :
    correlation φ G A B ((t : ℂ) + Complex.I * (β : ℂ)) =
      φ (alpha G (t : ℂ) B * A) := by
  rw [correlation, alpha_add_imaginary, ← hδ, ← hδinv]
  exact (htwist (alpha G (t : ℂ) B) A).symm

theorem norm_alpha_ofReal (G : selfAdjoint C) (B : C) (t : ℝ) :
    ‖alpha (G : C) (t : ℂ) B‖ = ‖B‖ := by
  rw [alpha_ofReal_eq_unitary]
  exact StarAlgEquiv.norm_map _ B

/-- Only the imaginary coordinate affects the norm of the orbit. -/
theorem norm_alpha_eq_imaginary (G : selfAdjoint C) (B : C) (z : ℂ) :
    ‖alpha (G : C) z B‖ =
      ‖alpha (G : C) (Complex.I * (z.im : ℂ)) B‖ := by
  have hz : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
    rw [mul_comm Complex.I, Complex.re_add_im]
  calc
    ‖alpha (G : C) z B‖ =
        ‖alpha (G : C) ((z.re : ℂ) + Complex.I * (z.im : ℂ)) B‖ :=
      congrArg (fun w : ℂ => ‖alpha (G : C) w B‖) hz
    _ = ‖alpha (G : C) (z.re : ℂ)
        (alpha (G : C) (Complex.I * (z.im : ℂ)) B)‖ := by rw [alpha_add]
    _ = ‖alpha (G : C) (Complex.I * (z.im : ℂ)) B‖ :=
      norm_alpha_ofReal G _ z.re

/-- A uniform bound on the entire closed strip, including its unbounded
real-time direction.  This also holds for an empty strip. -/
theorem correlation_bounded_closedStrip
    (φ : C →L[ℂ] ℂ) (G : selfAdjoint C) (A B : C) (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℂ, z.im ∈ Set.Icc 0 β →
        ‖correlation φ (G : C) A B z‖ ≤ M := by
  have ha : Continuous (fun z : ℂ => alpha (G : C) z B) :=
    continuous_iff_continuousAt.mpr fun z =>
      (alpha_analyticAt (G : C) B z).continuousAt
  have hq : Continuous (fun s : ℝ =>
      ‖alpha (G : C) (Complex.I * (s : ℂ)) B‖) :=
    (ha.comp (continuous_const.mul Complex.continuous_ofReal)).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) β)).bddAbove_image
    hq.continuousOn
  refine ⟨‖φ‖ * (‖A‖ * max M 0),
    mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_max_right _ _)), ?_⟩
  intro z hz
  calc
    ‖correlation φ (G : C) A B z‖ ≤
        ‖φ‖ * ‖A * alpha (G : C) z B‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (‖A‖ * ‖alpha (G : C) z B‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖φ‖ * (‖A‖ * ‖alpha (G : C) (Complex.I * (z.im : ℂ)) B‖) := by
      rw [norm_alpha_eq_imaginary]
    _ ≤ ‖φ‖ * (‖A‖ * max M 0) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (hM ⟨z.im, hz, rfl⟩).trans (le_max_left M 0)

end InfoGeometry.OperatorAlgebra.ComplexTimeCorrelation
