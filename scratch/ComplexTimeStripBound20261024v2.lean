/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ComplexTimeConjugation
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Topology.Order.Compact

/-! Uniform closed-strip bounds for the existing complex-time conjugation.
Uncompiled sandbox; the complex-time substrate is pending independent kernel QA.
No state, positivity, or KMS boundary is assumed or constructed.
-/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.ComplexTimeConjugation

variable {A : Type*} [CStarAlgebra A]

/-- The imaginary-axis orbit is continuous, by the derived entire orbit. -/
theorem continuous_alpha_imaginary (G X : A) :
    Continuous (fun s : ℝ => alpha G (Complex.I * (s : ℂ)) X) := by
  have hc : Continuous (fun z : ℂ => alpha G z X) :=
    continuous_iff_continuousAt.mpr fun z => (alpha_analyticAt G X z).continuousAt
  exact hc.comp (continuous_const.mul Complex.continuous_ofReal)

/-- Real time preserves the norm because its native conjugation is unitary. -/
theorem norm_alpha_ofReal (G : selfAdjoint A) (X : A) (t : ℝ) :
    ‖alpha (G : A) (t : ℂ) X‖ = ‖X‖ := by
  rw [alpha_ofReal_eq_unitary]
  exact StarAlgEquiv.norm_map
    (Unitary.conjStarAlgAut (S := ℂ) (R := A)
      (selfAdjoint.expUnitary (t • G))) X

/-- All real parts of a fixed complex-time height have the same orbit norm. -/
theorem norm_alpha_eq_imaginary (G : selfAdjoint A) (X : A) (z : ℂ) :
    ‖alpha (G : A) z X‖ =
      ‖alpha (G : A) (Complex.I * (z.im : ℂ)) X‖ := by
  have hz : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
    apply Complex.ext <;> simp
  calc
    ‖alpha (G : A) z X‖ =
        ‖alpha (G : A) ((z.re : ℂ) + Complex.I * (z.im : ℂ)) X‖ :=
      congrArg (fun w : ℂ => ‖alpha (G : A) w X‖) hz
    _ = ‖alpha (G : A) (Complex.I * (z.im : ℂ)) X‖ := by
      rw [alpha_add, norm_alpha_ofReal]

/-- Compact imaginary time gives a nonnegative uniform bound on the whole strip. -/
theorem exists_norm_alpha_le_closedStrip (G : selfAdjoint A) (X : A)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.im → z.im ≤ β →
      ‖alpha (G : A) z X‖ ≤ C := by
  have hc := (continuous_alpha_imaginary (G : A) X).norm
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) β)).bddAbove_image hc.continuousOn
  have hbound (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) β) :
      ‖alpha (G : A) (Complex.I * (s : ℂ)) X‖ ≤ C :=
    hC (Set.mem_image_of_mem _ hs)
  refine ⟨C, (norm_nonneg _).trans (hbound 0 ⟨le_rfl, hβ⟩), ?_⟩
  intro z hz0 hzβ
  rw [norm_alpha_eq_imaginary]
  exact hbound z.im ⟨hz0, hzβ⟩

/-- Every continuous linear scalar readout is uniformly bounded on the closed strip.
This is a bound for the actual orbit, not an assumed analytic KMS certificate. -/
theorem exists_scalar_alpha_le_closedStrip (G : selfAdjoint A)
    (φ : A →L[ℂ] ℂ) (X Y : A) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 ≤ z.im → z.im ≤ β →
      ‖φ (Y * alpha (G : A) z X)‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_alpha_le_closedStrip G X β hβ
  refine ⟨‖φ‖ * (‖Y‖ * C),
    mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC0), ?_⟩
  intro z hz0 hzβ
  exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (hC z hz0 hzβ) (norm_nonneg Y)))
    (norm_nonneg φ))

end InfoGeometry.OperatorAlgebra.ComplexTimeConjugation
