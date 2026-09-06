import Mathlib

noncomputable section

namespace InfoGeometry.Canonical.ZetaCoordinateSymmetry

open Set

/-- Involution on the critical strip coordinate `σ` implementing `σ ↦ 1 - σ`. -/
def kritCoordInvolution (σ : ℝ) : ℝ := 1 - σ

theorem involution_involutive (σ : ℝ) :
    kritCoordInvolution (kritCoordInvolution σ) = σ := by
  simp [kritCoordInvolution]

/-- The critical axis as the fixed point of the reflection `σ ↦ 1 - σ`. -/
def criticalAxis : ℝ := 1 / 2

lemma fixed_point_iff (σ : ℝ) : kritCoordInvolution σ = σ ↔ σ = criticalAxis := by
  constructor
  · intro h
    have h' : (1 : ℝ) - σ = σ := by simpa [kritCoordInvolution] using h
    have h'' : σ = (1 : ℝ) / 2 := by nlinarith [h']
    simpa [criticalAxis] using h''
  · intro h
    rw [h, kritCoordInvolution, criticalAxis]
    norm_num

/-- Strict convexity + reflection symmetry force the axis to be the strict global minimizer. -/
theorem stability_implies_axis_lock (f : ℝ → ℝ)
    (hConvex : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) f)
    (hSymm : ∀ σ ∈ Ioo (0 : ℝ) 1, f (kritCoordInvolution σ) = f σ)
    (σ : ℝ) (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ_ne : σ ≠ criticalAxis) :
    f criticalAxis < f σ := by
  have hσ' : kritCoordInvolution σ ∈ Ioo (0 : ℝ) 1 := by
    rcases hσ with ⟨h0, h1⟩
    constructor
    · dsimp [kritCoordInvolution]
      exact sub_pos.mpr h1
    · dsimp [kritCoordInvolution]
      linarith
  have hne : σ ≠ kritCoordInvolution σ := by
    intro h
    exact hσ_ne ((fixed_point_iff σ).1 h.symm)
  have hStrict :
      f ((1 / 2 : ℝ) * σ + (1 / 2 : ℝ) * kritCoordInvolution σ)
        < (1 / 2 : ℝ) * f σ + (1 / 2 : ℝ) * f (kritCoordInvolution σ) :=
    hConvex.2 hσ hσ' hne (by norm_num) (by norm_num) (by ring)
  have hComb :
      (1 / 2 : ℝ) * σ + (1 / 2 : ℝ) * kritCoordInvolution σ = criticalAxis := by
    simp [kritCoordInvolution, criticalAxis]
    ring
  rw [hComb] at hStrict
  rw [hSymm σ hσ] at hStrict
  have havg : (1 / 2 : ℝ) * f σ + (1 / 2 : ℝ) * f σ = f σ := by
    ring
  rw [havg] at hStrict
  exact hStrict

end InfoGeometry.Canonical.ZetaCoordinateSymmetry
