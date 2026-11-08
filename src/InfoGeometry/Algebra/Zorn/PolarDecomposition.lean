import InfoGeometry.Algebra.Zorn.InverseAdjugate
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Positive-norm polar normalization for concrete split Zorn cells

The split norm is indefinite, so there is no global positive polar
decomposition.  On the positive determinant locus, however, a Zorn cell has
the canonical scalar normalization by `sqrt (detZ X)` used below.
-/

namespace InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

noncomputable section

def polarRadius (X : ZornCell ℝ) : ℝ := Real.sqrt (detZ X)

def polarUnit (X : ZornCell ℝ) : ZornCell ℝ :=
  scaleZ (polarRadius X)⁻¹ X

theorem detZ_scaleZ_real (c : ℝ) (X : ZornCell ℝ) :
    detZ (scaleZ c X) = c ^ 2 * detZ X := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  unfold detZ scaleZ
  ring

theorem polarRadius_sq (X : ZornCell ℝ) (hX : 0 < detZ X) :
    polarRadius X ^ 2 = detZ X := by
  unfold polarRadius
  exact Real.sq_sqrt (le_of_lt hX)

theorem polarRadius_scaleZ (c : ℝ) (hc : 0 ≤ c) (X : ZornCell ℝ) :
    polarRadius (scaleZ c X) = c * polarRadius X := by
  unfold polarRadius
  rw [detZ_scaleZ_real]
  calc
    Real.sqrt (c ^ 2 * detZ X) = Real.sqrt (c ^ 2) * Real.sqrt (detZ X) := by
      exact Real.sqrt_mul (sq_nonneg c) (detZ X)
    _ = c * Real.sqrt (detZ X) := by
      rw [Real.sqrt_sq hc]

theorem detZ_polarUnit (X : ZornCell ℝ) (hX : 0 < detZ X) :
    detZ (polarUnit X) = 1 := by
  rw [polarUnit, detZ_scaleZ_real]
  have hsqrt : 0 < polarRadius X := by
    exact Real.sqrt_pos.2 hX
  field_simp [ne_of_gt hsqrt]
  exact (polarRadius_sq X hX).symm

theorem polarUnit_scaleZ (c : ℝ) (hc : 0 < c) (X : ZornCell ℝ) :
    polarUnit (scaleZ c X) = polarUnit X := by
  rw [polarUnit, polarUnit, polarRadius_scaleZ c hc.le X]
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  unfold scaleZ
  simp only [polarRadius, detZ]
  field_simp [ne_of_gt hc]

theorem scaleZ_polarUnit (X : ZornCell ℝ) (hX : 0 < detZ X) :
    scaleZ (polarRadius X) (polarUnit X) = X := by
  have hsqrt : polarRadius X ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hX)
  cases X
  simp only [polarUnit, polarRadius, scaleZ]
  congr 1 <;> field_simp [hsqrt]

theorem polarUnit_mul_conjZ (X : ZornCell ℝ) (hX : 0 < detZ X) :
    polarUnit X * conjZ (polarUnit X) = scalarZ 1 := by
  rw [mul_conjZ, detZ_polarUnit X hX]

theorem conjZ_polarUnit_mul (X : ZornCell ℝ) (hX : 0 < detZ X) :
    conjZ (polarUnit X) * polarUnit X = scalarZ 1 := by
  rw [conjZ_mul, detZ_polarUnit X hX]

end
end InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
