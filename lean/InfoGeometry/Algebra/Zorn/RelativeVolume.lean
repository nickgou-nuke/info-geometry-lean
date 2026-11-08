import InfoGeometry.Algebra.Zorn.ConcreteComposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.Zorn.RelativeVolume

Concrete logarithmic relative-volume identities for
`InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell`.
-/

namespace InfoGeometry.Algebra.Zorn.RelativeVolume

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

/-- Negative logarithmic Zorn volume potential. -/
noncomputable def negLogVolume (X : ZornCell ℝ) : ℝ :=
  -Real.log (detZ X)

/-- Radon–Nikodym-style relative Zorn volume factor. -/
noncomputable def relativeVolumeRN (X Y : ZornCell ℝ) : ℝ :=
  detZ Y / detZ X

/-- Positive determinant is preserved by concrete Zorn multiplication. -/
theorem detZ_mul_pos
    (X Y : ZornCell ℝ)
    (hX : 0 < detZ X) (hY : 0 < detZ Y) :
    0 < detZ (X * Y) := by
  rw [detZ_mul]
  exact mul_pos hX hY

/-- Relative Zorn volume is positive on the positive-determinant stratum. -/
theorem relativeVolumeRN_pos
    (X Y : ZornCell ℝ)
    (hX : 0 < detZ X) (hY : 0 < detZ Y) :
    0 < relativeVolumeRN X Y := by
  unfold relativeVolumeRN
  exact div_pos hY hX

/-- `-log(det Y / det X) = (-log det Y) - (-log det X)`. -/
theorem negLog_relativeVolumeRN_eq_negLogVolume_sub
    (X Y : ZornCell ℝ)
    (hX : 0 < detZ X) (hY : 0 < detZ Y) :
    -Real.log (relativeVolumeRN X Y) =
      negLogVolume Y - negLogVolume X := by
  unfold relativeVolumeRN negLogVolume
  rw [Real.log_div (ne_of_gt hY) (ne_of_gt hX)]
  ring

/-- `det(X⋆Y)/det(X) = det(Y)` whenever `det(X) ≠ 0`. -/
theorem relativeVolumeRN_mul_left
    (X Y : ZornCell ℝ)
    (hX : detZ X ≠ 0) :
    relativeVolumeRN X (X * Y) = detZ Y := by
  unfold relativeVolumeRN
  rw [detZ_mul]
  field_simp [hX]

/-- `-log(det(X⋆Y)/det(X)) = -log(det(Y))`. -/
theorem negLog_relativeVolumeRN_mul_left
    (X Y : ZornCell ℝ)
    (hX : detZ X ≠ 0) :
    -Real.log (relativeVolumeRN X (X * Y)) = negLogVolume Y := by
  rw [relativeVolumeRN_mul_left X Y hX]
  rfl

/-- Log-additivity of determinant on the positive stratum. -/
theorem log_detZ_mul
    (X Y : ZornCell ℝ)
    (hX : 0 < detZ X) (hY : 0 < detZ Y) :
    Real.log (detZ (X * Y)) = Real.log (detZ X) + Real.log (detZ Y) := by
  rw [detZ_mul]
  exact Real.log_mul (ne_of_gt hX) (ne_of_gt hY)

/-- Additivity of `negLogVolume` on the positive-determinant stratum. -/
theorem negLogVolume_mul
    (X Y : ZornCell ℝ)
    (hX : 0 < detZ X) (hY : 0 < detZ Y) :
    negLogVolume (X * Y) = negLogVolume X + negLogVolume Y := by
  unfold negLogVolume
  rw [log_detZ_mul X Y hX hY]
  ring

end InfoGeometry.Algebra.Zorn.RelativeVolume
