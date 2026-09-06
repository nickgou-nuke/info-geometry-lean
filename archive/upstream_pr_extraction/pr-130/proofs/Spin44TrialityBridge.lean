import Mathlib
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import proofs.SplitOctonionAlgebra
import proofs.SplitOctonionNorm44
import proofs.SplitOctonionTrialityCore

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityCore

namespace Spin44TrialityBridge

/-- `splitBilinear` as a `LinearMap.BilinMap ℝ SplitOct ℝ` -/
noncomputable def splitBilinearMap : LinearMap.BilinMap ℝ SplitOct ℝ :=
  LinearMap.mk₂ ℝ splitBilinear
    (by
      intro m₁ m₂ n
      dsimp [splitBilinear, splitNorm, add_def]
      ring)
    (by
      intro c m n
      dsimp [splitBilinear, splitNorm, smul_def]
      ring)
    (by
      intro m n₁ n₂
      rw [splitBilinear_symmetric]
      have h1 : splitBilinear (n₁ + n₂) m = splitBilinear m (n₁ + n₂) := splitBilinear_symmetric _ _
      rw [h1]
      dsimp [splitBilinear, splitNorm, add_def]
      ring)
    (by
      intro c m n
      rw [splitBilinear_symmetric]
      have h1 : splitBilinear (c • n) m = splitBilinear m (c • n) := splitBilinear_symmetric _ _
      rw [h1]
      dsimp [splitBilinear, splitNorm, smul_def]
      ring)

/-- The split octonion norm as a Mathlib `QuadraticForm ℝ SplitOct`. -/
noncomputable def splitQuadraticForm : QuadraticForm ℝ SplitOct where
  toFun := splitNorm
  toFun_smul := by
    intro a x
    dsimp [splitNorm, smul_def]
    ring
  exists_companion' := ⟨(2 : ℝ) • splitBilinearMap, by
    intro x y
    change splitNorm (x + y) = splitNorm x + splitNorm y + 2 * splitBilinear x y
    dsimp [splitNorm, splitBilinear, add_def]
    ring⟩

/-- The Spin(4,4) group is the Spin group of the split octonion quadratic form. -/
noncomputable def Spin44 := spinGroup splitQuadraticForm

end Spin44TrialityBridge
