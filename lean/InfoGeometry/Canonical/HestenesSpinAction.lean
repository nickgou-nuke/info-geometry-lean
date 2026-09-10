import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

noncomputable section

namespace InfoGeometry.Canonical.HestenesSpinAction

open Matrix

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- The action of SL(2,C) on a 2x2 complex matrix (Minkowski vector representative). -/
def spinAction (g : SL2C) (V : M2C) : M2C :=
  (g : M2C) * V * star (g : M2C)

/-- The determinant of the acted vector is preserved, which corresponds to preserving the Minkowski quadratic form. -/
theorem spinAction_preserves_det (g : SL2C) (V : M2C) :
    (spinAction g V).det = V.det := by
  dsimp [spinAction]
  rw [det_mul, det_mul]
  have hg : (g : M2C).det = 1 := g.prop
  have hg_star : (star (g : M2C)).det = 1 := by
    change ((g : M2C)ᴴ).det = 1
    rw [det_conjTranspose, hg, star_one]
  rw [hg, hg_star, one_mul, mul_one]

end InfoGeometry.Canonical.HestenesSpinAction
