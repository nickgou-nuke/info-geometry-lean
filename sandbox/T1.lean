import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

namespace ScratchT

open Matrix
open InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

noncomputable def bg0 : Matrix (Fin 7) (Fin 7) ℝ := (1/2 : ℝ) • (skewGen 1 2 - skewGen 3 4)
noncomputable def bg1 : Matrix (Fin 7) (Fin 7) ℝ := (1/2 : ℝ) • (- skewGen 0 2 - skewGen 3 5)

def sr0 : Fin 7 := 1
def ss0 : Fin 7 := 2

example : bg1 sr0 ss0 = 0 := by
  dsimp [bg1, skewGen]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> rfl

end ScratchT
