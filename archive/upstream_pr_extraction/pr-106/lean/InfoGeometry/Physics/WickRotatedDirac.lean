import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

open Complex Matrix

namespace InfoGeometry.Physics.Relativity

def wick_rotate (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun i => if i = 0 then I * v i else v i

def euclidean_inner (v w : Fin 4 → ℂ) : ℂ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3

def minkowski_inner (v w : Fin 4 → ℂ) : ℂ :=
  - (v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3

theorem wick_euclidean_is_minkowski (v w : Fin 4 → ℂ) :
    euclidean_inner (wick_rotate v) (wick_rotate w) = minkowski_inner v w := by
  dsimp [euclidean_inner, minkowski_inner, wick_rotate]
  calc
    I * v 0 * (I * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3
      = I * I * (v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by ring
    _ = -1 * (v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by rw [I_mul_I]
    _ = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by ring

end InfoGeometry.Physics.Relativity
