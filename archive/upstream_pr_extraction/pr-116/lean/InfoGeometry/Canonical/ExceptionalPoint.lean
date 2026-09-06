import Mathlib.Data.Complex.Basic
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.ExceptionalPoint

open Complex

structure JonesVector where
  x : ℂ
  y : ℂ

structure JonesMatrix where
  m11 : ℂ
  m12 : ℂ
  m21 : ℂ
  m22 : ℂ

def apply_matrix (M : JonesMatrix) (v : JonesVector) : JonesVector :=
  ⟨M.m11 * v.x + M.m12 * v.y, M.m21 * v.x + M.m22 * v.y⟩

def N (x_val : ℂ) : JonesMatrix := ⟨1, x_val, 0, 1⟩

def is_eigenvector (M : JonesMatrix) (lambda : ℂ) (v : JonesVector) : Prop :=
  apply_matrix M v = ⟨lambda * v.x, lambda * v.y⟩

@[rep_depth thermo]
theorem ep_dimensional_collapse (x_val : ℂ) (v : JonesVector)
    (hx : x_val ≠ 0) (heig : is_eigenvector (N x_val) 1 v) :
    v.y = 0 := by
  dsimp [is_eigenvector, apply_matrix, N] at heig
  have h1 : 1 * v.x + x_val * v.y = 1 * v.x :=
    congr_arg JonesVector.x heig
  have h2 : x_val * v.y = 0 := by
    calc
      x_val * v.y = (1 * v.x + x_val * v.y) - 1 * v.x := by ring
      _ = 1 * v.x - 1 * v.x := by rw [h1]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h2 with hzero | hzero
  · exact False.elim (hx hzero)
  · exact hzero

end InfoGeometry.Canonical.ExceptionalPoint
