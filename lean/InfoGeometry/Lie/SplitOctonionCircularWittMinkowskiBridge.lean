import Mathlib.Tactic
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow

/-!
# Minkowski readout of the circular Witt form

The circular Witt coordinates contain the ordinary Minkowski quadratic form
on the boundary subspace
`(t,x,y,z) ↦ (t+z,x,y,0,t-z,x,y,0)`.

This is a linear quadratic-form bridge only.  It does not identify the
Minkowski boundary with a subalgebra of the nonassociative carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularWittMinkowskiBridge

open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow

abbrev Coordinate := Fin 8 → ℝ

@[simp] theorem add_t (u v : Minkowski4) : (u + v).t = u.t + v.t := rfl
@[simp] theorem add_x (u v : Minkowski4) : (u + v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Minkowski4) : (u + v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Minkowski4) : (u + v).z = u.z + v.z := rfl
@[simp] theorem smul_t (c : ℝ) (v : Minkowski4) : (c • v).t = c * v.t := rfl
@[simp] theorem smul_x (c : ℝ) (v : Minkowski4) : (c • v).x = c * v.x := rfl
@[simp] theorem smul_y (c : ℝ) (v : Minkowski4) : (c • v).y = c * v.y := rfl
@[simp] theorem smul_z (c : ℝ) (v : Minkowski4) : (c • v).z = c * v.z := rfl

def circularMinkowskiEmbedding : Minkowski4 →ₗ[ℝ] Coordinate where
  toFun v := ![v.t + v.z, v.x, v.y, 0, v.t - v.z, v.x, v.y, 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp] theorem circularMinkowskiEmbedding_apply (v : Minkowski4) :
    circularMinkowskiEmbedding v =
      ![v.t + v.z, v.x, v.y, 0, v.t - v.z, v.x, v.y, 0] := rfl

theorem circularWittNorm_circularMinkowskiEmbedding (v : Minkowski4) :
    circularWittNorm (circularMinkowskiEmbedding v) = v.q := by
  simp [circularWittNorm, circularMinkowskiEmbedding, Minkowski4.q]
  ring

theorem circularWittNorm_circularMinkowskiEmbedding_eq_zero_iff
    (v : Minkowski4) :
    circularWittNorm (circularMinkowskiEmbedding v) = 0 ↔ v.IsNull := by
  rw [circularWittNorm_circularMinkowskiEmbedding]
  rfl

theorem circularMinkowskiEmbedding_injective :
    Function.Injective circularMinkowskiEmbedding := by
  intro v w h
  apply Minkowski4.ext
  · have h0 := congrFun h 0
    have h4 := congrFun h 4
    dsimp [circularMinkowskiEmbedding, Minkowski4.t, Minkowski4.z] at h0 h4
    linarith
  · change v.x = w.x
    simpa [circularMinkowskiEmbedding, Minkowski4.x] using congrFun h 1
  · change v.y = w.y
    simpa [circularMinkowskiEmbedding, Minkowski4.y] using congrFun h 2
  · have h0 := congrFun h 0
    have h4 := congrFun h 4
    dsimp [circularMinkowskiEmbedding, Minkowski4.t, Minkowski4.z] at h0 h4
    linarith

end InfoGeometry.Lie.SplitOctonionCircularWittMinkowskiBridge
