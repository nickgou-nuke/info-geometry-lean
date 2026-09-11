import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Wallpaper classification finite algebra

Repaired external file: Euclidean affine composition and the trace expression
used in crystallographic restrictions.
-/

noncomputable section

namespace WallpaperClassification

open Matrix Real

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Exact affine composition law: `N(Mx+v)+w=(NM)x+(Nv+w)`. -/
theorem e2_composition_exact (M N : Matrix n n ℝ) (v w x : n → ℝ) :
    N *ᵥ (M *ᵥ x + v) + w = (N * M) *ᵥ x + (N *ᵥ v + w) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  ext i
  simp only [Pi.add_apply]
  abel

/-- Trace of a planar rotation by angle `θ`. -/
def crystallographic_trace (theta : ℝ) : ℝ := 2 * Real.cos theta

/-- Algebraic statement that order `q` has integer trace `m`. -/
def valid_crystallographic_order (q : ℕ) (m : ℤ) : Prop :=
  crystallographic_trace (2 * Real.pi / (q : ℝ)) = (m : ℝ)

/-- Orders `1,2,3,4,6` have the expected integer traces. -/
theorem standard_crystallographic_traces :
    valid_crystallographic_order 1 2 ∧
    valid_crystallographic_order 2 (-2) ∧
    valid_crystallographic_order 3 (-1) ∧
    valid_crystallographic_order 4 0 ∧
    valid_crystallographic_order 6 1 := by
  unfold valid_crystallographic_order crystallographic_trace
  constructor
  · norm_num [Real.cos_two_pi]
  constructor
  · norm_num [Real.cos_pi]
  constructor
  · have hangle : 2 * Real.pi / ((3 : ℕ) : ℝ) = Real.pi - Real.pi / 3 := by norm_num; ring
    rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  constructor
  · have hangle : 2 * Real.pi / ((4 : ℕ) : ℝ) = Real.pi / 2 := by norm_num; ring
    rw [hangle, Real.cos_pi_div_two]
    norm_num
  · have hangle : 2 * Real.pi / ((6 : ℕ) : ℝ) = Real.pi / 3 := by norm_num; ring
    rw [hangle, Real.cos_pi_div_three]
    norm_num

end WallpaperClassification
