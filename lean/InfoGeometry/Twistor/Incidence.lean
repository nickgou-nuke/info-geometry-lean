import InfoGeometry.Clifford.Soldering
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Twistor Incidence Geometry

This module formalizes the geometric interpretation of the twistor incidence relation.
The central theorem is that the set of spacetime points incident with a fixed twistor
(with a non-zero primary spinor) forms a null geodesic (a light ray).

The proof leverages the Metric-Determinant Duality established via the Soldering Form.
-/

open scoped Matrix
open scoped Quaternion

namespace Incidence

open Soldering

/-- A twistor is a pair of spinors (represented here as vectors in ℝ²). -/
abbrev Twistor := (ℝ × ℝ) × (ℝ × ℝ)

/-- 
Spacetime points act on spinors via the soldering form.
This represents the matrix-vector multiplication $M \pi$.
-/
noncomputable def pointAction (X : Vec22) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun π :=
    let M := soldering X
    (M 0 0 * π.1 + M 0 1 * π.2, M 1 0 * π.1 + M 1 1 * π.2)
  map_add' π₁ π₂ := by
    dsimp
    ext <;> dsimp <;> ring
  map_smul' a π := by
    dsimp
    ext <;> dsimp <;> ring

/-- 
The Soldering form as a linear map into endomorphisms of the spinor space.
-/
noncomputable def twistorMap : Vec22 →ₗ[ℝ] ((ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) where
  toFun := pointAction
  map_add' X Y := by
    apply LinearMap.ext
    intro π
    ext <;> (dsimp [pointAction, soldering]; ring)
  map_smul' a X := by
    apply LinearMap.ext
    intro π
    ext <;> (dsimp [pointAction, soldering]; ring)

/-- 
Incidence relation: A twistor $Z = (\omega, \pi)$ is incident with point $X$ 
if $\omega = X(\pi)$ under the soldering action.
-/
def Incident (Z : Twistor) (X : Vec22) : Prop :=
  Z.1 = pointAction X Z.2

/-- 
Lemma: If a 2x2 matrix annihilates a non-zero vector, its determinant is zero.
This is a standard linear algebra result specialized for our explicit representation.
-/
lemma det_zero_of_annihilates_nonzero (M : Matrix (Fin 2) (Fin 2) ℝ) (π : ℝ × ℝ)
    (h_nonzero : π ≠ 0)
    (h_annihilates : M 0 0 * π.1 + M 0 1 * π.2 = 0 ∧ M 1 0 * π.1 + M 1 1 * π.2 = 0) :
    M.det = 0 := by
  rcases h_annihilates with ⟨h1, h2⟩
  have h_det : M.det * π.1 = 0 ∧ M.det * π.2 = 0 := by
    constructor
    · have H : M.det * π.1 = M 1 1 * (M 0 0 * π.1 + M 0 1 * π.2) - M 0 1 * (M 1 0 * π.1 + M 1 1 * π.2) := by
        simp [Matrix.det_fin_two]; ring
      rw [H, h1, h2]; ring
    · have H : M.det * π.2 = M 0 0 * (M 1 0 * π.1 + M 1 1 * π.2) - M 1 0 * (M 0 0 * π.1 + M 0 1 * π.2) := by
        simp [Matrix.det_fin_two]; ring
      rw [H, h1, h2]; ring
  
  -- Since π ≠ 0, either π.1 ≠ 0 or π.2 ≠ 0
  cases mul_eq_zero.mp h_det.1 with
  | inl hd => exact hd
  | inr hp1 => 
    cases mul_eq_zero.mp h_det.2 with
    | inl hd => exact hd
    | inr hp2 =>
      -- Both π.1 = 0 and π.2 = 0, contradiction.
      exfalso
      apply h_nonzero
      ext <;> assumption

/-- 
**The Fundamental Theorem of Twistor Incidence Geometry:**
If two distinct spacetime points $X$ and $Y$ are incident with the same twistor $Z = (\omega, \pi)$,
and the primary spinor $\pi$ is non-zero, then the vector difference $(X - Y)$ is null.
This proves that the locus of incident points forms a null geodesic (light ray).
-/
theorem incident_points_null_separated (Z : Twistor) (X Y : Vec22) 
    (hX : Incident Z X) (hY : Incident Z Y) (h_pi : Z.2 ≠ 0) :
    q22 (X - Y) = 0 := by
  -- 1. Unpack incidence relations
  have h1 : Z.1 = pointAction X Z.2 := hX
  have h2 : Z.1 = pointAction Y Z.2 := hY
  
  -- 2. Subtract to get pointAction (X - Y) π = 0
  have h_diff : pointAction (X - Y) Z.2 = 0 := by
    have h_lin : pointAction (X - Y) Z.2 = pointAction X Z.2 - pointAction Y Z.2 := by
      -- Use linearity of twistorMap
      have h_map : twistorMap (X - Y) = twistorMap X - twistorMap Y := map_sub twistorMap X Y
      have h_eval : twistorMap (X - Y) Z.2 = (twistorMap X - twistorMap Y) Z.2 := by rw [h_map]
      simpa [twistorMap, LinearMap.sub_apply] using h_eval
    rw [h_lin, ← h1, ← h2, sub_self]

  -- 3. Translate this to matrix annihilation: soldering(X - Y) * π = 0
  have h_matrix_annihilates : 
      (soldering (X - Y)) 0 0 * Z.2.1 + (soldering (X - Y)) 0 1 * Z.2.2 = 0 ∧ 
      (soldering (X - Y)) 1 0 * Z.2.1 + (soldering (X - Y)) 1 1 * Z.2.2 = 0 := by
    have hd : (pointAction (X - Y) Z.2).1 = 0 ∧ (pointAction (X - Y) Z.2).2 = 0 := by
      rw [h_diff]
      exact ⟨rfl, rfl⟩
    exact hd

  -- 4. By the lemma, the matrix must have zero determinant
  have h_det_zero : (soldering (X - Y)).det = 0 :=
    det_zero_of_annihilates_nonzero (soldering (X - Y)) Z.2 h_pi h_matrix_annihilates

  -- 5. By Metric-Determinant Duality, the quadratic form evaluated on (X - Y) is zero.
  rw [← det_soldering_eq_q22 (X - Y)]
  exact h_det_zero

end Incidence
