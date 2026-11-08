import InfoGeometry.Clifford.Soldering
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Twistor Incidence Geometry

This module proves the finite algebraic null-separation consequence of the
twistor incidence relation in the displayed `2 × 2` soldering model.  It does
not construct geodesics or a light-ray manifold.
-/

open scoped Matrix
open scoped Quaternion

namespace InfoGeometry.Twistor.Incidence

open InfoGeometry.Clifford.Soldering

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
    ext <;> (simp [pointAction, soldering, Pi.add_apply, Matrix.add_apply]; ring)
  map_smul' a X := by
    apply LinearMap.ext
    intro π
    ext <;> (simp [pointAction, soldering, Pi.smul_apply, Matrix.smul_apply]; ring)

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

/-- A singular real `2 × 2` matrix has a nonzero vector in its kernel.

The proof chooses a perpendicular vector to a nonzero row. If the first row
vanishes, it uses the second row; if both vanish, the first basis vector is a
kernel witness. -/
lemma exists_nonzero_annihilator_of_det_zero (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : M.det = 0) :
    ∃ π : ℝ × ℝ, π ≠ 0 ∧
      M 0 0 * π.1 + M 0 1 * π.2 = 0 ∧
      M 1 0 * π.1 + M 1 1 * π.2 = 0 := by
  by_cases hrow : M 0 0 = 0 ∧ M 0 1 = 0
  · by_cases hrow' : M 1 0 = 0 ∧ M 1 1 = 0
    · refine ⟨(1, 0), ?_, ?_, ?_⟩
      · simp
      · simp [hrow.1, hrow.2]
      · simp [hrow'.1, hrow'.2]
    · refine ⟨(-M 1 1, M 1 0), ?_, ?_, ?_⟩
      · intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp at h1 h2
        exact hrow' ⟨h2, h1⟩
      · simp [hrow.1, hrow.2]
      · ring
  · refine ⟨(-M 0 1, M 0 0), ?_, ?_, ?_⟩
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp at h1 h2
      exact hrow ⟨h2, h1⟩
    · ring
    · have hdet' : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
        Matrix.det_fin_two M
      rw [hdet'] at hdet
      nlinarith

/-- In the finite soldering model, a point displacement is null exactly when
its soldering operator annihilates some nonzero spinor. -/
theorem null_iff_exists_nonzero_soldering_annihilator (X : Vec22) :
    q22 X = 0 ↔ ∃ π : ℝ × ℝ, π ≠ 0 ∧ pointAction X π = 0 := by
  constructor
  · intro hnull
    have hdet : (soldering X).det = 0 := by
      rw [det_soldering_eq_q22]
      exact hnull
    obtain ⟨π, hπ, h₀, h₁⟩ := exists_nonzero_annihilator_of_det_zero _ hdet
    refine ⟨π, hπ, ?_⟩
    apply Prod.ext
    · simpa [pointAction, InfoGeometry.Clifford.Soldering.pointAction] using h₀
    · simpa [pointAction, InfoGeometry.Clifford.Soldering.pointAction] using h₁
  · rintro ⟨π, hπ, hker⟩
    have h₀ : (soldering X) 0 0 * π.1 + (soldering X) 0 1 * π.2 = 0 := by
      exact congrArg Prod.fst hker
    have h₁ : (soldering X) 1 0 * π.1 + (soldering X) 1 1 * π.2 = 0 := by
      exact congrArg Prod.snd hker
    have hdet : (soldering X).det = 0 :=
      det_zero_of_annihilates_nonzero (soldering X) π hπ ⟨h₀, h₁⟩
    rw [det_soldering_eq_q22] at hdet
    exact hdet

/-- 
If two spacetime points `X` and `Y` are incident with the same twistor
`Z = (ω, π)`, and the primary spinor `π` is non-zero, then the vector
difference `X - Y` is null in the finite soldering model.
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

/-- Two points share a twistor with nonzero primary spinor exactly when their
difference is null in the finite soldering model. -/
theorem incident_points_null_separated_iff (X Y : Vec22) :
    q22 (X - Y) = 0 ↔
      ∃ Z : Twistor, Z.2 ≠ 0 ∧ Incident Z X ∧ Incident Z Y := by
  constructor
  · intro hnull
    obtain ⟨π, hπ, hker⟩ :=
      (null_iff_exists_nonzero_soldering_annihilator (X - Y)).mp hnull
    refine ⟨(pointAction X π, π), hπ, rfl, ?_⟩
    change pointAction X π = pointAction Y π
    have hlin : pointAction (X - Y) π = pointAction X π - pointAction Y π := by
      change (twistorMap (X - Y)) π = (twistorMap X) π - (twistorMap Y) π
      rw [map_sub twistorMap X Y]
      simp
    rw [hlin] at hker
    exact sub_eq_zero.mp hker
  · rintro ⟨Z, hZ, hX, hY⟩
    exact incident_points_null_separated Z X Y hX hY hZ

end InfoGeometry.Twistor.Incidence
