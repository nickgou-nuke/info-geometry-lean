/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Sp4Contact
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.Graded
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Contact five-grading of the real symplectic Lie algebra in dimension four

Each homogeneous component is an actual eigenspace of the native adjoint
endomorphism. Explicit coordinate equivalences establish the dimensions
`1, 2, 4, 2, 1`; reconstruction and independence prove the decomposition.
The Lie bracket adds degrees, and components outside `[-2,2]` vanish. The
native `GradedLieAlgebra` instance supplies `DirectSum.decomposeLieEquiv grade`.
These facts prove the positive and negative two-step truncation for this
particular Lie algebra, without a classification or uniqueness claim.
-/

noncomputable section

namespace InfoGeometry.Algebra.Sp4Contact

open scoped DirectSum

/-- Contact degree of each of the ten matrix coordinates. -/
def degree : Fin 10 → ℤ := ![-2, -1, -1, 0, 0, 0, 0, 1, 1, 2]

/-- The homogeneous subspace of integer degree `k`, as a native eigenspace. -/
def grade (k : ℤ) : Submodule ℝ Sp :=
  (LieAlgebra.ad ℝ Sp gradingElement).eigenspace (k : ℝ)

theorem mem_grade_iff_lie (k : ℤ) (X : Sp) :
    X ∈ grade k ↔ ⁅gradingElement, X⁆ = (k : ℝ) • X :=
  Module.End.mem_eigenspace_iff

theorem coordinates_lie_gradingElement (X : Sp) (i : Fin 10) :
    coordinates ⁅gradingElement, X⁆ i = (degree i : ℝ) * coordinates X i := by
  obtain ⟨c, rfl⟩ := coordinateEquiv.surjective X
  fin_cases i <;>
    norm_num [coordinates, degree, gradingElement, generator, matrixOfCoordinates,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_succ,
      Pi.single_apply] <;> ring

theorem mem_grade_iff_coordinates (k : ℤ) (X : Sp) :
    X ∈ grade k ↔ ∀ i, degree i ≠ k → coordinates X i = 0 := by
  rw [mem_grade_iff_lie]
  constructor
  · intro h i hi
    have hc := congrArg (fun Y : Sp => coordinates Y i) h
    rw [coordinates_lie_gradingElement, coordinates_smul] at hc
    change (degree i : ℝ) * coordinates X i = (k : ℝ) * coordinates X i at hc
    have hne : (degree i : ℝ) - (k : ℝ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hi
    have hz : ((degree i : ℝ) - (k : ℝ)) * coordinates X i = 0 := by
      nlinarith [hc]
    exact (mul_eq_zero.mp hz).resolve_left hne
  · intro h
    apply coordinates_injective
    funext i
    rw [coordinates_lie_gradingElement, coordinates_smul]
    change (degree i : ℝ) * coordinates X i = (k : ℝ) * coordinates X i
    by_cases hi : degree i = k
    · rw [hi]
    · rw [h i hi]
      simp

/-- Zero-extension of the coordinates with prescribed degree. -/
def extendGradeCoordinates (k : ℤ) (c : {i : Fin 10 // degree i = k} → ℝ) :
    Fin 10 → ℝ :=
  fun i => if h : degree i = k then c ⟨i, h⟩ else 0

/-- Explicit equivalence between an eigenspace and its supported coordinates. -/
def gradeEquiv (k : ℤ) : ({i : Fin 10 // degree i = k} → ℝ) ≃ₗ[ℝ] grade k where
  toFun c := ⟨coordinateEquiv (extendGradeCoordinates k c), by
    rw [mem_grade_iff_coordinates]
    intro i hi
    simp [extendGradeCoordinates, hi]⟩
  invFun X i := coordinates (X : Sp) i
  left_inv c := by
    funext i
    simp [extendGradeCoordinates, i.property]
  right_inv X := by
    apply Subtype.ext
    apply coordinates_injective
    funext i
    simp only [coordinates_coordinateEquiv]
    by_cases hi : degree i = k
    · simp [extendGradeCoordinates, hi]
    · simp [extendGradeCoordinates, hi,
        (mem_grade_iff_coordinates k (X : Sp)).mp X.property i hi]
  map_add' c d := by
    apply Subtype.ext
    apply coordinates_injective
    funext i
    simp only [coordinates_coordinateEquiv]
    by_cases hi : degree i = k <;> simp [extendGradeCoordinates, hi]
  map_smul' r c := by
    apply Subtype.ext
    apply coordinates_injective
    funext i
    simp only [coordinates_coordinateEquiv]
    by_cases hi : degree i = k <;> simp [extendGradeCoordinates, hi]

theorem finrank_grade (k : ℤ) :
    Module.finrank ℝ (grade k) = Fintype.card {i : Fin 10 // degree i = k} := by
  rw [← (gradeEquiv k).finrank_eq, Module.finrank_fintype_fun_eq_card]

theorem finrank_grade_neg_two : Module.finrank ℝ (grade (-2)) = 1 := by
  rw [finrank_grade]
  decide

theorem finrank_grade_neg_one : Module.finrank ℝ (grade (-1)) = 2 := by
  rw [finrank_grade]
  decide

theorem finrank_grade_zero : Module.finrank ℝ (grade 0) = 4 := by
  rw [finrank_grade]
  decide

theorem finrank_grade_one : Module.finrank ℝ (grade 1) = 2 := by
  rw [finrank_grade]
  decide

theorem finrank_grade_two : Module.finrank ℝ (grade 2) = 1 := by
  rw [finrank_grade]
  decide

theorem degree_bounds (i : Fin 10) : -2 ≤ degree i ∧ degree i ≤ 2 := by
  fin_cases i <;> decide

theorem grade_eq_bot (k : ℤ) (hk : k < -2 ∨ 2 < k) : grade k = ⊥ := by
  apply (Submodule.eq_bot_iff (grade k)).mpr
  intro X hX
  apply coordinates_injective
  funext i
  rw [coordinates_zero]
  apply (mem_grade_iff_coordinates k X).mp hX
  have hi := degree_bounds i
  rcases hk with hk | hk <;> omega

/-- Matrix projection to one of the homogeneous components. -/
def component (k : ℤ) (X : Sp) : Sp :=
  coordinateEquiv (fun i => if degree i = k then coordinates X i else 0)

@[simp] theorem coordinates_component (k : ℤ) (X : Sp) (i : Fin 10) :
    coordinates (component k X) i =
      if degree i = k then coordinates X i else 0 := by
  simp [component]

theorem component_mem_grade (k : ℤ) (X : Sp) : component k X ∈ grade k := by
  rw [mem_grade_iff_coordinates]
  intro i hi
  simp [hi]

theorem component_of_mem_grade (k : ℤ) (X : Sp) (hX : X ∈ grade k) :
    component k X = X := by
  apply coordinates_injective
  funext i
  rw [coordinates_component]
  split_ifs with hi
  · rfl
  · exact ((mem_grade_iff_coordinates k X).mp hX i hi).symm

theorem homogeneous_reconstruction (X : Sp) :
    component (-2) X + component (-1) X + component 0 X +
      component 1 X + component 2 X = X := by
  apply coordinates_injective
  funext i
  fin_cases i <;> simp [coordinates_add, degree]

/-- Independence is inherited from the eigenspaces for distinct real eigenvalues. -/
theorem grades_independent : iSupIndep grade := by
  exact (LieAlgebra.ad ℝ Sp gradingElement).eigenspaces_iSupIndep.comp
    (Int.cast_injective : Function.Injective (fun k : ℤ => (k : ℝ)))

/-- The integer-indexed homogeneous spaces span the full symplectic Lie algebra. -/
theorem grades_span : (⨆ k : ℤ, grade k) = ⊤ := by
  apply top_unique
  intro X _
  rw [← homogeneous_reconstruction X]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact (le_iSup grade (-2)) (component_mem_grade (-2) X)
        · exact (le_iSup grade (-1)) (component_mem_grade (-1) X)
      · exact (le_iSup grade 0) (component_mem_grade 0 X)
    · exact (le_iSup grade 1) (component_mem_grade 1 X)
  · exact (le_iSup grade 2) (component_mem_grade 2 X)

/-- The homogeneous eigenspaces form an internal direct sum. -/
theorem grades_internal : DirectSum.IsInternal grade :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    grades_independent grades_span

theorem lie_mem_grade (p q : ℤ) {X Y : Sp}
    (hX : X ∈ grade p) (hY : Y ∈ grade q) : ⁅X, Y⁆ ∈ grade (p + q) := by
  rw [mem_grade_iff_lie] at hX hY ⊢
  rw [leibniz_lie, hX, hY, smul_lie, lie_smul, Int.cast_add, add_smul]

/-- Native graded Lie algebra structure from the proved decomposition and bracket law. -/
instance : GradedLieAlgebra grade where
  toDecomposition := grades_internal.chooseDecomposition
  bracket_mem := fun {p q} {_X _Y} hX hY => lie_mem_grade p q hX hY

theorem lie_eq_zero_of_degree_outside (p q : ℤ) {X Y : Sp}
    (hX : X ∈ grade p) (hY : Y ∈ grade q)
    (hpq : p + q < -2 ∨ 2 < p + q) : ⁅X, Y⁆ = 0 := by
  have h := lie_mem_grade p q hX hY
  rw [grade_eq_bot (p + q) hpq] at h
  exact h

theorem positive_two_step (X Y Z : Sp)
    (hX : X ∈ grade 1) (hY : Y ∈ grade 1) (hZ : Z ∈ grade 1) :
    ⁅X, ⁅Y, Z⁆⁆ = 0 :=
  lie_eq_zero_of_degree_outside 1 (1 + 1) hX (lie_mem_grade 1 1 hY hZ) (by norm_num)

theorem negative_two_step (X Y Z : Sp)
    (hX : X ∈ grade (-1)) (hY : Y ∈ grade (-1)) (hZ : Z ∈ grade (-1)) :
    ⁅X, ⁅Y, Z⁆⁆ = 0 :=
  lie_eq_zero_of_degree_outside (-1) (-1 + -1) hX
    (lie_mem_grade (-1) (-1) hY hZ) (by norm_num)

theorem generator_mem_grade (i : Fin 10) : generator i ∈ grade (degree i) := by
  rw [mem_grade_iff_coordinates]
  intro j hj
  simp only [generator, coordinates_coordinateEquiv]
  have hji : j ≠ i := by
    intro h
    exact hj (congrArg degree h)
  simp [hji]

theorem grade_one_decomposition (X : Sp) (hX : X ∈ grade 1) :
    X = coordinates X 7 • u1 + coordinates X 8 • u2 := by
  apply coordinates_injective
  funext i
  fin_cases i <;>
    simp [coordinates_add, coordinates_smul, u1, u2, generator]
  all_goals exact (mem_grade_iff_coordinates 1 X).mp hX _ (by decide)

theorem grade_neg_one_decomposition (X : Sp) (hX : X ∈ grade (-1)) :
    X = coordinates X 1 • v1 + coordinates X 2 • v2 := by
  apply coordinates_injective
  funext i
  fin_cases i <;>
    simp [coordinates_add, coordinates_smul, v1, v2, generator]
  all_goals exact (mem_grade_iff_coordinates (-1) X).mp hX _ (by decide)

theorem positive_bracket (a b c d : ℝ) :
    ⁅a • u1 + b • u2, c • u1 + d • u2⁆ =
      (-2 * (a * d - b * c)) • zPlus := by
  have hu : ⁅u2, u1⁆ = (2 : ℝ) • zPlus := by
    rw [← lie_skew u2 u1, lie_u1_u2]
    simp
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero,
    zero_add, add_zero, lie_u1_u2, hu, smul_smul]
  rw [← add_smul]
  congr 1
  ring

theorem negative_bracket (a b c d : ℝ) :
    ⁅a • v1 + b • v2, c • v1 + d • v2⁆ =
      (2 * (a * d - b * c)) • zMinus := by
  have hv : ⁅v2, v1⁆ = (-2 : ℝ) • zMinus := by
    rw [← lie_skew v2 v1, lie_v1_v2]
    simp
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero,
    zero_add, add_zero, lie_v1_v2, hv, smul_smul]
  rw [← add_smul]
  congr 1
  ring

/-- The bracket pairing on the positive degree-one space has zero radical. -/
theorem positive_pairing_nondegenerate (X : Sp) (hX : X ∈ grade 1)
    (h : ∀ Y ∈ grade 1, ⁅X, Y⁆ = 0) : X = 0 := by
  have h1 := h u1 (generator_mem_grade 7)
  have h2 := h u2 (generator_mem_grade 8)
  have hdec := grade_one_decomposition X hX
  rw [hdec] at h1 h2
  have h1' : (2 * coordinates X 8) • zPlus = 0 := by
    calc
      _ = ⁅coordinates X 7 • u1 + coordinates X 8 • u2, u1⁆ := by
        simpa using (positive_bracket (coordinates X 7) (coordinates X 8) 1 0).symm
      _ = 0 := h1
  have h2' : (-2 * coordinates X 7) • zPlus = 0 := by
    calc
      _ = ⁅coordinates X 7 • u1 + coordinates X 8 • u2, u2⁆ := by
        simpa using (positive_bracket (coordinates X 7) (coordinates X 8) 0 1).symm
      _ = 0 := h2
  have hb : coordinates X 8 = 0 := by
    have hs := (smul_eq_zero.mp h1').resolve_right (generator_ne_zero 9)
    linarith
  have ha : coordinates X 7 = 0 := by
    have hs := (smul_eq_zero.mp h2').resolve_right (generator_ne_zero 9)
    linarith
  rw [hdec, ha, hb]
  simp

/-- The bracket pairing on the negative degree-one space has zero radical. -/
theorem negative_pairing_nondegenerate (X : Sp) (hX : X ∈ grade (-1))
    (h : ∀ Y ∈ grade (-1), ⁅X, Y⁆ = 0) : X = 0 := by
  have h1 := h v1 (generator_mem_grade 1)
  have h2 := h v2 (generator_mem_grade 2)
  have hdec := grade_neg_one_decomposition X hX
  rw [hdec] at h1 h2
  have h1' : (-2 * coordinates X 2) • zMinus = 0 := by
    calc
      _ = ⁅coordinates X 1 • v1 + coordinates X 2 • v2, v1⁆ := by
        simpa using (negative_bracket (coordinates X 1) (coordinates X 2) 1 0).symm
      _ = 0 := h1
  have h2' : (2 * coordinates X 1) • zMinus = 0 := by
    calc
      _ = ⁅coordinates X 1 • v1 + coordinates X 2 • v2, v2⁆ := by
        simpa using (negative_bracket (coordinates X 1) (coordinates X 2) 0 1).symm
      _ = 0 := h2
  have hb : coordinates X 2 = 0 := by
    have hs := (smul_eq_zero.mp h1').resolve_right (generator_ne_zero 0)
    linarith
  have ha : coordinates X 1 = 0 := by
    have hs := (smul_eq_zero.mp h2').resolve_right (generator_ne_zero 0)
    linarith
  rw [hdec, ha, hb]
  simp

end InfoGeometry.Algebra.Sp4Contact
