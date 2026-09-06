import proofs.SO55HyperbolicDiagonalLieEquiv

/-! # The real split orthogonal group `O(5,5)` -/

noncomputable section
namespace RealOrthogonalGroup55

open SplitOctonionTKK55

/-- The genuine real matrix group preserving the diagonal `(5,5)` metric. -/
def O55 : Subgroup M10ˣ where
  carrier := {g | (g : M10).transpose * eta55 * (g : M10) = eta55}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ((g : M10) * (h : M10)).transpose * eta55 *
      ((g : M10) * (h : M10)) = eta55
    rw [Matrix.transpose_mul]
    calc
      (h : M10).transpose * (g : M10).transpose * eta55 *
          ((g : M10) * (h : M10)) =
        (h : M10).transpose *
          (((g : M10).transpose * eta55 * (g : M10)) * (h : M10)) := by
            simp only [Matrix.mul_assoc]
      _ = (h : M10).transpose * (eta55 * (h : M10)) := by rw [hg]
      _ = eta55 := by simpa only [Matrix.mul_assoc] using hh
  inv_mem' := by
    intro g hg
    let G : M10 := (g : M10)
    let Gi : M10 := (g⁻¹ : M10ˣ)
    have hright : G * Gi = 1 := by
      change ((g * g⁻¹ : M10ˣ) : M10) = 1
      rw [mul_inv_cancel]
      rfl
    have hrightT : Gi.transpose * G.transpose = 1 := by
      rw [← Matrix.transpose_mul, hright, Matrix.transpose_one]
    change Gi.transpose * eta55 * Gi = eta55
    calc
      Gi.transpose * eta55 * Gi =
          Gi.transpose * (G.transpose * eta55 * G) * Gi := by rw [hg]
      _ = eta55 := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Gi.transpose G.transpose, hrightT, one_mul]
        rw [hright, mul_one]

theorem mem_O55_iff (g : M10ˣ) :
    g ∈ O55 ↔ (g : M10).transpose * eta55 * (g : M10) = eta55 :=
  Iff.rfl

/-- The diagonal metric as a native diagonal matrix. -/
theorem eta55_eq_diagonal :
    eta55 = Matrix.diagonal (fun i : Fin 10 => if i.val < 5 then 1 else -1) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [eta55]
  · simp [eta55, Matrix.diagonal, h]

def coordinateReflectionMatrix (i : Fin 10) : M10 :=
  Matrix.diagonal (fun j => if j = i then -1 else 1)

theorem coordinateReflectionMatrix_transpose (i : Fin 10) :
    (coordinateReflectionMatrix i).transpose = coordinateReflectionMatrix i := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [coordinateReflectionMatrix]
  · simp [coordinateReflectionMatrix, Matrix.diagonal, h, Ne.symm h]

theorem coordinateReflectionMatrix_sq (i : Fin 10) :
    coordinateReflectionMatrix i * coordinateReflectionMatrix i = 1 := by
  rw [coordinateReflectionMatrix, Matrix.diagonal_mul_diagonal]
  ext j k
  by_cases hj : j = i <;> by_cases hjk : j = k
  · subst k
    simp [Matrix.diagonal, hj]
  · simp [Matrix.diagonal, hjk]
  · subst k
    simp [Matrix.diagonal, hj]
  · simp [Matrix.diagonal, hjk]

def coordinateReflectionUnit (i : Fin 10) : M10ˣ :=
  ⟨coordinateReflectionMatrix i, coordinateReflectionMatrix i,
    coordinateReflectionMatrix_sq i, coordinateReflectionMatrix_sq i⟩

@[simp] theorem coe_coordinateReflectionUnit (i : Fin 10) :
    (coordinateReflectionUnit i : M10) = coordinateReflectionMatrix i := rfl

theorem coordinateReflection_mem_O55 (i : Fin 10) :
    coordinateReflectionUnit i ∈ O55 := by
  rw [mem_O55_iff, coe_coordinateReflectionUnit,
    coordinateReflectionMatrix_transpose, eta55_eq_diagonal,
    coordinateReflectionMatrix, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  ext j k
  by_cases hj : j = i <;> by_cases hjk : j = k
  · subst k
    by_cases hi : i.val < 5 <;> simp [Matrix.diagonal, hj, hi]
  · simp [Matrix.diagonal, hjk]
  · subst k
    simp [Matrix.diagonal, hj]
  · simp [Matrix.diagonal, hjk]

/-- Every coordinate reflection is orientation reversing. -/
theorem coordinateReflection_det (i : Fin 10) :
    Matrix.det (coordinateReflectionUnit i : M10) = -1 := by
  rw [coe_coordinateReflectionUnit, coordinateReflectionMatrix,
    Matrix.det_diagonal]
  classical
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The native group contains ten explicit generating reflections. -/
theorem coordinate_reflections_complete :
    ∀ i : Fin 10, coordinateReflectionUnit i ∈ O55 :=
  coordinateReflection_mem_O55

end RealOrthogonalGroup55
end noncomputable section
