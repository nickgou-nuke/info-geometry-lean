import InfoGeometry.Canonical.O55OrthogonalLieCarrier

noncomputable section
namespace InfoGeometry.Canonical.O55Representation

open Matrix

abbrev GL10 := Matrix.GeneralLinearGroup (Fin 10) ℝ

def orthogonalGroupPredicate (g : GL10) : Prop :=
  (g : O55Matrix)ᵀ * O55Form * (g : O55Matrix) = O55Form

def OrthogonalGroup55 : Subgroup GL10 where
  carrier := {g | orthogonalGroupPredicate g}
  one_mem' := by simp [orthogonalGroupPredicate]
  mul_mem' := by
    intro g h hg hh
    change ((g * h : GL10) : O55Matrix)ᵀ * O55Form *
      ((g * h : GL10) : O55Matrix) = O55Form
    rw [Units.val_mul, Matrix.transpose_mul]
    calc
      ((h : O55Matrix)ᵀ * (g : O55Matrix)ᵀ * O55Form) *
          ((g : O55Matrix) * (h : O55Matrix)) =
        (h : O55Matrix)ᵀ *
          ((g : O55Matrix)ᵀ * O55Form * (g : O55Matrix)) *
          (h : O55Matrix) := by noncomm_ring
      _ = (h : O55Matrix)ᵀ * O55Form * (h : O55Matrix) := by rw [hg]
      _ = O55Form := hh
  inv_mem' := by
    intro g hg
    change ((g⁻¹ : GL10) : O55Matrix)ᵀ * O55Form *
      ((g⁻¹ : GL10) : O55Matrix) = O55Form
    let gi : O55Matrix := (g⁻¹ : GL10)
    have hleft : (g : O55Matrix) * gi = 1 := by
      dsimp [gi]
      rw [← Units.val_mul]
      simp
    have hright : gi * (g : O55Matrix) = 1 := by
      dsimp [gi]
      rw [← Units.val_mul]
      simp
    calc
      giᵀ * O55Form * gi =
        giᵀ *
          ((g : O55Matrix)ᵀ * O55Form * (g : O55Matrix)) *
          gi := by rw [hg]
      _ = ((g : O55Matrix) * gi)ᵀ * O55Form *
          ((g : O55Matrix) * gi) := by
            rw [Matrix.transpose_mul]
            noncomm_ring
      _ = O55Form := by rw [hleft]; simp

theorem orthogonal55_det_sq_eq_one {g : GL10}
    (hg : orthogonalGroupPredicate g) :
    ((g : O55Matrix).det) ^ 2 = 1 := by
  have hmetric : (O55Form (𝕜 := ℝ)).det ≠ 0 := by
    norm_num [O55Form, Matrix.det_diagonal, Finset.prod_ite]
  have hdet := congrArg Matrix.det hg
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hdet' :
      ((g : O55Matrix).det) ^ 2 * (O55Form (𝕜 := ℝ)).det =
        (O55Form (𝕜 := ℝ)).det := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hdet
  apply mul_right_cancel₀ hmetric
  simpa using hdet'

theorem orthogonal55_det_eq_one_or_neg_one {g : GL10}
    (hg : orthogonalGroupPredicate g) :
    (g : O55Matrix).det = 1 ∨ (g : O55Matrix).det = -1 := by
  exact (sq_eq_one_iff.mp (orthogonal55_det_sq_eq_one hg))

def coordinateReflection : O55Matrix :=
  Matrix.diagonal (fun i : Fin 10 => if i = 0 then (-1 : ℝ) else 1)

theorem coordinateReflection_det_ne_zero :
    coordinateReflection.det ≠ 0 := by
  norm_num [coordinateReflection, Matrix.det_diagonal, Finset.prod_ite]

theorem coordinateReflection_det :
    coordinateReflection.det = -1 := by
  norm_num [coordinateReflection, Matrix.det_diagonal, Finset.prod_ite]

def coordinateReflectionGL : GL10 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero coordinateReflection
    coordinateReflection_det_ne_zero

theorem coordinateReflectionGL_val :
    (coordinateReflectionGL : O55Matrix) = coordinateReflection := by
  rfl

theorem coordinateReflection_sq :
    coordinateReflection * coordinateReflection = (1 : O55Matrix) := by
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i = 0
    · subst i
      simp [coordinateReflection, Matrix.mul_apply, Matrix.diagonal_apply]
    · simp [coordinateReflection, Matrix.mul_apply, Matrix.diagonal_apply, hi]
  · simp [coordinateReflection, Matrix.mul_apply, Matrix.diagonal_apply, h]

theorem coordinateReflection_mem_orthogonal55 :
    orthogonalGroupPredicate coordinateReflectionGL := by
  change (coordinateReflection : O55Matrix)ᵀ * O55Form * coordinateReflection =
    O55Form
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i = 0
    · subst i
      simp [coordinateReflection, O55Form, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.diagonal_apply]
    · simp [coordinateReflection, O55Form, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.diagonal_apply, hi]
  · simp [coordinateReflection, O55Form, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.diagonal_apply, h]

theorem coordinateReflectionGL_mem_OrthogonalGroup55 :
    coordinateReflectionGL ∈ OrthogonalGroup55 :=
  coordinateReflection_mem_orthogonal55

theorem coordinateReflectionGL_det :
    ((coordinateReflectionGL : GL10) : O55Matrix).det = -1 := by
  rw [coordinateReflectionGL_val]
  exact coordinateReflection_det

end InfoGeometry.Canonical.O55Representation
