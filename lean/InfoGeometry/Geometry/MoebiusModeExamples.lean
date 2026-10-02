import InfoGeometry.Geometry.MoebiusConjugacyClassification
import InfoGeometry.Canonical.MoebiusDiscriminantBridge
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Geometry.MoebiusModeExamples

def parabolicExample : SL2C :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two]⟩

def ellipticExample : SL2C :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

def hyperbolicExample : SL2C :=
  ⟨!![2, 0; 0, 1 / 2], by norm_num [Matrix.det_fin_two]⟩

def loxodromicExample : SL2C :=
  ⟨!![⟨2, 1⟩, 0; 0, ⟨2 / 5, -1 / 5⟩], by
    apply Complex.ext <;> norm_num [Matrix.det_fin_two, Complex.mul_re, Complex.mul_im]⟩

theorem parabolicExample_isParabolic : IsParabolic parabolicExample := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [traceSq, parabolicExample, Matrix.trace, Fin.sum_univ_two]
  · intro hequal
    have hentry := congrArg (fun matrix : MobiusMatrix => matrix 0 1) hequal
    norm_num [parabolicExample] at hentry
  · intro hequal
    have hentry := congrArg (fun matrix : MobiusMatrix => matrix 0 1) hequal
    norm_num [parabolicExample] at hentry

theorem ellipticExample_isElliptic : IsElliptic ellipticExample := by
  refine ⟨0, le_rfl, by norm_num, ?_⟩
  norm_num [traceSq, ellipticExample, Matrix.trace, Fin.sum_univ_two]

theorem hyperbolicExample_isHyperbolic : IsHyperbolic hyperbolicExample := by
  refine ⟨25 / 4, by norm_num, ?_⟩
  norm_num [traceSq, hyperbolicExample, Matrix.trace, Fin.sum_univ_two]

theorem loxodromic_of_traceSq_im_ne_zero (matrix : SL2C)
    (hnonreal : (traceSq matrix).im ≠ 0) : IsLoxodromic matrix := by
  refine ⟨?_, ?_, ?_⟩
  · intro hequal
    apply hnonreal
    rw [hequal]
    norm_num
  · rintro ⟨value, _, _, hequal⟩
    apply hnonreal
    rw [hequal]
    rfl
  · rintro ⟨value, _, hequal⟩
    apply hnonreal
    rw [hequal]
    rfl

theorem loxodromicExample_traceSq_im : (traceSq loxodromicExample).im = 96 / 25 := by
  norm_num [traceSq, loxodromicExample, Matrix.trace, Fin.sum_univ_two,
    pow_two, Complex.mul_re, Complex.mul_im]

theorem loxodromicExample_isLoxodromic : IsLoxodromic loxodromicExample := by
  apply loxodromic_of_traceSq_im_ne_zero
  rw [loxodromicExample_traceSq_im]
  norm_num

def realDiscriminantLoxodromicExample : SL2C :=
  ⟨!![⟨0, 2⟩, 0; 0, ⟨0, -1 / 2⟩], by
    apply Complex.ext <;> norm_num [Matrix.det_fin_two, Complex.mul_re, Complex.mul_im]⟩

theorem realDiscriminantLoxodromicExample_traceSq :
    traceSq realDiscriminantLoxodromicExample = (-9 / 4 : ℂ) := by
  apply Complex.ext <;> norm_num [traceSq, realDiscriminantLoxodromicExample, Matrix.trace,
    Fin.sum_univ_two, pow_two, Complex.mul_re, Complex.mul_im]

theorem realDiscriminantLoxodromicExample_isLoxodromic :
    IsLoxodromic realDiscriminantLoxodromicExample := by
  refine ⟨?_, ?_, ?_⟩
  · rw [realDiscriminantLoxodromicExample_traceSq]
    norm_num
  · rintro ⟨value, hnonnegative, _, hequal⟩
    rw [realDiscriminantLoxodromicExample_traceSq] at hequal
    have hreal := congrArg Complex.re hequal
    norm_num at hreal
    linarith
  · rintro ⟨value, hlarge, hequal⟩
    rw [realDiscriminantLoxodromicExample_traceSq] at hequal
    have hreal := congrArg Complex.re hequal
    norm_num at hreal
    linarith

theorem loxodromic_can_have_real_negative_discriminant :
    IsLoxodromic realDiscriminantLoxodromicExample ∧
      traceSq realDiscriminantLoxodromicExample - 4 = (-25 / 4 : ℂ) := by
  refine ⟨realDiscriminantLoxodromicExample_isLoxodromic, ?_⟩
  rw [realDiscriminantLoxodromicExample_traceSq]
  norm_num

theorem reciprocal_discriminant (value : ℂ) (hnonzero : value ≠ 0) :
    Canonical.moebiusDiscriminant value value⁻¹ = (value - value⁻¹) ^ 2 := by
  calc
    Canonical.moebiusDiscriminant value value⁻¹ =
        (value⁻¹ - value) ^ 2 + 4 * 0 * 0 :=
      Canonical.moebius_discriminant_eq_fixed_point_disc value 0 0 value⁻¹
        (by simp [hnonzero])
    _ = (value - value⁻¹) ^ 2 := by ring

def polarMatrix (radius angle : ℝ) : MobiusMatrix :=
  !![⟨radius * Real.cos angle, radius * Real.sin angle⟩, 0;
     0, ⟨radius⁻¹ * Real.cos angle, -(radius⁻¹ * Real.sin angle)⟩]

theorem polarMatrix_det (radius angle : ℝ) (hnonzero : radius ≠ 0) :
    (polarMatrix radius angle).det = 1 := by
  simp only [polarMatrix, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero, sub_zero]
  apply Complex.ext
  · change (radius * Real.cos angle) * (radius⁻¹ * Real.cos angle) -
        (radius * Real.sin angle) * -(radius⁻¹ * Real.sin angle) = 1
    calc
      _ = (radius * radius⁻¹) *
          (Real.cos angle ^ 2 + Real.sin angle ^ 2) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hnonzero, Real.cos_sq_add_sin_sq]; simp
  · change (radius * Real.cos angle) * -(radius⁻¹ * Real.sin angle) +
        (radius * Real.sin angle) * (radius⁻¹ * Real.cos angle) = 0
    ring

theorem polarMatrix_trace (radius angle : ℝ) :
    (polarMatrix radius angle).trace =
      (⟨(radius + radius⁻¹) * Real.cos angle,
        (radius - radius⁻¹) * Real.sin angle⟩ : ℂ) := by
  apply Complex.ext <;> simp [polarMatrix, Matrix.trace, Fin.sum_univ_two] <;> ring

theorem polarMatrix_discriminant_im (radius angle : ℝ) :
    ((polarMatrix radius angle).trace ^ 2 - 4).im =
      (radius ^ 2 - (radius⁻¹) ^ 2) * Real.sin (2 * angle) := by
  rw [polarMatrix_trace, Real.sin_two_mul]
  simp [pow_two, Complex.mul_im]
  ring

theorem polarMatrix_discriminant_im_ne_zero (radius angle : ℝ)
    (hradius : 1 < radius) (hphase : Real.sin (2 * angle) ≠ 0) :
    ((polarMatrix radius angle).trace ^ 2 - 4).im ≠ 0 := by
  rw [polarMatrix_discriminant_im]
  apply mul_ne_zero _ hphase
  have hpositive : 0 < radius := by linarith
  have hproduct := mul_inv_cancel₀ (ne_of_gt hpositive)
  have hinverse : 0 < radius⁻¹ := inv_pos.mpr hpositive
  have hinverse_lt : radius⁻¹ < 1 := by nlinarith
  have hgap : 0 < radius ^ 2 - (radius⁻¹) ^ 2 := by nlinarith
  exact ne_of_gt hgap

theorem polarMatrix_isLoxodromic (radius angle : ℝ)
    (hradius : 1 < radius) (hphase : Real.sin (2 * angle) ≠ 0) :
    IsLoxodromic
      ⟨polarMatrix radius angle, polarMatrix_det radius angle (by linarith)⟩ := by
  apply loxodromic_of_traceSq_im_ne_zero
  simpa [traceSq] using
    polarMatrix_discriminant_im_ne_zero radius angle hradius hphase

end InfoGeometry.Geometry.MoebiusModeExamples
