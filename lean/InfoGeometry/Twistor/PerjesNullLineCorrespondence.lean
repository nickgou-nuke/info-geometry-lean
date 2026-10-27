import InfoGeometry.Twistor.PerjesConventions

/-!
# Real null lines as complete Hermitian incidence fibers

Given a Hermitian incident base point and a nonzero lower spinor, every
Hermitian point with the same incidence lies on one explicit real affine
null line. This classifies the entire fiber. Existence of an incident base
point for arbitrary null twistor data is a separate result.
-/

noncomputable section
namespace InfoGeometry.Twistor.PerjesNullLineCorrespondence

open Matrix
open scoped BigOperators
open PenroseIncidence PerjesConventions

def spinorNormSq (π : Spinor2) : ℝ := Complex.normSq (π 0) + Complex.normSq (π 1)

def orthogonalSpinor (π : Spinor2) : Spinor2 := ![-star (π 1), star (π 0)]

def rayDirection (π : Spinor2) : ComplexSpacetime :=
  vecMulVec (orthogonalSpinor π) (star (orthogonalSpinor π))

theorem spinorNormSq_pos (π : Spinor2) (hπ : π ≠ 0) : 0 < spinorNormSq π := by
  have h0 := Complex.normSq_nonneg (π 0)
  have h1 := Complex.normSq_nonneg (π 1)
  have hn : spinorNormSq π ≠ 0 := by
    intro h
    have hz0 : Complex.normSq (π 0) = 0 := by dsimp [spinorNormSq] at h; linarith
    have hz1 : Complex.normSq (π 1) = 0 := by dsimp [spinorNormSq] at h; linarith
    apply hπ
    funext i
    fin_cases i
    · exact Complex.normSq_eq_zero.mp hz0
    · exact Complex.normSq_eq_zero.mp hz1
  exact lt_of_le_of_ne (add_nonneg h0 h1) (Ne.symm hn)

theorem spinorNormSq_cast (π : Spinor2) :
    (spinorNormSq π : ℂ) = π 0 * star (π 0) + π 1 * star (π 1) := by
  simp [spinorNormSq, Complex.normSq_eq_conj_mul_self, mul_comm]

theorem rayDirection_hermitian (π : Spinor2) : (rayDirection π)ᴴ = rayDirection π := by
  ext i j
  simp [rayDirection, vecMulVec, mul_comm]

theorem rayDirection_annihilates (π : Spinor2) : (rayDirection π).mulVec π = 0 := by
  funext i
  fin_cases i <;>
    simp [rayDirection, orthogonalSpinor, vecMulVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem rayDirection_null (π : Spinor2) : (rayDirection π).det = 0 := by
  simp [rayDirection, vecMulVec, Matrix.det_fin_two]
  ring

theorem trace_rayDirection (π : Spinor2) :
    Matrix.trace (rayDirection π) = (spinorNormSq π : ℂ) := by
  rw [spinorNormSq_cast]
  simp [rayDirection, orthogonalSpinor, Matrix.trace, vecMulVec, Fin.sum_univ_two]
  ring

theorem rayDirection_ne_zero (π : Spinor2) (hπ : π ≠ 0) : rayDirection π ≠ 0 := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [trace_rayDirection] at ht
  have hz : spinorNormSq π = 0 := by simpa using ht
  exact (ne_of_gt (spinorNormSq_pos π hπ)) hz

theorem incidence_equal_iff (X Y : ComplexSpacetime) (π : Spinor2) :
    incidenceLinearMap X π = incidenceLinearMap Y π ↔ (X - Y).mulVec π = 0 := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hxy : X.mulVec π = Y.mulVec π := by
      simpa [incidenceLinearMap, omegaLinearMap] using hfst
    simp [Matrix.sub_mulVec, hxy]
  · intro h
    have hxy : X.mulVec π = Y.mulVec π := sub_eq_zero.mp (by
      simpa [Matrix.sub_mulVec] using h)
    simp [incidenceLinearMap, omegaLinearMap, hxy]

/-- Complete matrix identity underlying the real fiber classification. -/
theorem hermitian_kernel_formula (D : ComplexSpacetime) (π : Spinor2)
    (hD : Dᴴ = D) (hker : D.mulVec π = 0) :
    (spinorNormSq π : ℂ) • D = Matrix.trace D • rayDirection π := by
  have r0 : D 0 0 * π 0 + D 0 1 * π 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hker 0
  have r1 : D 1 0 * π 0 + D 1 1 * π 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hker 1
  have hd (i j : Fin 2) : star (D j i) = D i j := congrFun (congrFun hD i) j
  have c0 : star (π 0) * D 0 0 + star (π 1) * D 1 0 = 0 := by
    have hh := congrArg star r0
    simpa [hd, mul_comm] using hh
  have c1 : star (π 0) * D 0 1 + star (π 1) * D 1 1 = 0 := by
    have hh := congrArg star r1
    simpa [hd, mul_comm] using hh
  change (starRingEnd ℂ) (π 0) * D 0 0 + (starRingEnd ℂ) (π 1) * D 1 0 = 0 at c0
  change (starRingEnd ℂ) (π 0) * D 0 1 + (starRingEnd ℂ) (π 1) * D 1 1 = 0 at c1
  rw [spinorNormSq_cast]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rayDirection, orthogonalSpinor, Matrix.trace, vecMulVec, Fin.sum_univ_two,
      smul_eq_mul]
  · linear_combination (starRingEnd ℂ) (π 0) * r0 - π 1 * c1
  · linear_combination (starRingEnd ℂ) (π 1) * r0 + π 0 * c1
  · linear_combination (starRingEnd ℂ) (π 0) * r1 + π 1 * c0
  · linear_combination (starRingEnd ℂ) (π 1) * r1 - π 0 * c0

theorem hermitian_trace_real (D : ComplexSpacetime) (hD : Dᴴ = D) :
    ((Matrix.trace D).re : ℂ) = Matrix.trace D := by
  have h0 := congrArg Complex.im (congrFun (congrFun hD 0) 0)
  have h1 := congrArg Complex.im (congrFun (congrFun hD 1) 1)
  simp at h0 h1
  apply Complex.ext
  · simp
  · simp [Matrix.trace, Fin.sum_univ_two]
    linarith

theorem hermitian_kernel_real_span (D : ComplexSpacetime) (π : Spinor2)
    (hπ : π ≠ 0) (hD : Dᴴ = D) (hker : D.mulVec π = 0) :
    ∃ t : ℝ, D = (t : ℂ) • rayDirection π := by
  have hn : (spinorNormSq π : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (spinorNormSq_pos π hπ)
  have hf := hermitian_kernel_formula D π hD hker
  have hh := congrArg (fun M : ComplexSpacetime => (spinorNormSq π : ℂ)⁻¹ • M) hf
  refine ⟨(Matrix.trace D).re / spinorNormSq π, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at hh
  simpa only [Complex.ofReal_div, hermitian_trace_real D hD, div_eq_mul_inv,
    mul_comm, smul_smul] using hh

/-- The entire Hermitian incidence fiber is a real affine null line. -/
theorem real_incidence_fiber (X Y : ComplexSpacetime) (hX : Xᴴ = X)
    (π : Spinor2) (hπ : π ≠ 0) :
    (Yᴴ = Y ∧ incidenceLinearMap Y π = incidenceLinearMap X π) ↔
      ∃ t : ℝ, Y = X + (t : ℂ) • rayDirection π := by
  constructor
  · rintro ⟨hY, hinc⟩
    have hD : (Y - X)ᴴ = Y - X := by simp [hY, hX]
    obtain ⟨t, ht⟩ := hermitian_kernel_real_span (Y - X) π hπ hD
      ((incidence_equal_iff Y X π).mp hinc)
    exact ⟨t, by rw [← ht]; abel⟩
  · rintro ⟨t, rfl⟩
    constructor
    · simp [Matrix.conjTranspose_smul, hX, rayDirection_hermitian]
    · apply (incidence_equal_iff _ _ π).mpr
      simp [Matrix.smul_mulVec, rayDirection_annihilates]

theorem real_ray_parameter_unique (X : ComplexSpacetime) (π : Spinor2)
    (hπ : π ≠ 0) (s t : ℝ)
    (h : X + (s : ℂ) • rayDirection π = X + (t : ℂ) • rayDirection π) : s = t := by
  have hst := add_left_cancel h
  have hc : (s : ℂ) = (t : ℂ) := (smul_left_injective ℂ (rayDirection_ne_zero π hπ)) hst
  exact_mod_cast hc

end InfoGeometry.Twistor.PerjesNullLineCorrespondence
