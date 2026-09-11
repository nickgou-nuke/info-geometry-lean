import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Quantum.KitaevChain

open Matrix

abbrev Pauli4 := Matrix (Fin 4) (Fin 4) ℂ

def pauliMajorana0 : Pauli4 := !![
  0, 0, 1, 0;
  0, 0, 0, 1;
  1, 0, 0, 0;
  0, 1, 0, 0]

def pauliMajorana1 : Pauli4 := !![
  0, 0, -Complex.I, 0;
  0, 0, 0, -Complex.I;
  Complex.I, 0, 0, 0;
  0, Complex.I, 0, 0]

def pauliMajorana2 : Pauli4 := !![
  0, 1, 0, 0;
  1, 0, 0, 0;
  0, 0, 0, -1;
  0, 0, -1, 0]

def pauliMajorana3 : Pauli4 := !![
  0, -Complex.I, 0, 0;
  Complex.I, 0, 0, 0;
  0, 0, 0, Complex.I;
  0, 0, -Complex.I, 0]

theorem pauliMajorana0_sq : pauliMajorana0 * pauliMajorana0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliMajorana1_sq : pauliMajorana1 * pauliMajorana1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana1, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_mul_I]

theorem pauliMajorana2_sq : pauliMajorana2 * pauliMajorana2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliMajorana3_sq : pauliMajorana3 * pauliMajorana3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana3, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_mul_I]

theorem pauliMajorana0_selfAdjoint :
    pauliMajorana0.conjTranspose = pauliMajorana0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliMajorana0, Matrix.conjTranspose_apply]

theorem pauliMajorana1_selfAdjoint :
    pauliMajorana1.conjTranspose = pauliMajorana1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliMajorana1, Matrix.conjTranspose_apply]

theorem pauliMajorana2_selfAdjoint :
    pauliMajorana2.conjTranspose = pauliMajorana2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliMajorana2, Matrix.conjTranspose_apply]

theorem pauliMajorana3_selfAdjoint :
    pauliMajorana3.conjTranspose = pauliMajorana3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliMajorana3, Matrix.conjTranspose_apply]

theorem pauliMajorana01_anticomm :
    pauliMajorana0 * pauliMajorana1 + pauliMajorana1 * pauliMajorana0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliMajorana0, pauliMajorana1]

theorem pauliMajorana02_anticomm :
    pauliMajorana0 * pauliMajorana2 + pauliMajorana2 * pauliMajorana0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana0, pauliMajorana2, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem pauliMajorana03_anticomm :
    pauliMajorana0 * pauliMajorana3 + pauliMajorana3 * pauliMajorana0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana0, pauliMajorana3, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.I_mul_I]

theorem pauliMajorana12_anticomm :
    pauliMajorana1 * pauliMajorana2 + pauliMajorana2 * pauliMajorana1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliMajorana1, pauliMajorana2]

theorem pauliMajorana13_anticomm :
    pauliMajorana1 * pauliMajorana3 + pauliMajorana3 * pauliMajorana1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana1, pauliMajorana3, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.I_mul_I]

theorem pauliMajorana23_anticomm :
    pauliMajorana2 * pauliMajorana3 + pauliMajorana3 * pauliMajorana2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMajorana2, pauliMajorana3, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.I_mul_I]

def pauliMajorana (i : Fin 4) : Pauli4 :=
  ![pauliMajorana0, pauliMajorana1, pauliMajorana2, pauliMajorana3] i

theorem pauliMajorana_selfAdjoint (i : Fin 4) :
    (pauliMajorana i).conjTranspose = pauliMajorana i := by
  fin_cases i
  · exact pauliMajorana0_selfAdjoint
  · exact pauliMajorana1_selfAdjoint
  · exact pauliMajorana2_selfAdjoint
  · exact pauliMajorana3_selfAdjoint

def pauliMajoranaOperators : MajoranaCliffordOperators 2 Pauli4 where
  γ := pauliMajorana
  h_ortho := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [pauliMajorana] at hij ⊢
    · simpa [add_comm] using pauliMajorana01_anticomm
    · simpa [add_comm] using pauliMajorana02_anticomm
    · exact pauliMajorana03_anticomm
    · simpa [add_comm] using pauliMajorana01_anticomm
    · simpa [add_comm] using pauliMajorana12_anticomm
    · simpa [add_comm] using pauliMajorana13_anticomm
    · simpa [add_comm] using pauliMajorana02_anticomm
    · simpa [add_comm] using pauliMajorana12_anticomm
    · exact pauliMajorana23_anticomm
    · simpa [add_comm] using pauliMajorana03_anticomm
    · simpa [add_comm] using pauliMajorana13_anticomm
    · simpa [add_comm] using pauliMajorana23_anticomm
  h_sq := by
    intro i
    fin_cases i
    · exact pauliMajorana0_sq
    · exact pauliMajorana1_sq
    · exact pauliMajorana2_sq
    · exact pauliMajorana3_sq

theorem pauli_outer_product_ne_zero :
    pauliMajorana 0 * pauliMajorana 2 ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Pauli4 => M 0 3) h
  simp [pauliMajorana, pauliMajorana0, pauliMajorana2,
    Matrix.mul_apply, Fin.sum_univ_succ] at hentry

noncomputable def pauliBraidScalar : Pauli4 :=
  (1 / Real.sqrt 2 : ℝ) • (1 : Pauli4)

theorem pauliBraidScalar_central (X : Pauli4) :
    pauliBraidScalar * X = X * pauliBraidScalar := by
  simp [pauliBraidScalar]

theorem pauliBraidScalar_normalized :
    pauliBraidScalar * pauliBraidScalar + pauliBraidScalar * pauliBraidScalar =
      (1 : Pauli4) := by
  have h := real_mem_braidNormalizationLocus
  change (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) +
      (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 at h
  simp only [pauliBraidScalar, smul_mul_smul, mul_one]
  rw [← add_smul, h]
  simp

theorem pauli_braid_commutator_ne_zero :
    braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
        braidOperator pauliBraidScalar pauliMajoranaOperators 1 2 -
      braidOperator pauliBraidScalar pauliMajoranaOperators 1 2 *
        braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 ≠ 0 := by
  apply braid_commutator_ne_zero_of_outer_product_ne_zero pauliBraidScalar
    pauliBraidScalar_central pauliBraidScalar_normalized pauliMajoranaOperators 0 1 2
  · decide
  · decide
  · decide
  · simpa [pauliMajoranaOperators] using pauli_outer_product_ne_zero

theorem pauli_braid_inverse_01 :
    braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
        braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 = 1 ∧
      braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 *
        braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 = 1 := by
  apply braidOperator_inverse_law pauliBraidScalar pauliBraidScalar_central
    pauliBraidScalar_normalized pauliMajoranaOperators 0 1
  · decide
  · decide

theorem pauli_braid_01_conjTranspose :
    (braidOperator pauliBraidScalar pauliMajoranaOperators 0 1).conjTranspose =
      braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 := by
  unfold braidOperator
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_mul]
  change (1 + (pauliMajorana 1).conjTranspose *
      (pauliMajorana 0).conjTranspose) * pauliBraidScalar.conjTranspose =
    pauliBraidScalar * (1 + pauliMajorana 1 * pauliMajorana 0)
  rw [pauliMajorana_selfAdjoint, pauliMajorana_selfAdjoint]
  have hscalar : pauliBraidScalar.conjTranspose = pauliBraidScalar := by
    simp [pauliBraidScalar, Matrix.conjTranspose_smul]
  rw [hscalar]
  rw [← pauliBraidScalar_central
    (1 + pauliMajorana 1 * pauliMajorana 0)]

theorem pauli_braid_01_mem_unitary :
    braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 ∈
      Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (braidOperator pauliBraidScalar pauliMajoranaOperators 0 1).conjTranspose *
      braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 = 1
  rw [pauli_braid_01_conjTranspose]
  exact pauli_braid_inverse_01.2

theorem pauli_braid_10_conjTranspose :
    (braidOperator pauliBraidScalar pauliMajoranaOperators 1 0).conjTranspose =
      braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 := by
  have h := congrArg Matrix.conjTranspose pauli_braid_01_conjTranspose
  simpa only [Matrix.conjTranspose_conjTranspose] using h.symm

theorem pauli_braid_10_mem_unitary :
    braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 ∈
      Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (braidOperator pauliBraidScalar pauliMajoranaOperators 1 0).conjTranspose *
      braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 = 1
  rw [pauli_braid_10_conjTranspose]
  exact pauli_braid_inverse_01.1

noncomputable def pauliBraidGate01 : Matrix.unitaryGroup (Fin 4) ℂ :=
  ⟨braidOperator pauliBraidScalar pauliMajoranaOperators 0 1,
    pauli_braid_01_mem_unitary⟩

noncomputable def pauliBraidGate10 : Matrix.unitaryGroup (Fin 4) ℂ :=
  ⟨braidOperator pauliBraidScalar pauliMajoranaOperators 1 0,
    pauli_braid_10_mem_unitary⟩

@[simp] theorem coe_pauliBraidGate01 :
    (pauliBraidGate01 : Pauli4) =
      braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 := rfl

@[simp] theorem coe_pauliBraidGate10 :
    (pauliBraidGate10 : Pauli4) =
      braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 := rfl

theorem pauliBraidGate01_mul_gate10 :
    pauliBraidGate01 * pauliBraidGate10 = (1 : Matrix.unitaryGroup (Fin 4) ℂ) := by
  apply Subtype.ext
  change braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
      braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 = 1
  exact pauli_braid_inverse_01.1

theorem pauliBraidGate10_mul_gate01 :
    pauliBraidGate10 * pauliBraidGate01 = (1 : Matrix.unitaryGroup (Fin 4) ℂ) := by
  apply Subtype.ext
  change braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 *
      braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 = 1
  exact pauli_braid_inverse_01.2

theorem pauliBraidGate01_inv :
    pauliBraidGate01⁻¹ = pauliBraidGate10 := by
  exact inv_eq_of_mul_eq_one_right pauliBraidGate01_mul_gate10

theorem pauliBraidGate10_inv :
    pauliBraidGate10⁻¹ = pauliBraidGate01 := by
  exact inv_eq_of_mul_eq_one_right pauliBraidGate10_mul_gate01

theorem pauli_braid_conjugates_left_01 :
    braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
        pauliMajorana 0 *
          braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 =
      -pauliMajorana 1 := by
  exact braidOperator_conjugates_left pauliBraidScalar
    pauliBraidScalar_central pauliBraidScalar_normalized
    pauliMajoranaOperators 0 1 (by decide)

theorem pauli_braid_conjugates_right_01 :
    braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
        pauliMajorana 1 *
          braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 =
      pauliMajorana 0 := by
  exact braidOperator_conjugates_right pauliBraidScalar
    pauliBraidScalar_central pauliBraidScalar_normalized
    pauliMajoranaOperators 0 1 (by decide)

theorem pauliBraidGate01_conjugates_left :
    (pauliBraidGate01 : Pauli4) * pauliMajorana 0 *
        (pauliBraidGate10 : Pauli4) = -pauliMajorana 1 := by
  simpa using pauli_braid_conjugates_left_01

theorem pauliBraidGate01_conjugates_right :
    (pauliBraidGate01 : Pauli4) * pauliMajorana 1 *
        (pauliBraidGate10 : Pauli4) = pauliMajorana 0 := by
  simpa using pauli_braid_conjugates_right_01

theorem pauliBraidGate10_conjugates_left :
    (pauliBraidGate10 : Pauli4) * pauliMajorana 1 *
        (pauliBraidGate01 : Pauli4) = -pauliMajorana 0 := by
  exact braidOperator_conjugates_left pauliBraidScalar
    pauliBraidScalar_central pauliBraidScalar_normalized
    pauliMajoranaOperators 1 0 (by decide)

theorem pauliBraidGate10_conjugates_right :
    (pauliBraidGate10 : Pauli4) * pauliMajorana 0 *
        (pauliBraidGate01 : Pauli4) = pauliMajorana 1 := by
  exact braidOperator_conjugates_right pauliBraidScalar
    pauliBraidScalar_central pauliBraidScalar_normalized
    pauliMajoranaOperators 1 0 (by decide)

noncomputable def pauliUnitaryConjugation
    (g : Matrix.unitaryGroup (Fin 4) ℂ) (x : Pauli4) : Pauli4 :=
  (g : Pauli4) * x * star (g : Pauli4)

theorem continuous_pauliUnitaryConjugation (x : Pauli4) :
    Continuous (fun g : Matrix.unitaryGroup (Fin 4) ℂ =>
      pauliUnitaryConjugation g x) := by
  unfold pauliUnitaryConjugation
  exact (continuous_mul.comp
    ((continuous_subtype_val.prodMk continuous_const))).mul
    (continuous_star.comp continuous_subtype_val)

theorem pauliUnitaryConjugation_gate01_left :
    pauliUnitaryConjugation pauliBraidGate01 (pauliMajorana 0) =
      -pauliMajorana 1 := by
  change braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
      pauliMajorana 0 *
        (braidOperator pauliBraidScalar pauliMajoranaOperators 0 1).conjTranspose =
      -pauliMajorana 1
  rw [pauli_braid_01_conjTranspose]
  exact pauliBraidGate01_conjugates_left

theorem pauliUnitaryConjugation_gate01_right :
    pauliUnitaryConjugation pauliBraidGate01 (pauliMajorana 1) =
      pauliMajorana 0 := by
  change braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
      pauliMajorana 1 *
        (braidOperator pauliBraidScalar pauliMajoranaOperators 0 1).conjTranspose =
      pauliMajorana 0
  rw [pauli_braid_01_conjTranspose]
  exact pauliBraidGate01_conjugates_right

theorem continuous_pauli_braid_conjugation_01 :
    Continuous (fun r : Pauli4 =>
      braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 0 *
        braidOperator r pauliMajoranaOperators 1 0) := by
  exact (continuous_braidOperator pauliMajoranaOperators 0 1).mul
    continuous_const |>.mul (continuous_braidOperator pauliMajoranaOperators 1 0)

def pauliNormalizedScalarSet : Set Pauli4 :=
  {pauliBraidScalar, -pauliBraidScalar}

theorem pauliNormalizedScalarSet_isCompact :
    IsCompact pauliNormalizedScalarSet := by
  rw [pauliNormalizedScalarSet]
  exact (Set.Finite.insert _ (Set.finite_singleton _)).isCompact

theorem pauliNormalizedScalarSet_subset_braidNormalizationLocus :
    pauliNormalizedScalarSet ⊆ braidNormalizationLocus (A := Pauli4) := by
  intro r hr
  rcases hr with (rfl | rfl)
  · exact pauliBraidScalar_normalized
  · change (-pauliBraidScalar) * (-pauliBraidScalar) +
      (-pauliBraidScalar) * (-pauliBraidScalar) = (1 : Pauli4)
    simpa only [neg_mul_neg] using pauliBraidScalar_normalized

theorem compact_pauli_braid_conjugation_image :
    IsCompact ((fun r : Pauli4 =>
      braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 0 *
        braidOperator r pauliMajoranaOperators 1 0) ''
      pauliNormalizedScalarSet) := by
  exact pauliNormalizedScalarSet_isCompact.image
    continuous_pauli_braid_conjugation_01

theorem pauli_braid_conjugation_image_eq_singleton :
    (fun r : Pauli4 =>
      braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 0 *
        braidOperator r pauliMajoranaOperators 1 0) ''
      pauliNormalizedScalarSet = {-pauliMajorana 1} := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with (rfl | rfl)
    · simpa using pauli_braid_conjugates_left_01
    · have hleft :
          braidOperator (-pauliBraidScalar) pauliMajoranaOperators 0 1 =
            -braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 := by
        unfold braidOperator
        noncomm_ring
      have hright :
          braidOperator (-pauliBraidScalar) pauliMajoranaOperators 1 0 =
            -braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 := by
        unfold braidOperator
        noncomm_ring
      change braidOperator (-pauliBraidScalar) pauliMajoranaOperators 0 1 *
          pauliMajorana 0 *
            braidOperator (-pauliBraidScalar) pauliMajoranaOperators 1 0 ∈
          {-pauliMajorana 1}
      rw [hleft, hright]
      simpa using pauli_braid_conjugates_left_01
  · intro hy
    have hy' : y = -pauliMajorana 1 := by simpa using hy
    subst y
    refine ⟨pauliBraidScalar, ?_, ?_⟩
    · exact (by simp [pauliNormalizedScalarSet])
    · exact pauli_braid_conjugates_left_01

theorem pauli_braid_right_conjugation_image_eq_singleton :
    (fun r : Pauli4 =>
      braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 1 *
        braidOperator r pauliMajoranaOperators 1 0) ''
      pauliNormalizedScalarSet = {pauliMajorana 0} := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with (rfl | rfl)
    · simpa using pauli_braid_conjugates_right_01
    · have hleft :
          braidOperator (-pauliBraidScalar) pauliMajoranaOperators 0 1 =
            -braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 := by
        unfold braidOperator
        noncomm_ring
      have hright :
          braidOperator (-pauliBraidScalar) pauliMajoranaOperators 1 0 =
            -braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 := by
        unfold braidOperator
        noncomm_ring
      change braidOperator (-pauliBraidScalar) pauliMajoranaOperators 0 1 *
          pauliMajorana 1 *
            braidOperator (-pauliBraidScalar) pauliMajoranaOperators 1 0 ∈
          {pauliMajorana 0}
      rw [hleft, hright]
      simpa using pauli_braid_conjugates_right_01
  · intro hy
    have hy' : y = pauliMajorana 0 := by simpa using hy
    subst y
    refine ⟨pauliBraidScalar, ?_, ?_⟩
    · exact (by simp [pauliNormalizedScalarSet])
    · exact pauli_braid_conjugates_right_01

theorem compact_pauli_braid_right_conjugation_image :
    IsCompact ((fun r : Pauli4 =>
      braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 1 *
        braidOperator r pauliMajoranaOperators 1 0) ''
      pauliNormalizedScalarSet) := by
  rw [pauli_braid_right_conjugation_image_eq_singleton]
  exact isCompact_singleton

noncomputable def pauliBraidConjugationPair (r : Pauli4) : Pauli4 × Pauli4 :=
  (braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 0 *
      braidOperator r pauliMajoranaOperators 1 0,
    braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 1 *
      braidOperator r pauliMajoranaOperators 1 0)

theorem pauliBraidConjugationPair_neg (r : Pauli4) :
    pauliBraidConjugationPair (-r) = pauliBraidConjugationPair r := by
  unfold pauliBraidConjugationPair braidOperator
  noncomm_ring

def pauliBraidSignRel (r s : Pauli4) : Prop := s = r ∨ s = -r

instance pauliBraidSignSetoid : Setoid Pauli4 where
  r := pauliBraidSignRel
  iseqv := {
    refl := by
      intro r
      exact Or.inl rfl
    symm := by
      intro r s hrs
      rcases hrs with hrs | hrs
      · exact Or.inl hrs.symm
      · right
        rw [hrs]
        simp
    trans := by
      intro r s t hrs hst
      rcases hrs with hrs | hrs <;> rcases hst with hst | hst
      · subst s
        exact Or.inl hst
      · subst s
        exact Or.inr hst
      · subst s
        exact Or.inr hst
      · subst s
        rw [neg_neg] at hst
        exact Or.inl hst
  }

abbrev PauliBraidSignQuotient := Quotient pauliBraidSignSetoid

noncomputable def pauliBraidConjugationQuotient :
    PauliBraidSignQuotient → Pauli4 × Pauli4 :=
  Quotient.lift pauliBraidConjugationPair (by
    intro r s hrs
    rcases hrs with hrs | hrs
    · subst s
      rfl
    · subst s
      exact (pauliBraidConjugationPair_neg r).symm)

@[simp] theorem pauliBraidConjugationQuotient_mk (r : Pauli4) :
    pauliBraidConjugationQuotient (Quotient.mk' r) =
      pauliBraidConjugationPair r := rfl

theorem continuous_pauliBraidConjugationPair :
    Continuous pauliBraidConjugationPair := by
  have hright : Continuous (fun r : Pauli4 =>
      braidOperator r pauliMajoranaOperators 0 1 * pauliMajorana 1 *
        braidOperator r pauliMajoranaOperators 1 0) :=
    (continuous_braidOperator pauliMajoranaOperators 0 1).mul continuous_const |>.mul
      (continuous_braidOperator pauliMajoranaOperators 1 0)
  exact Continuous.prodMk continuous_pauli_braid_conjugation_01 hright

theorem continuous_pauliBraidConjugationQuotient :
    Continuous pauliBraidConjugationQuotient := by
  exact continuous_pauliBraidConjugationPair.quotient_lift (by
    intro r s hrs
    rcases hrs with hrs | hrs
    · subst s
      rfl
    · subst s
      exact (pauliBraidConjugationPair_neg r).symm)

def pauliNormalizedSignQuotientSet : Set PauliBraidSignQuotient :=
  (Quotient.mk' : Pauli4 → PauliBraidSignQuotient) ''
    pauliNormalizedScalarSet

theorem pauliNormalizedSignQuotientSet_eq_singleton :
    pauliNormalizedSignQuotientSet =
      {Quotient.mk' pauliBraidScalar} := by
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with (rfl | rfl)
    · rfl
    · rw [Set.mem_singleton_iff]
      apply Quotient.sound
      right
      simp
  · intro hq
    have hq' : q = Quotient.mk' pauliBraidScalar := by
      simpa using hq
    subst q
    exact ⟨pauliBraidScalar, by simp [pauliNormalizedScalarSet], rfl⟩

theorem pauliBraidConjugationQuotient_image_eq_pair_image :
    pauliBraidConjugationQuotient '' pauliNormalizedSignQuotientSet =
      pauliBraidConjugationPair '' pauliNormalizedScalarSet := by
  ext y
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨Quotient.mk' r, ⟨r, hr, rfl⟩, rfl⟩

theorem compact_pauliNormalizedSignQuotientSet :
    IsCompact pauliNormalizedSignQuotientSet := by
  exact pauliNormalizedScalarSet_isCompact.image continuous_quotient_mk'

theorem pauliBraidConjugationQuotient_normalized_image_eq_singleton :
    pauliBraidConjugationQuotient '' pauliNormalizedSignQuotientSet =
      {(-pauliMajorana 1, pauliMajorana 0)} := by
  ext y
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    change pauliBraidConjugationPair r ∈
      {(-pauliMajorana 1, pauliMajorana 0)}
    rcases hr with (rfl | rfl)
    · rw [Set.mem_singleton_iff]
      exact Prod.ext (by simpa using pauli_braid_conjugates_left_01)
        (by simpa using pauli_braid_conjugates_right_01)
    · rw [pauliBraidConjugationPair_neg]
      rw [Set.mem_singleton_iff]
      exact Prod.ext (by simpa using pauli_braid_conjugates_left_01)
        (by simpa using pauli_braid_conjugates_right_01)
  · intro hy
    have hy' : y = (-pauliMajorana 1, pauliMajorana 0) := by
      simpa using hy
    subst y
    refine ⟨Quotient.mk' pauliBraidScalar, ?_, ?_⟩
    · exact ⟨pauliBraidScalar, by simp [pauliNormalizedScalarSet], rfl⟩
    · exact pauliBraidConjugationQuotient_mk pauliBraidScalar ▸
        Prod.ext pauli_braid_conjugates_left_01
          pauli_braid_conjugates_right_01

theorem compact_pauliBraidConjugationQuotient_normalized_image :
    IsCompact
      (pauliBraidConjugationQuotient '' pauliNormalizedSignQuotientSet) := by
  exact compact_pauliNormalizedSignQuotientSet.image
    continuous_pauliBraidConjugationQuotient

theorem pauliBraidConjugationPair_image_eq_singleton :
    pauliBraidConjugationPair '' pauliNormalizedScalarSet =
      {(-pauliMajorana 1, pauliMajorana 0)} := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with (rfl | rfl)
    · rw [Set.mem_singleton_iff]
      exact Prod.ext (by simpa using pauli_braid_conjugates_left_01)
        (by simpa using pauli_braid_conjugates_right_01)
    · have hleft :
          braidOperator (-pauliBraidScalar) pauliMajoranaOperators 0 1 =
            -braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 := by
        unfold braidOperator
        noncomm_ring
      have hright :
          braidOperator (-pauliBraidScalar) pauliMajoranaOperators 1 0 =
            -braidOperator pauliBraidScalar pauliMajoranaOperators 1 0 := by
        unfold braidOperator
        noncomm_ring
      change (braidOperator (-pauliBraidScalar) pauliMajoranaOperators 0 1 *
          pauliMajorana 0 *
            braidOperator (-pauliBraidScalar) pauliMajoranaOperators 1 0,
        braidOperator (-pauliBraidScalar) pauliMajoranaOperators 0 1 *
          pauliMajorana 1 *
            braidOperator (-pauliBraidScalar) pauliMajoranaOperators 1 0) ∈
          {(-pauliMajorana 1, pauliMajorana 0)}
      rw [hleft, hright]
      rw [Set.mem_singleton_iff]
      exact Prod.ext (by simpa using pauli_braid_conjugates_left_01)
        (by simpa using pauli_braid_conjugates_right_01)
  · intro hy
    have hy' : y = (-pauliMajorana 1, pauliMajorana 0) := by
      simpa using hy
    subst y
    refine ⟨pauliBraidScalar, ?_, ?_⟩
    · exact (by simp [pauliNormalizedScalarSet])
    · change (braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
        pauliMajorana 0 * braidOperator pauliBraidScalar pauliMajoranaOperators 1 0,
      braidOperator pauliBraidScalar pauliMajoranaOperators 0 1 *
        pauliMajorana 1 * braidOperator pauliBraidScalar pauliMajoranaOperators 1 0) =
        (-pauliMajorana 1, pauliMajorana 0)
      exact Prod.ext pauli_braid_conjugates_left_01
        pauli_braid_conjugates_right_01

theorem compact_pauliBraidConjugationPair_image :
    IsCompact (pauliBraidConjugationPair '' pauliNormalizedScalarSet) := by
  rw [pauliBraidConjugationPair_image_eq_singleton]
  exact isCompact_singleton

end InfoGeometry.Quantum.KitaevChain
