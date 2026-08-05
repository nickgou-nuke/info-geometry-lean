import InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
import InfoGeometry.Clifford.Cl11Matrix

noncomputable section

namespace InfoGeometry.Canonical.CantorLocalCl11Universal

open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
open InfoGeometry.Clifford.Cl11Matrix

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

noncomputable def cl11Generator
    (positive negative : Op) : (ℝ × ℝ) →ₗ[ℝ] Op where
  toFun v := v.1 • positive + v.2 • negative
  map_add' u v := by
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' a v := by
    simp [smul_add, smul_smul]

theorem cl11Generator_sq
    (positive negative : Op)
    (h : CantorBinaryTiltCARCCRBridge.IsLocalCl11Relation positive negative)
    (v : ℝ × ℝ) :
    cl11Generator positive negative v * cl11Generator positive negative v =
      algebraMap ℝ Op (q11 v) := by
  rcases v with ⟨a, b⟩
  dsimp [cl11Generator]
  rw [q11_apply]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h.1, h.2.1]
  simp only [smul_add, smul_smul]
  have hcross :
      (a * b : ℝ) • (positive * negative) +
          (b * a : ℝ) • (negative * positive) = 0 := by
    rw [show b * a = a * b by ring]
    rw [← smul_add, h.2.2]
    simp
  let hcrossExpr : Op :=
    (a * b : ℝ) • (positive * negative) +
      (b * a : ℝ) • (negative * positive)
  calc
    (a * a : ℝ) • (1 : Op) +
          (a * b : ℝ) • (negative * positive) +
          ((b * a : ℝ) • (positive * negative) +
            (b * b : ℝ) • (-1 : Op)) =
        (a ^ 2 - b ^ 2 : ℝ) • (1 : Op) + hcrossExpr := by module
    _ = algebraMap ℝ Op (a ^ 2 - b ^ 2) := by
      dsimp [hcrossExpr]
      rw [hcross]
      simp [Algebra.algebraMap_eq_smul_one]

noncomputable def cl11AlgebraHom
    (positive negative : Op)
    (h : CantorBinaryTiltCARCCRBridge.IsLocalCl11Relation positive negative) :
    CliffordAlgebra q11 →ₐ[ℝ] Op :=
  CliffordAlgebra.lift q11 ⟨cl11Generator positive negative,
    by intro v
       simpa [Algebra.algebraMap_eq_smul_one] using
         cl11Generator_sq positive negative h v⟩

noncomputable def localCl11Generator
    (P : BinaryWordTiltReadout Op) : (ℝ × ℝ) →ₗ[ℝ] Op :=
  cl11Generator (localCl11Positive P) (localCl11Negative P)

noncomputable def localCl11AlgebraHom
    (P : BinaryWordTiltReadout Op) :
    CliffordAlgebra q11 →ₐ[ℝ] Op :=
  cl11AlgebraHom (localCl11Positive P) (localCl11Negative P)
    (binaryWordLocalCl11Relation P)

theorem localCl11Generator_sq
    (P : BinaryWordTiltReadout Op) (v : ℝ × ℝ) :
    localCl11Generator P v * localCl11Generator P v =
      algebraMap ℝ Op (q11 v) := by
  exact cl11Generator_sq (localCl11Positive P) (localCl11Negative P)
    (binaryWordLocalCl11Relation P) v

@[simp] theorem cl11AlgebraHom_ι
    (positive negative : Op)
    (h : IsLocalCl11Relation positive negative)
    (v : ℝ × ℝ) :
    cl11AlgebraHom positive negative h (CliffordAlgebra.ι q11 v) =
      cl11Generator positive negative v := by
  simp [cl11AlgebraHom]

theorem cl11AlgebraHom_ext
    {positive negative positive' negative' : Op}
    {h : CantorBinaryTiltCARCCRBridge.IsLocalCl11Relation positive negative}
    {h' : CantorBinaryTiltCARCCRBridge.IsLocalCl11Relation positive' negative'}
    (hpos : positive = positive')
    (hneg : negative = negative') :
    cl11AlgebraHom positive negative h =
      cl11AlgebraHom positive' negative' h' := by
  subst positive'
  subst negative'
  rfl

@[simp] theorem localCl11AlgebraHom_ι
    (P : BinaryWordTiltReadout Op) (v : ℝ × ℝ) :
    localCl11AlgebraHom P (CliffordAlgebra.ι q11 v) =
      localCl11Generator P v := by
  exact cl11AlgebraHom_ι _ _ _ v

theorem localCl11AlgebraHom_pos
    (P : BinaryWordTiltReadout Op) :
    localCl11AlgebraHom P (CliffordAlgebra.ι q11 (1, 0)) =
      localCl11Positive P := by
  rw [localCl11AlgebraHom_ι]
  simp [localCl11Generator, cl11Generator]

theorem localCl11AlgebraHom_neg
    (P : BinaryWordTiltReadout Op) :
    localCl11AlgebraHom P (CliffordAlgebra.ι q11 (0, 1)) =
      localCl11Negative P := by
  rw [localCl11AlgebraHom_ι]
  simp [localCl11Generator, cl11Generator]

def representationPositive (R : CantorCliffordRepresentation Op) : Op :=
  R.gamma 0

def representationNegative (R : CantorCliffordRepresentation Op) : Op :=
  R.gamma 0 * R.gamma 1

theorem representationLocalCl11Relation
    (R : CantorCliffordRepresentation Op) :
    CantorBinaryTiltCARCCRBridge.IsLocalCl11Relation
      (representationPositive R) (representationNegative R) := by
  refine ⟨R.gamma_sq 0, ?_, ?_⟩
  · apply mul_sq_neg_one_of_sq_one_of_anticomm
    · exact R.gamma_sq 0
    · exact R.gamma_sq 1
    · exact R.generator_anticomm (by decide)
  · have h := R.generator_anticomm (i := 0) (j := 1) (by decide)
    have hrev : R.gamma 1 * R.gamma 0 =
        -(R.gamma 0 * R.gamma 1) := eq_neg_of_add_eq_zero_right h
    change R.gamma 0 * (R.gamma 0 * R.gamma 1) +
        (R.gamma 0 * R.gamma 1) * R.gamma 0 = 0
    rw [show R.gamma 0 * (R.gamma 0 * R.gamma 1) +
        (R.gamma 0 * R.gamma 1) * R.gamma 0 =
        (R.gamma 0 * R.gamma 0) * R.gamma 1 +
          R.gamma 0 * (R.gamma 1 * R.gamma 0) by noncomm_ring]
    rw [R.gamma_sq 0, hrev, mul_neg, ← mul_assoc, R.gamma_sq 0]
    simp

@[simp] theorem representationPositive_eq (R : CantorCliffordRepresentation Op) :
    representationPositive R = R.gamma 0 := rfl

@[simp] theorem representationNegative_eq (R : CantorCliffordRepresentation Op) :
    representationNegative R = R.gamma 0 * R.gamma 1 := rfl

theorem real_cl11_matrix_equivalence_injective :
    Function.Injective cl11EquivMat := cl11EquivMat.injective

theorem real_cl11_matrix_equivalence_surjective :
    Function.Surjective cl11EquivMat := cl11EquivMat.surjective

theorem real_cl11_matrix_coordinate_decomposition (M : Mat2) :
    M = (alpha M) • (1 : Mat2) + (beta M) • Eplus +
      (gamma M) • Eminus + (delta M) • J1 :=
  mat2_decompose M

theorem real_cl11_matrix_coordinate_decomposition_unique
    (a b c d : ℝ)
    (h : a • (1 : Mat2) + b • Eplus + c • Eminus + d • J1 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h00 := congr_fun (congr_fun h 0) 0
  have h11 := congr_fun (congr_fun h 1) 1
  have h01 := congr_fun (congr_fun h 0) 1
  have h10 := congr_fun (congr_fun h 1) 0
  simp [Eplus, Eminus, J1, Matrix.smul_apply, Matrix.add_apply] at h00 h11 h01 h10
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem real_cl11_matrix_packet_linearly_independent :
    LinearIndependent ℝ ![(1 : Mat2), Eplus, Eminus, J1] := by
  apply Fintype.linearIndependent_iff.mpr
  intro l hsum i
  fin_cases i
  · exact (real_cl11_matrix_coordinate_decomposition_unique
      (l 0) (l 1) (l 2) (l 3) (by simpa [Fin.sum_univ_four] using hsum)).1
  · exact (real_cl11_matrix_coordinate_decomposition_unique
      (l 0) (l 1) (l 2) (l 3) (by simpa [Fin.sum_univ_four] using hsum)).2.1
  · exact (real_cl11_matrix_coordinate_decomposition_unique
      (l 0) (l 1) (l 2) (l 3) (by simpa [Fin.sum_univ_four] using hsum)).2.2.1
  · exact (real_cl11_matrix_coordinate_decomposition_unique
      (l 0) (l 1) (l 2) (l 3) (by simpa [Fin.sum_univ_four] using hsum)).2.2.2

theorem representationPositive_eq_binary
    (P : BinaryWordTiltReadout Op)
    (R : CantorCliffordRepresentation Op)
    (h0 : R.gamma 0 = P.bitOperator false) :
    representationPositive R = localCl11Positive P := by
  simp [representationPositive, localCl11Positive, h0]

theorem representationNegative_eq_binary
    (P : BinaryWordTiltReadout Op)
    (R : CantorCliffordRepresentation Op)
    (h0 : R.gamma 0 = P.bitOperator false)
    (h1 : R.gamma 1 = P.bitOperator true) :
    representationNegative R = localCl11Negative P := by
  simp [representationNegative, localCl11Positive, localCl11Negative, h0, h1]

theorem localCl11AlgebraHom_eq_representationHom
    (P : BinaryWordTiltReadout Op)
    (R : CantorCliffordRepresentation Op)
    (h0 : R.gamma 0 = P.bitOperator false)
    (h1 : R.gamma 1 = P.bitOperator true) :
    localCl11AlgebraHom P =
      cl11AlgebraHom (representationPositive R) (representationNegative R)
        (representationLocalCl11Relation R) := by
  apply cl11AlgebraHom_ext
  · exact (representationPositive_eq_binary P R h0).symm
  · exact (representationNegative_eq_binary P R h0 h1).symm

end InfoGeometry.Canonical.CantorLocalCl11Universal
