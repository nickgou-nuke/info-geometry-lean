import proofs.HestenesEvenPauliEquiv
import proofs.HestenesCliffordKrein
import proofs.HestenesKreinFramework

/-! # Transport of the native Hestenes reverse/Krein involution

The independently constructed equivalence `Cl⁺(1,3) ≃ₐ[ℝ] M₂(ℂ)` transports the
intrinsic Clifford involution to a canonical real-linear anti-automorphism of
the Pauli matrix algebra.  This owner also records that, with the repository's
current conventions, it is not the previously defined conjugate-transpose
Krein adjoint: the two operations already differ on the fundamental bivector.
-/

noncomputable section
namespace HestenesKreinMatrixBridge

open HestenesCl14
open HestenesPauliSheetBridge
open HestenesEvenPauliEquiv
open HestenesCliffordKrein
open HestenesKreinFramework
open TwoSheetThreeColorWeyl

abbrev Sheet := HestenesPauliSheetBridge.Sheet

def reverseEven (x : ClPlus14) : ClPlus14 :=
  ⟨CliffordAlgebra.reverse (x : Cl14),
    (CliffordAlgebra.reverse_mem_evenOdd_iff (Q := Q14)).2 x.2⟩

def reverseKreinEven (x : ClPlus14) : ClPlus14 :=
  sigmaEven 0 * reverseEven x * sigmaEven 0

@[simp] theorem reverseKreinEven_val (x : ClPlus14) :
    (reverseKreinEven x : Cl14) = reverseKrein (x : Cl14) := rfl

@[simp] theorem reverseEven_add (x y : ClPlus14) :
    reverseEven (x + y) = reverseEven x + reverseEven y := by
  apply Subtype.ext
  simp [reverseEven, map_add]

@[simp] theorem reverseEven_smul (r : ℝ) (x : ClPlus14) :
    reverseEven (r • x) = r • reverseEven x := by
  apply Subtype.ext
  simp [reverseEven, map_smul]

@[simp] theorem reverseEven_mul (x y : ClPlus14) :
    reverseEven (x * y) = reverseEven y * reverseEven x := by
  apply Subtype.ext
  exact CliffordAlgebra.reverse.map_mul (x : Cl14) (y : Cl14)

@[simp] theorem reverseKreinEven_add (x y : ClPlus14) :
    reverseKreinEven (x + y) = reverseKreinEven x + reverseKreinEven y := by
  simp [reverseKreinEven, mul_add, add_mul]

@[simp] theorem reverseKreinEven_smul (r : ℝ) (x : ClPlus14) :
    reverseKreinEven (r • x) = r • reverseKreinEven x := by
  apply Subtype.ext
  simp [reverseKreinEven]

@[simp] theorem reverseKreinEven_mul (x y : ClPlus14) :
    reverseKreinEven (x * y) = reverseKreinEven y * reverseKreinEven x := by
  apply Subtype.ext
  change reverseKrein ((x : Cl14) * (y : Cl14)) =
    reverseKrein (y : Cl14) * reverseKrein (x : Cl14)
  simp only [reverseKrein, CliffordAlgebra.reverse.map_mul]
  have hb : beta * beta = (1 : Cl14) := beta_sq
  calc
    beta * (CliffordAlgebra.reverse (y : Cl14) *
        CliffordAlgebra.reverse (x : Cl14)) * beta =
        beta * CliffordAlgebra.reverse (y : Cl14) *
          CliffordAlgebra.reverse (x : Cl14) * beta := by
            simp only [mul_assoc]
    _ = beta * CliffordAlgebra.reverse (y : Cl14) * (beta * beta) *
          CliffordAlgebra.reverse (x : Cl14) * beta := by
            rw [hb]
            simp
    _ = (beta * CliffordAlgebra.reverse (y : Cl14) * beta) *
          (beta * CliffordAlgebra.reverse (x : Cl14) * beta) := by
            simp only [mul_assoc]

@[simp] theorem reverseKreinEven_involutive (x : ClPlus14) :
    reverseKreinEven (reverseKreinEven x) = x := by
  apply Subtype.ext
  exact reverseKrein_involutive (x : Cl14)

/-- The matrix-side involution canonically transported through the genuine
real algebra equivalence. -/
def transportedReverseKrein (A : Sheet) : Sheet :=
  clPlusPauliAlgEquiv
    (reverseKreinEven (clPlusPauliAlgEquiv.symm A))

/-- The requested transport theorem, stated without imposing a false matrix
normal form. -/
theorem reverseKrein_transport (x : ClPlus14) :
    clPlusPauliAlgEquiv (reverseKreinEven x) =
      transportedReverseKrein (clPlusPauliAlgEquiv x) := by
  simp [transportedReverseKrein]

@[simp] theorem transportedReverseKrein_add (A B : Sheet) :
    transportedReverseKrein (A + B) =
      transportedReverseKrein A + transportedReverseKrein B := by
  simp [transportedReverseKrein]

@[simp] theorem transportedReverseKrein_real_smul (r : ℝ) (A : Sheet) :
    transportedReverseKrein (r • A) = r • transportedReverseKrein A := by
  simp [transportedReverseKrein]

@[simp] theorem transportedReverseKrein_mul (A B : Sheet) :
    transportedReverseKrein (A * B) =
      transportedReverseKrein B * transportedReverseKrein A := by
  simp [transportedReverseKrein]

@[simp] theorem transportedReverseKrein_involutive (A : Sheet) :
    transportedReverseKrein (transportedReverseKrein A) = A := by
  simp [transportedReverseKrein]

@[simp] theorem reverseKreinEven_beta :
    reverseKreinEven (sigmaEven 0) = -sigmaEven 0 := by
  apply Subtype.ext
  change reverseKrein beta = -beta
  rw [reverseKrein, reverse_beta]
  have hb : beta * beta = (1 : Cl14) := beta_sq
  simp [hb]

@[simp] theorem transportedReverseKrein_pauli1 :
    transportedReverseKrein pauli1 = -pauli1 := by
  have hs : clPlusPauliAlgEquiv.symm pauli1 = sigmaEven 0 := by
    apply clPlusPauliAlgEquiv.injective
    rw [clPlusPauliAlgEquiv.apply_symm_apply]
    exact clPlusToPauli_sigma0.symm
  rw [transportedReverseKrein, hs, reverseKreinEven_beta, map_neg]
  exact congrArg Neg.neg clPlusToPauli_sigma0

theorem pauli1_eq_fundamentalSymmetry :
    pauli1 = fundamentalSymmetry := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, fundamentalSymmetry, sheetFlip]

@[simp] theorem matrixKreinAdjoint_pauli1 : kreinAdjoint pauli1 = pauli1 := by
  rw [pauli1_eq_fundamentalSymmetry]
  exact kreinAdjoint_fundamentalSymmetry

/-- Concrete obstruction: the intrinsic reverse/Krein involution and the
existing matrix conjugate-transpose Krein adjoint are different operations
under the current generator conventions. -/
theorem transportedReverseKrein_ne_kreinAdjoint :
    transportedReverseKrein ≠ kreinAdjoint := by
  intro h
  have hp := congrFun h pauli1
  rw [transportedReverseKrein_pauli1, matrixKreinAdjoint_pauli1] at hp
  have hp01 := congrFun (congrFun hp 0) 1
  norm_num [pauli1] at hp01

end HestenesKreinMatrixBridge
end noncomputable section
