import proofs.HexagonalSixRootTiling
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import Mathlib.Tactic

/-!
# Six-state spectral bridge

This owner connects the finite `ZMod 6` labels to explicit nonzero
eigenvectors of `sheetGamma ⊗ colorShift`, including their sheet parity.
Characteristic polynomials and simple spectrum remain separate obligations.
-/

noncomputable section
namespace SixStateSpectralBridge

open HexagonalSixRootTiling TwoSheetThreeColorWeyl

abbrev State := SixIndex → ℂ

def colorEigenvalue (ω : ℂ) (a : HexColor) : ℂ :=
  if a = 0 then 1 else if a = 1 then ω else ω ^ 2

/-- Fourier eigenvector `[1, λ², λ]` for the cyclic colour shift. -/
def colorEigenvector (ω : ℂ) (a : HexColor) : Fin 3 → ℂ :=
  ![1, colorEigenvalue ω a ^ 2, colorEigenvalue ω a]

def reflectedColor (a : HexColor) : HexColor :=
  if a = 0 then 0 else if a = 1 then 2 else 1

theorem reflectedColor_eq_neg (a : HexColor) : reflectedColor a = -a := by
  fin_cases a <;> decide

theorem colorEigenvalue_cube (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (a : HexColor) : colorEigenvalue ω a ^ 3 = 1 := by
  fin_cases a
  · norm_num [colorEigenvalue]
  · simpa [colorEigenvalue] using omega_cube ω hω
  · change (ω ^ 2) ^ 3 = 1
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, omega_cube ω hω]
    norm_num

theorem colorEigenvector_nonzero (ω : ℂ) (a : HexColor) :
    colorEigenvector ω a ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [colorEigenvector] using h0

theorem colorShift_eigenvector (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (a : HexColor) :
    colorShift.mulVec (colorEigenvector ω a) =
      colorEigenvalue ω a • colorEigenvector ω a := by
  have hc := colorEigenvalue_cube ω hω a
  funext i
  fin_cases i
  · simp [colorShift, colorEigenvector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  · simp [colorShift, colorEigenvector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
    simpa [pow_succ, mul_assoc] using hc.symm
  · simp [colorShift, colorEigenvector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, pow_two]

def sheetVector : HexSheet → Fin 2 → ℂ
  | .positive => ![1, 0]
  | .negative => ![0, 1]

def pureTensor (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) : State :=
  fun ij => x ij.1 * y ij.2

theorem tensor_mulVec_pureTensor (A : M2C) (B : M3C)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) :
    (tensor A B).mulVec (pureTensor x y) =
      pureTensor (A.mulVec x) (B.mulVec y) := by
  ext ⟨i, j⟩
  change (∑ kl : Fin 2 × Fin 3,
      A i kl.1 * B j kl.2 * (x kl.1 * y kl.2)) =
    (∑ k, A i k * x k) * (∑ l, B j l * y l)
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ l, A i k * B j l * (x k * y l)) =
        ∑ l, (A i k * x k) * (B j l * y l) := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = (A i k * x k) * ∑ l, B j l * y l := by
      rw [Finset.mul_sum]

def sheetColorVector (ω : ℂ) (s : HexSheet) (a : HexColor) : State :=
  pureTensor (sheetVector s) (colorEigenvector ω a)

def labelledVector (ω : ℂ) (n : HexIndex) : State :=
  sheetColorVector ω (sheetOf n) (colorOf n)

def labelledEigenvalue (ω : ℂ) (n : HexIndex) : ℂ :=
  match sheetOf n with
  | .positive => colorEigenvalue ω (colorOf n)
  | .negative => -colorEigenvalue ω (colorOf n)

def sheetParityOperator : M6C := tensor sheetGamma (1 : M3C)

/-- Orientation-reversing sheet/family operator `J ⊗ R`. -/
def pinTheta : M6C := tensor sheetFlip colorReflection

theorem sheetColorVector_nonzero (ω : ℂ) (s : HexSheet) (a : HexColor) :
    sheetColorVector ω s a ≠ 0 := by
  intro h
  cases s
  · have h0 := congrFun h (0, 0)
    simpa [sheetColorVector, pureTensor, sheetVector, colorEigenvector] using h0
  · have h0 := congrFun h (1, 0)
    simpa [sheetColorVector, pureTensor, sheetVector, colorEigenvector] using h0

theorem labelledVector_nonzero (ω : ℂ) (n : HexIndex) :
    labelledVector ω n ≠ 0 :=
  sheetColorVector_nonzero ω (sheetOf n) (colorOf n)

theorem sheetGamma_eigen_positive :
    sheetGamma.mulVec (sheetVector .positive) = sheetVector .positive := by
  funext i
  fin_cases i <;>
    simp [sheetGamma, sheetPlus, sheetMinus, sheetVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sheetGamma_eigen_negative :
    sheetGamma.mulVec (sheetVector .negative) = -sheetVector .negative := by
  funext i
  fin_cases i <;>
    simp [sheetGamma, sheetPlus, sheetMinus, sheetVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sheetFlip_positive :
    sheetFlip.mulVec (sheetVector .positive) = sheetVector .negative := by
  funext i
  fin_cases i <;>
    simp [sheetFlip, sheetVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sheetFlip_negative :
    sheetFlip.mulVec (sheetVector .negative) = sheetVector .positive := by
  funext i
  fin_cases i <;>
    simp [sheetFlip, sheetVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem colorReflection_eigenvector (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (a : HexColor) :
    colorReflection.mulVec (colorEigenvector ω a) =
      colorEigenvector ω (-a) := by
  rw [← reflectedColor_eq_neg a]
  have h4 : ω ^ 4 = ω := by
    calc
      ω ^ 4 = ω * ω ^ 3 := by ring
      _ = ω := by rw [omega_cube ω hω]; ring
  have h20 : (2 : HexColor) ≠ 0 := by decide
  have h21 : (2 : HexColor) ≠ 1 := by decide
  have hr0 : reflectedColor (0 : HexColor) = 0 := by decide
  have hr1 : reflectedColor (1 : HexColor) = 2 := by decide
  have hr2 : reflectedColor (2 : HexColor) = 1 := by decide
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by
    fin_cases a <;> simp
  rcases ha with rfl | rfl | rfl
  all_goals
    funext i
    fin_cases i <;>
      norm_num [colorReflection, colorEigenvector, colorEigenvalue,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, pow_two,
        reflectedColor, h20, h21, hr0, hr1, hr2] <;>
      first
      | rfl
      | simpa [pow_succ, mul_assoc] using h4
      | simpa [pow_succ, mul_assoc] using h4.symm

theorem triality_eigen_positive (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (a : HexColor) :
    sixfoldTriality.mulVec (sheetColorVector ω .positive a) =
      colorEigenvalue ω a • sheetColorVector ω .positive a := by
  rw [show sixfoldTriality = tensor sheetGamma colorShift by rfl,
    sheetColorVector, tensor_mulVec_pureTensor,
    sheetGamma_eigen_positive, colorShift_eigenvector ω hω]
  ext ⟨i, j⟩
  simp only [pureTensor, Pi.smul_apply, smul_eq_mul]
  ring

theorem triality_eigen_negative (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (a : HexColor) :
    sixfoldTriality.mulVec (sheetColorVector ω .negative a) =
      (-colorEigenvalue ω a) • sheetColorVector ω .negative a := by
  rw [show sixfoldTriality = tensor sheetGamma colorShift by rfl,
    sheetColorVector, tensor_mulVec_pureTensor,
    sheetGamma_eigen_negative, colorShift_eigenvector ω hω]
  ext ⟨i, j⟩
  simp only [pureTensor, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem labelledVector_eigen (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (n : HexIndex) :
    sixfoldTriality.mulVec (labelledVector ω n) =
      labelledEigenvalue ω n • labelledVector ω n := by
  simp only [labelledVector]
  cases h : sheetOf n
  · simpa [labelledEigenvalue, h] using triality_eigen_positive ω hω (colorOf n)
  · simpa [labelledEigenvalue, h] using triality_eigen_negative ω hω (colorOf n)

theorem parity_eigen_positive (ω : ℂ) (a : HexColor) :
    sheetParityOperator.mulVec (sheetColorVector ω .positive a) =
      sheetColorVector ω .positive a := by
  rw [sheetParityOperator, sheetColorVector, tensor_mulVec_pureTensor,
    sheetGamma_eigen_positive]
  rw [Matrix.one_mulVec]

theorem parity_eigen_negative (ω : ℂ) (a : HexColor) :
    sheetParityOperator.mulVec (sheetColorVector ω .negative a) =
      -sheetColorVector ω .negative a := by
  rw [sheetParityOperator, sheetColorVector, tensor_mulVec_pureTensor,
    sheetGamma_eigen_negative]
  rw [Matrix.one_mulVec]
  ext ⟨i, j⟩
  simp only [pureTensor, Pi.neg_apply]
  ring

theorem labelledVector_sheet_parity (ω : ℂ) (n : HexIndex) :
    sheetParityOperator.mulVec (labelledVector ω n) =
      match sheetOf n with
      | .positive => labelledVector ω n
      | .negative => -labelledVector ω n := by
  simp only [labelledVector]
  cases h : sheetOf n
  · simpa [h] using parity_eigen_positive ω (colorOf n)
  · simpa [h] using parity_eigen_negative ω (colorOf n)

theorem pinTheta_positive (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (a : HexColor) :
    pinTheta.mulVec (sheetColorVector ω .positive a) =
      sheetColorVector ω .negative (-a) := by
  rw [pinTheta, sheetColorVector, tensor_mulVec_pureTensor,
    sheetFlip_positive, colorReflection_eigenvector ω hω]
  rfl

theorem pinTheta_negative (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (a : HexColor) :
    pinTheta.mulVec (sheetColorVector ω .negative a) =
      sheetColorVector ω .positive (-a) := by
  rw [pinTheta, sheetColorVector, tensor_mulVec_pureTensor,
    sheetFlip_negative, colorReflection_eigenvector ω hω]
  rfl

/-- The concrete Pin reflection realizes exactly `n ↦ 3 - n` on labels. -/
theorem pinTheta_labelledVector (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (n : HexIndex) :
    pinTheta.mulVec (labelledVector ω n) =
      labelledVector ω (hexReflect n) := by
  fin_cases n
  all_goals
    simp only [labelledVector]
    first
    | exact pinTheta_positive ω hω 0
    | exact pinTheta_positive ω hω 1
    | exact pinTheta_positive ω hω 2
    | exact pinTheta_negative ω hω 0
    | exact pinTheta_negative ω hω 1
    | exact pinTheta_negative ω hω 2

theorem positiveVertex_eigenvalue (ω : ℂ) (a : HexColor) :
    labelledEigenvalue ω (positiveVertex a) = colorEigenvalue ω a := by
  fin_cases a <;> rfl

theorem negativeVertex_eigenvalue (ω : ℂ) (a : HexColor) :
    labelledEigenvalue ω (negativeVertex a) = -colorEigenvalue ω a := by
  fin_cases a <;> rfl

end SixStateSpectralBridge
end noncomputable section
