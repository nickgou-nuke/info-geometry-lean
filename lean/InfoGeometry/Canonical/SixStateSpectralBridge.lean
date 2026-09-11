import Mathlib.LinearAlgebra.Matrix.Vec
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Canonical.HexagonalSixRootTiling

open scoped Matrix Kronecker

namespace InfoGeometry.Canonical.SixStateSpectralBridge

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.HexagonalSixRootTiling

abbrev SixVector := Fin 2 × Fin 3 → ℂ

def colorEigenvector (zeta : ℂ) : Fin 3 → ℂ := ![1, zeta ^ 2, zeta]

def positiveColorMatrix (zeta : ℂ) : Matrix (Fin 3) (Fin 2) ℂ :=
  !![1, 0; zeta ^ 2, 0; zeta, 0]

def negativeColorMatrix (zeta : ℂ) : Matrix (Fin 3) (Fin 2) ℂ :=
  !![0, 1; 0, zeta ^ 2; 0, zeta]

def positiveSpectralVector (zeta : ℂ) : SixVector :=
  Matrix.vec (positiveColorMatrix zeta)

def negativeSpectralVector (zeta : ℂ) : SixVector :=
  Matrix.vec (negativeColorMatrix zeta)

def spectralVector (zeta : HexColor → ℂ) (n : HexIndex) : SixVector :=
  match (sheetColorEquiv n).1 with
  | .positive => positiveSpectralVector (zeta (sheetColorEquiv n).2)
  | .negative => negativeSpectralVector (zeta (sheetColorEquiv n).2)

theorem colorEigenvector_shift (zeta : ℂ) (hzeta : zeta ^ 3 = 1) :
    colorShift *ᵥ colorEigenvector zeta = zeta • colorEigenvector zeta := by
  funext i
  fin_cases i
  · simp [colorShift, colorEigenvector, Matrix.mulVec, pow_two]
  · simp [colorShift, colorEigenvector, Matrix.mulVec, pow_two]
    simpa [pow_three] using hzeta.symm
  · simp [colorShift, colorEigenvector, Matrix.mulVec, pow_two]

theorem positiveSpectralVector_triality (zeta : ℂ) (hzeta : zeta ^ 3 = 1) :
    sixTriality *ᵥ positiveSpectralVector zeta =
      zeta • positiveSpectralVector zeta := by
  change (sheetParity ⊗ₖ colorShift) *ᵥ
      Matrix.vec (positiveColorMatrix zeta) =
    zeta • Matrix.vec (positiveColorMatrix zeta)
  rw [Matrix.kronecker_mulVec_vec]
  have h : colorShift * positiveColorMatrix zeta * sheetParityᵀ =
      zeta • positiveColorMatrix zeta := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [colorShift, positiveColorMatrix, sheetParity, uPlus, uMinus,
        Matrix.mul_apply, Fin.sum_univ_two, pow_two] ; ring
    all_goals exact hzeta.symm
  rw [h]
  rfl

theorem negativeSpectralVector_triality (zeta : ℂ) (hzeta : zeta ^ 3 = 1) :
    sixTriality *ᵥ negativeSpectralVector zeta =
      (-zeta) • negativeSpectralVector zeta := by
  change (sheetParity ⊗ₖ colorShift) *ᵥ
      Matrix.vec (negativeColorMatrix zeta) =
    (-zeta) • Matrix.vec (negativeColorMatrix zeta)
  rw [Matrix.kronecker_mulVec_vec]
  have h : colorShift * negativeColorMatrix zeta * sheetParityᵀ =
      (-zeta) • negativeColorMatrix zeta := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [colorShift, negativeColorMatrix, sheetParity, uPlus, uMinus,
        Matrix.mul_apply, Fin.sum_univ_two, pow_two] ; ring
    all_goals exact hzeta.symm
  rw [h]
  ext ⟨i, j⟩
  simp [Matrix.vec, Matrix.smul_apply]

theorem spectralVector_triality
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    sixTriality *ᵥ spectralVector zeta n =
      (if (sheetColorEquiv n).1 = .positive then
          zeta (sheetColorEquiv n).2
       else -zeta (sheetColorEquiv n).2) • spectralVector zeta n := by
  dsimp [spectralVector]
  cases h : (sheetColorEquiv n).1 with
  | positive =>
      exact positiveSpectralVector_triality _ (hzeta _)
  | negative =>
      exact negativeSpectralVector_triality _ (hzeta _)

theorem positiveSpectralVector_ne_zero (zeta : ℂ) :
    positiveSpectralVector zeta ≠ 0 := by
  intro h
  have h0 := congrFun h (0, 0)
  simp [positiveSpectralVector, positiveColorMatrix, Matrix.vec] at h0

theorem negativeSpectralVector_ne_zero (zeta : ℂ) :
    negativeSpectralVector zeta ≠ 0 := by
  intro h
  have h0 := congrFun h (1, 0)
  simp [negativeSpectralVector, negativeColorMatrix, Matrix.vec] at h0

theorem spectralVector_ne_zero
    (zeta : HexColor → ℂ) (n : HexIndex) :
    spectralVector zeta n ≠ 0 := by
  dsimp [spectralVector]
  cases h : (sheetColorEquiv n).1 with
  | positive =>
      exact positiveSpectralVector_ne_zero _
  | negative =>
      exact negativeSpectralVector_ne_zero _

theorem positiveSpectralVector_parity (zeta : ℂ) :
    sixParity *ᵥ positiveSpectralVector zeta =
      positiveSpectralVector zeta := by
  change (sheetParity ⊗ₖ (1 : Mat3C)) *ᵥ
      Matrix.vec (positiveColorMatrix zeta) = Matrix.vec _
  rw [Matrix.kronecker_mulVec_vec]
  funext p
  rcases p with ⟨j, i⟩
  change ((1 : Mat3C) * positiveColorMatrix zeta * sheetParityᵀ) i j =
    positiveColorMatrix zeta i j
  fin_cases i <;> fin_cases j <;>
      simp [positiveColorMatrix, sheetParity, uPlus, uMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem negativeSpectralVector_parity (zeta : ℂ) :
    sixParity *ᵥ negativeSpectralVector zeta =
      -negativeSpectralVector zeta := by
  change (sheetParity ⊗ₖ (1 : Mat3C)) *ᵥ
      Matrix.vec (negativeColorMatrix zeta) = -Matrix.vec _
  rw [Matrix.kronecker_mulVec_vec]
  funext p
  rcases p with ⟨j, i⟩
  change ((1 : Mat3C) * negativeColorMatrix zeta * sheetParityᵀ) i j =
    -negativeColorMatrix zeta i j
  fin_cases i <;> fin_cases j <;>
      simp [negativeColorMatrix, sheetParity, uPlus, uMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem spectralVector_parity
    (zeta : HexColor → ℂ) (n : HexIndex) :
    sixParity *ᵥ spectralVector zeta n =
      (if (sheetColorEquiv n).1 = .positive then
          spectralVector zeta n
       else -spectralVector zeta n) := by
  dsimp [spectralVector]
  cases h : (sheetColorEquiv n).1 with
  | positive =>
      exact positiveSpectralVector_parity _
  | negative =>
      exact negativeSpectralVector_parity _

theorem positiveVertex_triality
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (a : HexColor) :
    sixTriality *ᵥ spectralVector zeta (positiveVertex a) =
      zeta a • spectralVector zeta (positiveVertex a) := by
  have h := spectralVector_triality zeta hzeta (positiveVertex a)
  have hlabel : sheetColorEquiv (positiveVertex a) = (.positive, a) := by
    exact sheetColorEquiv.apply_symm_apply (.positive, a)
  simpa [hlabel] using h

theorem negativeVertex_triality
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (a : HexColor) :
    sixTriality *ᵥ spectralVector zeta (negativeVertex a) =
      (-zeta a) • spectralVector zeta (negativeVertex a) := by
  have h := spectralVector_triality zeta hzeta (negativeVertex a)
  have hlabel : sheetColorEquiv (negativeVertex a) = (.negative, a) := by
    exact sheetColorEquiv.apply_symm_apply (.negative, a)
  simpa [hlabel] using h

theorem positiveVertex_parity
    (zeta : HexColor → ℂ) (a : HexColor) :
    sixParity *ᵥ spectralVector zeta (positiveVertex a) =
      spectralVector zeta (positiveVertex a) := by
  have h := spectralVector_parity zeta (positiveVertex a)
  have hlabel : sheetColorEquiv (positiveVertex a) = (.positive, a) := by
    exact sheetColorEquiv.apply_symm_apply (.positive, a)
  simpa [hlabel] using h

theorem negativeVertex_parity
    (zeta : HexColor → ℂ) (a : HexColor) :
    sixParity *ᵥ spectralVector zeta (negativeVertex a) =
      -spectralVector zeta (negativeVertex a) := by
  have h := spectralVector_parity zeta (negativeVertex a)
  have hlabel : sheetColorEquiv (negativeVertex a) = (.negative, a) := by
    exact sheetColorEquiv.apply_symm_apply (.negative, a)
  simpa [hlabel] using h

end InfoGeometry.Canonical.SixStateSpectralBridge
