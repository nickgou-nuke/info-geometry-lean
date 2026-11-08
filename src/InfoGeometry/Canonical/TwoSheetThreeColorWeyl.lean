import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Two-sheet and three-colour Weyl operators

This owner keeps the two finite factors separate.  The sheet factor is the
complex two-by-two CAR algebra; the colour factor is the three-by-three
clock--shift algebra.  Their combined carrier is the native Kronecker matrix
carrier indexed by `Fin 2 × Fin 3`.

The colour root is intentionally a parameter subject to its defining
cyclotomic identities.  No unproved choice of a complex primitive root is
hidden in this file.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.TwoSheetThreeColorWeyl

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev Mat3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev Mat23C := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

def uPlus : Mat2C := !![(1 : ℂ), 0; 0, 0]
def uMinus : Mat2C := !![(0 : ℂ), 0; 0, 1]
def sigmaPlus : Mat2C := !![(0 : ℂ), 1; 0, 0]
def sigmaMinus : Mat2C := !![(0 : ℂ), 0; 1, 0]
def sheetParity : Mat2C := uPlus - uMinus
def sheetExchange : Mat2C := !![(0 : ℂ), 1; 1, 0]

@[simp] theorem uPlus_sq : uPlus * uPlus = uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem uMinus_sq : uMinus * uMinus = uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem uPlus_add_uMinus : uPlus + uMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uPlus, uMinus]

@[simp] theorem uPlus_mul_uMinus : uPlus * uMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sigmaMinus_sq : sigmaMinus * sigmaMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sigmaPlus_mul_sigmaMinus :
    sigmaPlus * sigmaMinus = uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, uPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sigmaMinus_mul_sigmaPlus :
    sigmaMinus * sigmaPlus = uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sigmaPlus_anticomm_sigmaMinus :
    sigmaPlus * sigmaMinus + sigmaMinus * sigmaPlus = 1 := by
  rw [sigmaPlus_mul_sigmaMinus, sigmaMinus_mul_sigmaPlus, uPlus_add_uMinus]

@[simp] theorem sheetParity_sq : sheetParity * sheetParity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, uPlus, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sheetExchange_sq : sheetExchange * sheetExchange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetExchange_uPlus_sheetExchange :
    sheetExchange * uPlus * sheetExchange = uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, uPlus, uMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetExchange_parity_sheetExchange :
    sheetExchange * sheetParity * sheetExchange = -sheetParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, sheetParity, uPlus, uMinus, Matrix.mul_apply,
      Fin.sum_univ_two]

def colorShift : Mat3C := !![(0 : ℂ), 0, 1; 1, 0, 0; 0, 1, 0]
def colorClock (ω : ℂ) : Mat3C := !![(1 : ℂ), 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

theorem colorShift_cubed : colorShift ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorShift, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem colorClock_cubed (ω : ℂ) (hω : ω ^ 3 = 1) :
    colorClock ω ^ 3 = 1 := by
  have hωmul : ω * ω * ω = 1 := by
    simpa [pow_three, mul_assoc] using hω
  have hωsq : ω ^ 2 = ω * ω := by
    simp [pow_two]
  have hω6 : ω ^ 6 = 1 := by
    calc
      ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorClock, pow_succ, Matrix.mul_apply, Fin.sum_univ_three,
      hωmul, hωsq] ; (ring_nf; exact hω6)

theorem color_weyl_relation (ω : ℂ) (hω : ω ^ 3 = 1) :
    colorClock ω * colorShift = ω • (colorShift * colorClock ω) := by
  have hωmul : ω * ω * ω = 1 := by
    simpa [pow_three, mul_assoc] using hω
  have hωsq : ω ^ 2 = ω * ω := by
    simp [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorClock, colorShift, Matrix.mul_apply, Fin.sum_univ_three,
      hωsq] ; (ring_nf; exact hω.symm)

theorem kronecker_mul
    (A C : Mat2C) (B D : Mat3C) :
    Matrix.kronecker A B * Matrix.kronecker C D =
      Matrix.kronecker (A * C) (B * D) := by
  exact (Matrix.mul_kronecker_mul A C B D).symm

theorem kronecker_pow_two (A : Mat2C) (B : Mat3C) :
    (Matrix.kronecker A B) ^ 2 = Matrix.kronecker (A ^ 2) (B ^ 2) := by
  calc
    (Matrix.kronecker A B) ^ 2 =
        Matrix.kronecker A B * Matrix.kronecker A B := by simp [pow_two]
    _ = Matrix.kronecker (A * A) (B * B) := kronecker_mul A A B B
    _ = Matrix.kronecker (A ^ 2) (B ^ 2) := by simp [pow_two]

theorem kronecker_pow_three (A : Mat2C) (B : Mat3C) :
    (Matrix.kronecker A B) ^ 3 = Matrix.kronecker (A ^ 3) (B ^ 3) := by
  calc
    (Matrix.kronecker A B) ^ 3 =
        (Matrix.kronecker A B) ^ 2 * Matrix.kronecker A B := by
          simp [pow_succ, mul_assoc]
    _ = Matrix.kronecker (A ^ 2 * A) (B ^ 2 * B) := by
          rw [kronecker_pow_two, kronecker_mul]
    _ = Matrix.kronecker (A ^ 3) (B ^ 3) := by
          simp [pow_succ, mul_assoc]

@[simp] theorem kronecker_one_one :
    Matrix.kronecker (1 : Mat2C) (1 : Mat3C) = (1 : Mat23C) := by
  exact Matrix.one_kronecker_one

def sixClock (ω : ℂ) : Mat23C := Matrix.kronecker (1 : Mat2C) (colorClock ω)
def sixShift : Mat23C := Matrix.kronecker (1 : Mat2C) colorShift
def sixParity : Mat23C := Matrix.kronecker sheetParity (1 : Mat3C)
def sixSheetExchange : Mat23C := Matrix.kronecker sheetExchange (1 : Mat3C)
def sixTriality : Mat23C := Matrix.kronecker sheetParity colorShift
def twistedShift : Mat23C :=
  Matrix.kronecker uPlus colorShift +
    Matrix.kronecker uMinus (colorShift ^ 2)

theorem sheetExchange_uMinus_sheetExchange :
    sheetExchange * uMinus * sheetExchange = uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, uMinus, uPlus, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem twistedSheetExchange_conjugates_shift :
    sixSheetExchange * twistedShift * sixSheetExchange =
      Matrix.kronecker uPlus (colorShift ^ 2) +
        Matrix.kronecker uMinus colorShift := by
  simp only [sixSheetExchange, twistedShift]
  rw [mul_add, add_mul]
  rw [kronecker_mul, kronecker_mul, kronecker_mul, kronecker_mul]
  rw [sheetExchange_uPlus_sheetExchange,
    sheetExchange_uMinus_sheetExchange]
  simp [pow_two, add_comm]

theorem sixClock_cubed (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixClock ω ^ 3 = 1 := by
  rw [sixClock, kronecker_pow_three, colorClock_cubed ω hω]
  simp

theorem sixShift_cubed : sixShift ^ 3 = 1 := by
  rw [sixShift, kronecker_pow_three, colorShift_cubed]
  simp

theorem six_weyl_relation (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixClock ω * sixShift = ω • (sixShift * sixClock ω) := by
  rw [sixClock, sixShift, kronecker_mul, kronecker_mul,
    color_weyl_relation ω hω]
  exact Matrix.kronecker_smul ω (1 * 1 : Mat2C) (colorShift * colorClock ω)

theorem sixParity_squared :
    sixParity ^ 2 = 1 := by
  calc
    sixParity ^ 2 =
        Matrix.kronecker (sheetParity * sheetParity) ((1 : Mat3C) * 1) := by
          simpa [sixParity, pow_two] using kronecker_mul sheetParity sheetParity
            (1 : Mat3C) 1
    _ = 1 := by rw [sheetParity_sq]; simp

theorem sheetParity_cube : sheetParity ^ 3 = sheetParity := by
  simp [pow_succ, sheetParity_sq]

theorem sixTriality_cube : sixTriality ^ 3 = sixParity := by
  calc
    sixTriality ^ 3 =
        Matrix.kronecker (sheetParity ^ 3) (colorShift ^ 3) :=
      kronecker_pow_three sheetParity colorShift
    _ = sixParity := by
      rw [sheetParity_cube, colorShift_cubed]
      simp [sixParity]

theorem sixTriality_sixth : sixTriality ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul,
    sixTriality_cube, sixParity_squared]

theorem sixSheetExchange_involutive :
    sixSheetExchange ^ 2 = 1 := by
  calc
    sixSheetExchange ^ 2 =
        Matrix.kronecker (sheetExchange * sheetExchange) ((1 : Mat3C) * 1) := by
          simpa [sixSheetExchange, pow_two] using kronecker_mul sheetExchange sheetExchange
            (1 : Mat3C) 1
    _ = 1 := by rw [sheetExchange_sq]; simp

theorem sixSheetExchange_flips_parity :
    sixSheetExchange * sixParity * sixSheetExchange = -sixParity := by
  calc
    sixSheetExchange * sixParity * sixSheetExchange =
        Matrix.kronecker
          (sheetExchange * sheetParity * sheetExchange)
          ((1 : Mat3C) * 1 * 1) := by
            simp only [sixSheetExchange, sixParity]
            rw [kronecker_mul, kronecker_mul]
    _ = -sixParity := by
      rw [sheetExchange_parity_sheetExchange]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sixParity, Matrix.kroneckerMap_apply]

def projectiveTriality : Mat3C := -colorShift

theorem projectiveTriality_cube :
    projectiveTriality ^ 3 = -(1 : Mat3C) := by
  have hshift : colorShift ^ 3 = (1 : Mat3C) := colorShift_cubed
  calc
    projectiveTriality ^ 3 = (-colorShift) ^ 3 := rfl
    _ = -(colorShift ^ 3) := by noncomm_ring
    _ = -(1 : Mat3C) := by rw [hshift]

theorem projectiveTriality_sixth :
    projectiveTriality ^ 6 = (1 : Mat3C) := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul,
    projectiveTriality_cube]
  simp

end InfoGeometry.Canonical.TwoSheetThreeColorWeyl
