import Mathlib.Algebra.Category.ModuleCat.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-!
# Categorical finite carrier for the five-channel Fibonacci sector

The canonical low-anyon owner already supplies the concrete `Basis6 = Fin 5`
carrier and the five symbolic braid matrices.  This file only reinterprets
those matrices as morphisms in `ModuleCat`; it introduces no second path-space
or matrix API.
-/

namespace InfoGeometry.Categorical.FibonacciFourAnyonCarrier

open CategoryTheory
open InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciFusionTreeBraiding

noncomputable def fibonacciBBlockEntries (q : Units ℂ) (τ s : ℂ) :
    BBlockEntries :=
  { B00 := fibonacciBMatrix q τ s 0 0
    B01 := fibonacciBMatrix q τ s 0 1
    B10 := fibonacciBMatrix q τ s 1 0
    B11 := fibonacciBMatrix q τ s 1 1 }

theorem fibonacciBBlockEntries_matrix (q : Units ℂ) (τ s : ℂ) :
    BBlockEntries.matrix (fibonacciBBlockEntries q τ s) =
      fibonacciBMatrix q τ s := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    rfl

abbrev FourAnyonCarrier := Basis6 → ℂ

noncomputable def matrixHom (M : Matrix Basis6 Basis6 ℂ) :
    ModuleCat.of ℂ FourAnyonCarrier ⟶ ModuleCat.of ℂ FourAnyonCarrier :=
  ModuleCat.ofHom (Matrix.toLin' M)

@[simp] theorem matrixHom_apply (M : Matrix Basis6 Basis6 ℂ)
    (x : FourAnyonCarrier) :
    matrixHom M x = Matrix.mulVec M x := by
  rfl

theorem matrixHom_comp (M N : Matrix Basis6 Basis6 ℂ) :
    matrixHom M ≫ matrixHom N = matrixHom (N * M) := by
  apply ModuleCat.hom_ext
  ext x i
  simp [matrixHom, Matrix.toLin'_mul, Matrix.mulVec]

theorem matrixHom_one :
    matrixHom (1 : Matrix Basis6 Basis6 ℂ) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x i
  simp [matrixHom, Matrix.toLin'_apply, Matrix.mulVec]

theorem matrixHom_zero :
    matrixHom (0 : Matrix Basis6 Basis6 ℂ) = 0 := by
  apply ModuleCat.hom_ext
  ext x i
  simp [matrixHom, Matrix.toLin'_apply, Matrix.mulVec]

theorem matrixHom_add (M N : Matrix Basis6 Basis6 ℂ) :
    matrixHom (M + N) = matrixHom M + matrixHom N := by
  apply ModuleCat.hom_ext
  ext x i
  simp [matrixHom, Matrix.toLin'_apply, Matrix.mulVec, add_mul]

/--
Package a two-sided matrix inverse as a genuine `ModuleCat` isomorphism on the
four-anyon carrier.  The inverse equations are explicit hypotheses: this
bridge does not infer invertibility from a braid relation.
-/
noncomputable def matrixIso
    (M N : Matrix Basis6 Basis6 ℂ)
    (hMN : M * N = 1) (hNM : N * M = 1) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  { hom := matrixHom M
    inv := matrixHom N
    hom_inv_id := by
      rw [matrixHom_comp, hNM, matrixHom_one]
    inv_hom_id := by
      rw [matrixHom_comp, hMN, matrixHom_one] }

@[simp] theorem matrixIso_hom
    (M N : Matrix Basis6 Basis6 ℂ)
    (hMN : M * N = 1) (hNM : N * M = 1) :
    (matrixIso M N hMN hNM).hom = matrixHom M := by
  rfl

@[simp] theorem matrixIso_inv
    (M N : Matrix Basis6 Basis6 ℂ)
    (hMN : M * N = 1) (hNM : N * M = 1) :
    (matrixIso M N hMN hNM).inv = matrixHom N := by
  rfl

theorem matrixHom_artin_of_matrix_artin
    (M N : Matrix Basis6 Basis6 ℂ)
    (h : M * N * M = N * M * N) :
    matrixHom M ≫ matrixHom N ≫ matrixHom M =
      matrixHom N ≫ matrixHom M ≫ matrixHom N := by
  simpa only [matrixHom_comp] using congrArg matrixHom h

noncomputable def endpointOneHom (qNeg4 q3 : ℂ) :
    ModuleCat.of ℂ FourAnyonCarrier ⟶ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixHom (pi6_b1 qNeg4 q3)

noncomputable def endpointFiveHom (qNeg4 q3 : ℂ) :
    ModuleCat.of ℂ FourAnyonCarrier ⟶ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixHom (pi6_b5 qNeg4 q3)

theorem endpointOne_matrix_mul_inverse
    (qNeg4 q3 : ℂ) (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    pi6_b1 qNeg4 q3 * pi6_b1 qNeg4⁻¹ q3⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b1, Matrix.mul_apply, Fin.sum_univ_five, hqNeg4, hq3]

theorem endpointFive_matrix_mul_inverse
    (qNeg4 q3 : ℂ) (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    pi6_b5 qNeg4 q3 * pi6_b5 qNeg4⁻¹ q3⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b5, Matrix.mul_apply, Fin.sum_univ_five, hqNeg4, hq3]

noncomputable def endpointOneIso
    (qNeg4 q3 : ℂ) (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixIso (pi6_b1 qNeg4 q3) (pi6_b1 qNeg4⁻¹ q3⁻¹)
    (endpointOne_matrix_mul_inverse qNeg4 q3 hqNeg4 hq3)
    (by
      simpa only [inv_inv] using
        (endpointOne_matrix_mul_inverse qNeg4⁻¹ q3⁻¹
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3)))

noncomputable def endpointFiveIso
    (qNeg4 q3 : ℂ) (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixIso (pi6_b5 qNeg4 q3) (pi6_b5 qNeg4⁻¹ q3⁻¹)
    (endpointFive_matrix_mul_inverse qNeg4 q3 hqNeg4 hq3)
    (by
      simpa only [inv_inv] using
        (endpointFive_matrix_mul_inverse qNeg4⁻¹ q3⁻¹
          (inv_ne_zero hqNeg4) (inv_ne_zero hq3)))

noncomputable def middleTwoHom (q3 : ℂ) (B : BBlockEntries) :
    ModuleCat.of ℂ FourAnyonCarrier ⟶ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixHom (pi6_b2 q3 B)

theorem middleTwo_matrix_mul_inverse
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hq3 : q3 ≠ 0) :
    pi6_b2 q3 B * pi6_b2 q3⁻¹ Binv = 1 := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hB
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hB
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hB
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hB
  have h00' : B.B00 * Binv.B00 + B.B01 * Binv.B10 = 1 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h00
  have h01' : B.B00 * Binv.B01 + B.B01 * Binv.B11 = 0 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h01
  have h10' : B.B10 * Binv.B00 + B.B11 * Binv.B10 = 0 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h10
  have h11' : B.B10 * Binv.B01 + B.B11 * Binv.B11 = 1 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b2, BBlockEntries.matrix, Matrix.mul_apply,
      Fin.sum_univ_five, h00', h01', h10', h11', hq3]

theorem middleTwo_matrix_inverse_mul
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    pi6_b2 q3⁻¹ Binv * pi6_b2 q3 B = 1 := by
  simpa only [inv_inv] using
    (middleTwo_matrix_mul_inverse q3⁻¹ Binv B hB (inv_ne_zero hq3))

theorem fibonacciBBlockEntries_matrix_mul_inverse
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    BBlockEntries.matrix (fibonacciBBlockEntries q τ s) *
        BBlockEntries.matrix (fibonacciBBlockEntries q⁻¹ τ s) = 1 := by
  rw [fibonacciBBlockEntries_matrix, fibonacciBBlockEntries_matrix]
  exact bMatrix_mul_inv q τ s hs hτ

theorem fibonacciBBlockEntries_matrix_inverse_mul
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    BBlockEntries.matrix (fibonacciBBlockEntries q⁻¹ τ s) *
        BBlockEntries.matrix (fibonacciBBlockEntries q τ s) = 1 := by
  rw [fibonacciBBlockEntries_matrix, fibonacciBBlockEntries_matrix]
  exact bMatrix_inv_mul q τ s hs hτ

theorem middleTwo_fibonacci_matrix_mul_inverse
    (q3 : ℂ) (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) (hq3 : q3 ≠ 0) :
    pi6_b2 q3 (fibonacciBBlockEntries q τ s) *
        pi6_b2 q3⁻¹ (fibonacciBBlockEntries q⁻¹ τ s) = 1 := by
  exact middleTwo_matrix_mul_inverse q3
    (fibonacciBBlockEntries q τ s)
    (fibonacciBBlockEntries q⁻¹ τ s)
    (fibonacciBBlockEntries_matrix_mul_inverse q τ s hs hτ) hq3

theorem middleTwo_fibonacci_matrix_inverse_mul
    (q3 : ℂ) (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) (hq3 : q3 ≠ 0) :
    pi6_b2 q3⁻¹ (fibonacciBBlockEntries q⁻¹ τ s) *
        pi6_b2 q3 (fibonacciBBlockEntries q τ s) = 1 := by
  exact middleTwo_matrix_inverse_mul q3
    (fibonacciBBlockEntries q τ s)
    (fibonacciBBlockEntries q⁻¹ τ s)
    (fibonacciBBlockEntries_matrix_inverse_mul q τ s hs hτ) hq3

theorem middleThree_matrix_mul_inverse
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    pi6_b3 qNeg4 q3 B * pi6_b3 qNeg4⁻¹ q3⁻¹ Binv = 1 := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hB
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hB
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hB
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hB
  have h00' : B.B00 * Binv.B00 + B.B01 * Binv.B10 = 1 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h00
  have h01' : B.B00 * Binv.B01 + B.B01 * Binv.B11 = 0 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h01
  have h10' : B.B10 * Binv.B00 + B.B11 * Binv.B10 = 0 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h10
  have h11' : B.B10 * Binv.B01 + B.B11 * Binv.B11 = 1 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b3, BBlockEntries.matrix, Matrix.mul_apply,
      Fin.sum_univ_five, h00', h01', h10', h11', hqNeg4, hq3]

theorem middleThree_matrix_inverse_mul
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    pi6_b3 qNeg4⁻¹ q3⁻¹ Binv * pi6_b3 qNeg4 q3 B = 1 := by
  simpa only [inv_inv] using
    (middleThree_matrix_mul_inverse qNeg4⁻¹ q3⁻¹ Binv B hB
      (inv_ne_zero hqNeg4) (inv_ne_zero hq3))

theorem middleFour_matrix_mul_inverse
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hq3 : q3 ≠ 0) :
    pi6_b4 q3 B * pi6_b4 q3⁻¹ Binv = 1 := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hB
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hB
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hB
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hB
  have h00' : B.B00 * Binv.B00 + B.B01 * Binv.B10 = 1 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h00
  have h01' : B.B00 * Binv.B01 + B.B01 * Binv.B11 = 0 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h01
  have h10' : B.B10 * Binv.B00 + B.B11 * Binv.B10 = 0 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h10
  have h11' : B.B10 * Binv.B01 + B.B11 * Binv.B11 = 1 := by
    simpa [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] using h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b4, BBlockEntries.matrix, Matrix.mul_apply,
      Fin.sum_univ_five, h00', h01', h10', h11', hq3]

theorem middleFour_matrix_inverse_mul
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    pi6_b4 q3⁻¹ Binv * pi6_b4 q3 B = 1 := by
  simpa only [inv_inv] using
    (middleFour_matrix_mul_inverse q3⁻¹ Binv B hB (inv_ne_zero hq3))

noncomputable def middleThreeHom (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    ModuleCat.of ℂ FourAnyonCarrier ⟶ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixHom (pi6_b3 qNeg4 q3 B)

noncomputable def middleFourHom (q3 : ℂ) (B : BBlockEntries) :
    ModuleCat.of ℂ FourAnyonCarrier ⟶ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixHom (pi6_b4 q3 B)

noncomputable def middleTwoIso
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixIso (pi6_b2 q3 B) (pi6_b2 q3⁻¹ Binv)
    (middleTwo_matrix_mul_inverse q3 B Binv hB hq3)
    (middleTwo_matrix_inverse_mul q3 B Binv hBinv hq3)

noncomputable def middleThreeIso
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixIso (pi6_b3 qNeg4 q3 B) (pi6_b3 qNeg4⁻¹ q3⁻¹ Binv)
    (middleThree_matrix_mul_inverse qNeg4 q3 B Binv hB hqNeg4 hq3)
    (middleThree_matrix_inverse_mul qNeg4 q3 B Binv hBinv hqNeg4 hq3)

noncomputable def middleFourIso
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  matrixIso (pi6_b4 q3 B) (pi6_b4 q3⁻¹ Binv)
    (middleFour_matrix_mul_inverse q3 B Binv hB hq3)
    (middleFour_matrix_inverse_mul q3 B Binv hBinv hq3)

noncomputable def middleTwoFibonacciIso
    (q3 : ℂ) (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  middleTwoIso q3 (fibonacciBBlockEntries q τ s)
    (fibonacciBBlockEntries q⁻¹ τ s)
    (fibonacciBBlockEntries_matrix_mul_inverse q τ s hs hτ)
    (fibonacciBBlockEntries_matrix_inverse_mul q τ s hs hτ) hq3

noncomputable def middleThreeFibonacciIso
    (qNeg4 q3 : ℂ) (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  middleThreeIso qNeg4 q3 (fibonacciBBlockEntries q τ s)
    (fibonacciBBlockEntries q⁻¹ τ s)
    (fibonacciBBlockEntries_matrix_mul_inverse q τ s hs hτ)
    (fibonacciBBlockEntries_matrix_inverse_mul q τ s hs hτ) hqNeg4 hq3

noncomputable def middleFourFibonacciIso
    (q3 : ℂ) (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) (hq3 : q3 ≠ 0) :
    ModuleCat.of ℂ FourAnyonCarrier ≅ ModuleCat.of ℂ FourAnyonCarrier :=
  middleFourIso q3 (fibonacciBBlockEntries q τ s)
    (fibonacciBBlockEntries q⁻¹ τ s)
    (fibonacciBBlockEntries_matrix_mul_inverse q τ s hs hτ)
    (fibonacciBBlockEntries_matrix_inverse_mul q τ s hs hτ) hq3

@[simp] theorem middleTwoIso_hom
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    (middleTwoIso q3 B Binv hB hBinv hq3).hom =
      matrixHom (pi6_b2 q3 B) := by
  rfl

@[simp] theorem middleTwoIso_inv
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    (middleTwoIso q3 B Binv hB hBinv hq3).inv =
      matrixHom (pi6_b2 q3⁻¹ Binv) := by
  rfl

@[simp] theorem middleThreeIso_hom
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (middleThreeIso qNeg4 q3 B Binv hB hBinv hqNeg4 hq3).hom =
      matrixHom (pi6_b3 qNeg4 q3 B) := by
  rfl

@[simp] theorem middleThreeIso_inv
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (middleThreeIso qNeg4 q3 B Binv hB hBinv hqNeg4 hq3).inv =
      matrixHom (pi6_b3 qNeg4⁻¹ q3⁻¹ Binv) := by
  rfl

@[simp] theorem middleFourIso_hom
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    (middleFourIso q3 B Binv hB hBinv hq3).hom =
      matrixHom (pi6_b4 q3 B) := by
  rfl

@[simp] theorem middleFourIso_inv
    (q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hq3 : q3 ≠ 0) :
    (middleFourIso q3 B Binv hB hBinv hq3).inv =
      matrixHom (pi6_b4 q3⁻¹ Binv) := by
  rfl

theorem endpointOneHom_matrix (qNeg4 q3 : ℂ) :
    endpointOneHom qNeg4 q3 = matrixHom (pi6_b1 qNeg4 q3) := by
  rfl

theorem endpointFiveHom_matrix (qNeg4 q3 : ℂ) :
    endpointFiveHom qNeg4 q3 = matrixHom (pi6_b5 qNeg4 q3) := by
  rfl

theorem middleTwoHom_matrix (q3 : ℂ) (B : BBlockEntries) :
    middleTwoHom q3 B = matrixHom (pi6_b2 q3 B) := by
  rfl

theorem middleThreeHom_matrix (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    middleThreeHom qNeg4 q3 B = matrixHom (pi6_b3 qNeg4 q3 B) := by
  rfl

theorem middleFourHom_matrix (q3 : ℂ) (B : BBlockEntries) :
    middleFourHom q3 B = matrixHom (pi6_b4 q3 B) := by
  rfl

theorem endpointOneHom_apply_component
    (qNeg4 q3 : ℂ) (x : FourAnyonCarrier) (i : Basis6) :
    (endpointOneHom qNeg4 q3) x i =
      Matrix.mulVec (pi6_b1 qNeg4 q3) x i := by
  rfl

theorem endpointFiveHom_apply_component
    (qNeg4 q3 : ℂ) (x : FourAnyonCarrier) (i : Basis6) :
    (endpointFiveHom qNeg4 q3) x i =
      Matrix.mulVec (pi6_b5 qNeg4 q3) x i := by
  rfl

theorem middleTwoHom_apply_component
    (q3 : ℂ) (B : BBlockEntries) (x : FourAnyonCarrier) (i : Basis6) :
    (middleTwoHom q3 B) x i =
      Matrix.mulVec (pi6_b2 q3 B) x i := by
  rfl

theorem middleThreeHom_apply_component
    (qNeg4 q3 : ℂ) (B : BBlockEntries) (x : FourAnyonCarrier) (i : Basis6) :
    (middleThreeHom qNeg4 q3 B) x i =
      Matrix.mulVec (pi6_b3 qNeg4 q3 B) x i := by
  rfl

theorem middleFourHom_apply_component
    (q3 : ℂ) (B : BBlockEntries) (x : FourAnyonCarrier) (i : Basis6) :
    (middleFourHom q3 B) x i =
      Matrix.mulVec (pi6_b4 q3 B) x i := by
  rfl

theorem middleTwoHom_fibonacci_block_entries
    (q : Units ℂ) (τ s : ℂ) (i j : Fin 2) :
    (pi6_b2 q (fibonacciBBlockEntries q τ s) (i.castLE (by omega))
      (j.castLE (by omega))) =
      fibonacciBMatrix q τ s i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem middleTwoHom_fibonacci_repeated_blocks
    (q : Units ℂ) (τ s : ℂ) :
    pi6_b2 q (fibonacciBBlockEntries q τ s) 0 0 =
        fibonacciBMatrix q τ s 0 0 ∧
      pi6_b2 q (fibonacciBBlockEntries q τ s) 0 1 =
        fibonacciBMatrix q τ s 0 1 ∧
      pi6_b2 q (fibonacciBBlockEntries q τ s) 1 0 =
        fibonacciBMatrix q τ s 1 0 ∧
      pi6_b2 q (fibonacciBBlockEntries q τ s) 1 1 =
        fibonacciBMatrix q τ s 1 1 ∧
      pi6_b2 q (fibonacciBBlockEntries q τ s) 3 3 =
        fibonacciBMatrix q τ s 0 0 ∧
      pi6_b2 q (fibonacciBBlockEntries q τ s) 3 4 =
        fibonacciBMatrix q τ s 0 1 ∧
      pi6_b2 q (fibonacciBBlockEntries q τ s) 4 3 =
        fibonacciBMatrix q τ s 1 0 ∧
      pi6_b2 q (fibonacciBBlockEntries q τ s) 4 4 =
        fibonacciBMatrix q τ s 1 1 := by
  simpa [fibonacciBBlockEntries] using
    (pi6_b2_repeated_B_blocks q (fibonacciBBlockEntries q τ s))

theorem adjacentArtinHoms_of_matrix_relations
    (qNeg4 q3 : ℂ) (B : BBlockEntries)
    (h12 : pi6_b1 qNeg4 q3 * pi6_b2 q3 B * pi6_b1 qNeg4 q3 =
      pi6_b2 q3 B * pi6_b1 qNeg4 q3 * pi6_b2 q3 B)
    (h23 : pi6_b2 q3 B * pi6_b3 qNeg4 q3 B * pi6_b2 q3 B =
      pi6_b3 qNeg4 q3 B * pi6_b2 q3 B * pi6_b3 qNeg4 q3 B)
    (h34 : pi6_b3 qNeg4 q3 B * pi6_b4 q3 B * pi6_b3 qNeg4 q3 B =
      pi6_b4 q3 B * pi6_b3 qNeg4 q3 B * pi6_b4 q3 B)
    (h45 : pi6_b4 q3 B * pi6_b5 qNeg4 q3 * pi6_b4 q3 B =
      pi6_b5 qNeg4 q3 * pi6_b4 q3 B * pi6_b5 qNeg4 q3) :
    (endpointOneHom qNeg4 q3 ≫ middleTwoHom q3 B ≫ endpointOneHom qNeg4 q3 =
      middleTwoHom q3 B ≫ endpointOneHom qNeg4 q3 ≫ middleTwoHom q3 B) ∧
    (middleTwoHom q3 B ≫ middleThreeHom qNeg4 q3 B ≫ middleTwoHom q3 B =
      middleThreeHom qNeg4 q3 B ≫ middleTwoHom q3 B ≫ middleThreeHom qNeg4 q3 B) ∧
    (middleThreeHom qNeg4 q3 B ≫ middleFourHom q3 B ≫ middleThreeHom qNeg4 q3 B =
      middleFourHom q3 B ≫ middleThreeHom qNeg4 q3 B ≫ middleFourHom q3 B) ∧
    (middleFourHom q3 B ≫ endpointFiveHom qNeg4 q3 ≫ middleFourHom q3 B =
      endpointFiveHom qNeg4 q3 ≫ middleFourHom q3 B ≫ endpointFiveHom qNeg4 q3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact matrixHom_artin_of_matrix_artin _ _ h12
  · exact matrixHom_artin_of_matrix_artin _ _ h23
  · exact matrixHom_artin_of_matrix_artin _ _ h34
  · exact matrixHom_artin_of_matrix_artin _ _ h45

/-! The first genuinely overlapping pair is controlled by five scalar
identities.  This helper exposes that finite algebraic reduction without
claiming that the Fibonacci specialization has already discharged them. -/

theorem middleTwo_middleThree_artin_of_overlap
    (x r : ℂ) (B : BBlockEntries)
    (h00 : B.B00 ^ 2 * x - B.B00 * x ^ 2 + B.B01 * B.B10 * r = 0)
    (h01 : -B.B00 * x - B.B11 * r + r * x = 0)
    (h11 : B.B01 * B.B10 * x + B.B11 ^ 2 * r - B.B11 * r ^ 2 = 0)
    (h22 : -B.B00 ^ 2 * r + B.B00 * r ^ 2 -
      B.B01 * B.B10 * B.B11 = 0)
    (h24 : B.B00 * r + B.B11 ^ 2 - B.B11 * r = 0) :
    pi6_b2 r B * pi6_b3 x r B * pi6_b2 r B =
      pi6_b3 x r B * pi6_b2 r B * pi6_b3 x r B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b2, pi6_b3,
      Matrix.mul_apply, Fin.sum_univ_five] at *
  all_goals ring_nf at *
  all_goals try linear_combination h00
  all_goals try linear_combination (-B.B01) * h01
  all_goals try linear_combination (-B.B10) * h01
  all_goals try linear_combination h11
  all_goals try linear_combination h22
  all_goals try linear_combination B.B01 * h24
  all_goals try linear_combination B.B10 * h24
  · linear_combination (-B.B01) * h24
  · linear_combination (-1) * h22
  · linear_combination (-B.B10) * h24

/-! The first, second, and fourth scalar conditions are exactly the entries of
the ordinary two-channel Artin relation.  This bridge isolates the two extra
overlap identities which are specific to the three-channel realization. -/

theorem middleTwo_middleThree_artin_of_block_artin
    (x r : ℂ) (B : BBlockEntries)
    (hArtin :
      !![x, 0; 0, r] * B.matrix * !![x, 0; 0, r] =
        B.matrix * !![x, 0; 0, r] * B.matrix)
    (h01 : -B.B00 * x - B.B11 * r + r * x = 0)
    (h22 : B.B00 ^ 2 * r - B.B00 * r ^ 2 +
      B.B01 * B.B10 * B.B11 = 0)
    (h24 : B.B00 * r + B.B11 ^ 2 - B.B11 * r = 0) :
    pi6_b2 r B * pi6_b3 x r B * pi6_b2 r B =
      pi6_b3 x r B * pi6_b2 r B * pi6_b3 x r B := by
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hArtin
  have h11 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hArtin
  simp [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  apply middleTwo_middleThree_artin_of_overlap x r B
  · linear_combination -h00
  · exact h01
  · linear_combination -h11
  · linear_combination -h22
  · exact h24

theorem fibonacci_overlap_h24
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    (fibonacciBBlockEntries q τ s).B00 * (q : ℂ) ^ 3 +
        (fibonacciBBlockEntries q τ s).B11 ^ 2 -
        (fibonacciBBlockEntries q τ s).B11 * (q : ℂ) ^ 3 = 0 := by
  dsimp [fibonacciBBlockEntries]
  rw [fibonacciBMatrix_apply_zero_zero,
    fibonacciBMatrix_apply_one_one, hq_inv, hq_pow3]
  rw [hτ] at *
  rw [← pow_two s]
  rw [hs]
  have hq6 : (q : ℂ) ^ 6 = -(q : ℂ) := q_pow_6 (q : ℂ) hq5
  have hq7 : (q : ℂ) ^ 7 = -(q : ℂ) ^ 2 := q_pow_7 (q : ℂ) hq5
  have hq8 : (q : ℂ) ^ 8 = -(q : ℂ) ^ 3 := q_pow_8 (q : ℂ) hq5
  have hq9 : (q : ℂ) ^ 9 = -(q : ℂ) ^ 4 := q_pow_9 (q : ℂ) hq5
  have hq10 : (q : ℂ) ^ 10 = 1 := by
    calc
      (q : ℂ) ^ 10 = (q : ℂ) ^ 5 * (q : ℂ) ^ 5 := by ring
      _ = 1 := by rw [hq5]; ring
  have hq11 : (q : ℂ) ^ 11 = (q : ℂ) := by
    calc
      (q : ℂ) ^ 11 = (q : ℂ) ^ 5 * (q : ℂ) ^ 6 := by ring
      _ = (q : ℂ) := by rw [hq5, hq6]; ring
  have hq12 : (q : ℂ) ^ 12 = (q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 12 = (q : ℂ) ^ 5 * (q : ℂ) ^ 7 := by ring
      _ = (q : ℂ) ^ 2 := by rw [hq5, hq7]; ring
  have hq13 : (q : ℂ) ^ 13 = (q : ℂ) ^ 3 := by
    calc
      (q : ℂ) ^ 13 = (q : ℂ) ^ 5 * (q : ℂ) ^ 8 := by ring
      _ = (q : ℂ) ^ 3 := by rw [hq5, hq8]; ring
  have hq14 : (q : ℂ) ^ 14 = (q : ℂ) ^ 4 := by
    calc
      (q : ℂ) ^ 14 = (q : ℂ) ^ 5 * (q : ℂ) ^ 9 := by ring
      _ = (q : ℂ) ^ 4 := by rw [hq5, hq9]; ring
  have hq15 : (q : ℂ) ^ 15 = -1 := by
    calc
      (q : ℂ) ^ 15 = (q : ℂ) ^ 5 * (q : ℂ) ^ 10 := by ring
      _ = -1 := by rw [hq5, hq10]; ring
  have hq16 : (q : ℂ) ^ 16 = -(q : ℂ) := by
    calc
      (q : ℂ) ^ 16 = (q : ℂ) ^ 5 * (q : ℂ) ^ 11 := by ring
      _ = -(q : ℂ) := by rw [hq5, hq11]; ring
  have hq17 : (q : ℂ) ^ 17 = -(q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 17 = (q : ℂ) ^ 5 * (q : ℂ) ^ 12 := by ring
      _ = -(q : ℂ) ^ 2 := by rw [hq5, hq12]; ring
  have hq18 : (q : ℂ) ^ 18 = -(q : ℂ) ^ 3 := by
    calc
      (q : ℂ) ^ 18 = (q : ℂ) ^ 5 * (q : ℂ) ^ 13 := by ring
      _ = -(q : ℂ) ^ 3 := by rw [hq5, hq13]; ring
  ring_nf at *
  simp only [hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14,
    hq15, hq16, hq17, hq18]
  ring_nf

theorem fibonacci_overlap_h22
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    (fibonacciBBlockEntries q τ s).B00 ^ 2 * (q : ℂ) ^ 3 -
        (fibonacciBBlockEntries q τ s).B00 * (q : ℂ) ^ 6 +
        (fibonacciBBlockEntries q τ s).B01 *
          (fibonacciBBlockEntries q τ s).B10 *
          (fibonacciBBlockEntries q τ s).B11 = 0 := by
  dsimp [fibonacciBBlockEntries]
  rw [fibonacciBMatrix_apply_zero_zero,
    fibonacciBMatrix_apply_zero_one,
    fibonacciBMatrix_apply_one_zero,
    fibonacciBMatrix_apply_one_one, hq_inv, hq_pow3]
  rw [hτ] at *
  rw [← pow_two s, hs]
  have hq6 : (q : ℂ) ^ 6 = -(q : ℂ) := q_pow_6 (q : ℂ) hq5
  have hq7 : (q : ℂ) ^ 7 = -(q : ℂ) ^ 2 := q_pow_7 (q : ℂ) hq5
  have hq8 : (q : ℂ) ^ 8 = -(q : ℂ) ^ 3 := q_pow_8 (q : ℂ) hq5
  have hq9 : (q : ℂ) ^ 9 = -(q : ℂ) ^ 4 := q_pow_9 (q : ℂ) hq5
  have hq10 : (q : ℂ) ^ 10 = 1 := by
    calc
      (q : ℂ) ^ 10 = (q : ℂ) ^ 5 * (q : ℂ) ^ 5 := by ring
      _ = 1 := by rw [hq5]; ring
  have hq11 : (q : ℂ) ^ 11 = (q : ℂ) := by
    calc
      (q : ℂ) ^ 11 = (q : ℂ) ^ 5 * (q : ℂ) ^ 6 := by ring
      _ = (q : ℂ) := by rw [hq5, hq6]; ring
  have hq12 : (q : ℂ) ^ 12 = (q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 12 = (q : ℂ) ^ 5 * (q : ℂ) ^ 7 := by ring
      _ = (q : ℂ) ^ 2 := by rw [hq5, hq7]; ring
  have hq13 : (q : ℂ) ^ 13 = (q : ℂ) ^ 3 := by
    calc
      (q : ℂ) ^ 13 = (q : ℂ) ^ 5 * (q : ℂ) ^ 8 := by ring
      _ = (q : ℂ) ^ 3 := by rw [hq5, hq8]; ring
  have hq14 : (q : ℂ) ^ 14 = (q : ℂ) ^ 4 := by
    calc
      (q : ℂ) ^ 14 = (q : ℂ) ^ 5 * (q : ℂ) ^ 9 := by ring
      _ = (q : ℂ) ^ 4 := by rw [hq5, hq9]; ring
  have hq15 : (q : ℂ) ^ 15 = -1 := by
    calc
      (q : ℂ) ^ 15 = (q : ℂ) ^ 5 * (q : ℂ) ^ 10 := by ring
      _ = -1 := by rw [hq5, hq10]; ring
  have hq16 : (q : ℂ) ^ 16 = -(q : ℂ) := by
    calc
      (q : ℂ) ^ 16 = (q : ℂ) ^ 5 * (q : ℂ) ^ 11 := by ring
      _ = -(q : ℂ) := by rw [hq5, hq11]; ring
  have hq17 : (q : ℂ) ^ 17 = -(q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 17 = (q : ℂ) ^ 5 * (q : ℂ) ^ 12 := by ring
      _ = -(q : ℂ) ^ 2 := by rw [hq5, hq12]; ring
  have hq18 : (q : ℂ) ^ 18 = -(q : ℂ) ^ 3 := by
    calc
      (q : ℂ) ^ 18 = (q : ℂ) ^ 5 * (q : ℂ) ^ 13 := by ring
      _ = -(q : ℂ) ^ 3 := by rw [hq5, hq13]; ring
  have hq19 : (q : ℂ) ^ 19 = -(q : ℂ) ^ 4 := by
    calc
      (q : ℂ) ^ 19 = (q : ℂ) ^ 5 * (q : ℂ) ^ 14 := by ring
      _ = -(q : ℂ) ^ 4 := by rw [hq5, hq14]; ring
  have hq20 : (q : ℂ) ^ 20 = 1 := by
    calc
      (q : ℂ) ^ 20 = (q : ℂ) ^ 5 * (q : ℂ) ^ 15 := by ring
      _ = 1 := by rw [hq5, hq15]; ring
  have hq21 : (q : ℂ) ^ 21 = (q : ℂ) := by
    calc
      (q : ℂ) ^ 21 = (q : ℂ) ^ 5 * (q : ℂ) ^ 16 := by ring
      _ = (q : ℂ) := by rw [hq5, hq16]; ring
  ring_nf at *
  simp only [hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14,
    hq15, hq16, hq17, hq18, hq19, hq20, hq21, hs]
  ring_nf
  rw [hq5, hq6, hq7]
  ring_nf
  linear_combination -14 * h_poly

theorem fibonacci_overlap_h01
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    -(fibonacciBBlockEntries q τ s).B00 * (-(q : ℂ)) -
        (fibonacciBBlockEntries q τ s).B11 * (q : ℂ) ^ 3 +
        (q : ℂ) ^ 3 * (-(q : ℂ)) = 0 := by
  dsimp [fibonacciBBlockEntries]
  rw [fibonacciBMatrix_apply_zero_zero,
    fibonacciBMatrix_apply_one_one, hq_inv, hq_pow3]
  rw [hτ] at *
  rw [← pow_two s, hs]
  have hq6 : (q : ℂ) ^ 6 = -(q : ℂ) := q_pow_6 (q : ℂ) hq5
  have hq7 : (q : ℂ) ^ 7 = -(q : ℂ) ^ 2 := q_pow_7 (q : ℂ) hq5
  have hq8 : (q : ℂ) ^ 8 = -(q : ℂ) ^ 3 := q_pow_8 (q : ℂ) hq5
  have hq9 : (q : ℂ) ^ 9 = -(q : ℂ) ^ 4 := q_pow_9 (q : ℂ) hq5
  ring_nf at *
  simp only [hq5, hq6, hq7, hq8, hq9]
  have hq10 : (q : ℂ) ^ 10 = 1 := by
    calc
      (q : ℂ) ^ 10 = (q : ℂ) ^ 5 * (q : ℂ) ^ 5 := by ring
      _ = 1 := by rw [hq5]; ring
  have hq11 : (q : ℂ) ^ 11 = (q : ℂ) := by
    calc
      (q : ℂ) ^ 11 = (q : ℂ) ^ 5 * (q : ℂ) ^ 6 := by ring
      _ = (q : ℂ) := by rw [hq5, hq6]; ring
  have hq12 : (q : ℂ) ^ 12 = (q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 12 = (q : ℂ) ^ 5 * (q : ℂ) ^ 7 := by ring
      _ = (q : ℂ) ^ 2 := by rw [hq5, hq7]; ring
  simp only [hq10, hq11, hq12]
  ring_nf
  linear_combination -h_poly

theorem middleTwo_middleThree_fibonacci_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    middleTwoHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        middleThreeHom (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) ≫
        middleTwoHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) =
      middleThreeHom (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) ≫
        middleTwoHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        middleThreeHom (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) := by
  apply matrixHom_artin_of_matrix_artin
  apply middleTwo_middleThree_artin_of_block_artin
  · have hq_inv' : ((q : ℂ) ^ 4)⁻¹ = -(q : ℂ) := by
      simpa [zpow_neg, inv_pow] using hq_inv
    have hr : !![-(q : ℂ), 0; 0, (q : ℂ) ^ 3] =
        fibonacciRMatrix q := by
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [fibonacciRMatrix] using hq_inv'.symm
      · simp [fibonacciRMatrix]
      · simp [fibonacciRMatrix]
      · simp [fibonacciRMatrix]
        rfl
    rw [hr, fibonacciBBlockEntries_matrix]
    exact fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs
  · simpa [fibonacciBBlockEntries] using
      (fibonacci_overlap_h01 q τ s hq_inv hq_pow3 hq5 h_poly hτ hs)
  · have h := fibonacci_overlap_h22 q τ s hq_inv hq_pow3 hq5 h_poly hτ hs
    convert h using 1 <;> simp only [fibonacciBBlockEntries] <;> ring
  · simpa [fibonacciBBlockEntries] using
      (fibonacci_overlap_h24 q τ s hq_inv hq_pow3 hq5 hτ hs)


/-- A two-channel Artin relation lifts through the repeated `Fin 5` block
    used by the first two low-anyon generators. -/
theorem endpointOne_middleTwo_artin_of_block
    (r0 c : ℂ) (B : BBlockEntries)
    (h : !![r0, 0; 0, c] * B.matrix * !![r0, 0; 0, c] =
      B.matrix * !![r0, 0; 0, c] * B.matrix) :
    pi6_b1 r0 c * pi6_b2 c B * pi6_b1 r0 c =
      pi6_b2 c B * pi6_b1 r0 c * pi6_b2 c B := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
  simp [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b1, pi6_b2, BBlockEntries.matrix, Matrix.mul_apply,
      Fin.sum_univ_five, Fin.sum_univ_two, h00, h01, h10, h11]

/-- The canonical Fibonacci specialization of the repeated-block lift. -/
theorem endpointOne_middleTwo_fibonacci_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    endpointOneHom (-(q : ℂ)) ((q : ℂ) ^ 3) ≫
        middleTwoHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        endpointOneHom (-(q : ℂ)) ((q : ℂ) ^ 3) =
      middleTwoHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        endpointOneHom (-(q : ℂ)) ((q : ℂ) ^ 3) ≫
        middleTwoHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) := by
  apply matrixHom_artin_of_matrix_artin
  apply endpointOne_middleTwo_artin_of_block
  have hq_inv' : ((q : ℂ) ^ 4)⁻¹ = -(q : ℂ) := by
    simpa [zpow_neg, inv_pow] using hq_inv
  have hr : !![-(q : ℂ), 0; 0, (q : ℂ) ^ 3] =
      fibonacciRMatrix q := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [fibonacciRMatrix] using hq_inv'.symm
    · simp [fibonacciRMatrix]
    · simp [fibonacciRMatrix]
    · simp [fibonacciRMatrix]
      rfl
  rw [hr, fibonacciBBlockEntries_matrix]
  exact fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs

/-! The other endpoint relation has the same two-channel shape, with the
    repeated `B` blocks of `b₄` paired against the diagonal `R` entries of
    `b₅`. -/

theorem middleFour_endpointFive_artin_of_block
    (r0 c : ℂ) (B : BBlockEntries)
    (h : B.matrix * !![r0, 0; 0, c] * B.matrix =
      !![r0, 0; 0, c] * B.matrix * !![r0, 0; 0, c]) :
    pi6_b4 c B * pi6_b5 r0 c * pi6_b4 c B =
      pi6_b5 r0 c * pi6_b4 c B * pi6_b5 r0 c := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
  simp [BBlockEntries.matrix, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b4, pi6_b5, BBlockEntries.matrix, Matrix.mul_apply,
      Fin.sum_univ_five, Fin.sum_univ_two, h00, h01, h10, h11]

theorem middleFour_endpointFive_fibonacci_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    middleFourHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        endpointFiveHom (-(q : ℂ)) ((q : ℂ) ^ 3) ≫
        middleFourHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) =
      endpointFiveHom (-(q : ℂ)) ((q : ℂ) ^ 3) ≫
        middleFourHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        endpointFiveHom (-(q : ℂ)) ((q : ℂ) ^ 3) := by
  apply matrixHom_artin_of_matrix_artin
  apply middleFour_endpointFive_artin_of_block
  have hq_inv' : ((q : ℂ) ^ 4)⁻¹ = -(q : ℂ) := by
    simpa [zpow_neg, inv_pow] using hq_inv
  have hr : !![-(q : ℂ), 0; 0, (q : ℂ) ^ 3] =
      fibonacciRMatrix q := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [fibonacciRMatrix] using hq_inv'.symm
    · simp [fibonacciRMatrix]
    · simp [fibonacciRMatrix]
    · simp [fibonacciRMatrix]
      rfl
  rw [fibonacciBBlockEntries_matrix, hr]
  exact (fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs).symm

set_option maxHeartbeats 1000000 in
theorem middleThree_middleFour_fibonacci_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    middleThreeHom (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) ≫
        middleFourHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        middleThreeHom (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) =
      middleFourHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) ≫
        middleThreeHom (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) ≫
        middleFourHom ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) := by
  apply matrixHom_artin_of_matrix_artin
  ext i j
  have hq6 : (q : ℂ) ^ 6 = -(q : ℂ) := q_pow_6 (q : ℂ) hq5
  have hq7 : (q : ℂ) ^ 7 = -(q : ℂ) ^ 2 := q_pow_7 (q : ℂ) hq5
  have hq8 : (q : ℂ) ^ 8 = -(q : ℂ) ^ 3 := q_pow_8 (q : ℂ) hq5
  have hq9 : (q : ℂ) ^ 9 = -(q : ℂ) ^ 4 := q_pow_9 (q : ℂ) hq5
  have hq10 : (q : ℂ) ^ 10 = 1 := by
    calc
      (q : ℂ) ^ 10 = (q : ℂ) ^ 5 * (q : ℂ) ^ 5 := by ring
      _ = 1 := by rw [hq5]; ring
  have hq11 : (q : ℂ) ^ 11 = (q : ℂ) := by
    calc
      (q : ℂ) ^ 11 = (q : ℂ) ^ 5 * (q : ℂ) ^ 6 := by ring
      _ = (q : ℂ) := by rw [hq5, hq6]; ring
  have hq12 : (q : ℂ) ^ 12 = (q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 12 = (q : ℂ) ^ 5 * (q : ℂ) ^ 7 := by ring
      _ = (q : ℂ) ^ 2 := by rw [hq5, hq7]; ring
  have hq13 : (q : ℂ) ^ 13 = (q : ℂ) ^ 3 := by
    calc
      (q : ℂ) ^ 13 = (q : ℂ) ^ 5 * (q : ℂ) ^ 8 := by ring
      _ = (q : ℂ) ^ 3 := by rw [hq5, hq8]; ring
  have hq14 : (q : ℂ) ^ 14 = (q : ℂ) ^ 4 := by
    calc
      (q : ℂ) ^ 14 = (q : ℂ) ^ 5 * (q : ℂ) ^ 9 := by ring
      _ = (q : ℂ) ^ 4 := by rw [hq5, hq9]; ring
  have hq15 : (q : ℂ) ^ 15 = -1 := by
    calc
      (q : ℂ) ^ 15 = (q : ℂ) ^ 5 * (q : ℂ) ^ 10 := by ring
      _ = -1 := by rw [hq5, hq10]; ring
  have hq16 : (q : ℂ) ^ 16 = -(q : ℂ) := by
    calc
      (q : ℂ) ^ 16 = (q : ℂ) ^ 5 * (q : ℂ) ^ 11 := by ring
      _ = -(q : ℂ) := by rw [hq5, hq11]; ring
  have hq17 : (q : ℂ) ^ 17 = -(q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 17 = (q : ℂ) ^ 5 * (q : ℂ) ^ 12 := by ring
      _ = -(q : ℂ) ^ 2 := by rw [hq5, hq12]; ring
  have hq18 : (q : ℂ) ^ 18 = -(q : ℂ) ^ 3 := by
    calc
      (q : ℂ) ^ 18 = (q : ℂ) ^ 5 * (q : ℂ) ^ 13 := by ring
      _ = -(q : ℂ) ^ 3 := by rw [hq5, hq13]; ring
  have hq19 : (q : ℂ) ^ 19 = -(q : ℂ) ^ 4 := by
    calc
      (q : ℂ) ^ 19 = (q : ℂ) ^ 5 * (q : ℂ) ^ 14 := by ring
      _ = -(q : ℂ) ^ 4 := by rw [hq5, hq14]; ring
  have hq20 : (q : ℂ) ^ 20 = 1 := by
    calc
      (q : ℂ) ^ 20 = (q : ℂ) ^ 5 * (q : ℂ) ^ 15 := by ring
      _ = 1 := by rw [hq5, hq15]; ring
  have hq21 : (q : ℂ) ^ 21 = (q : ℂ) := by
    calc
      (q : ℂ) ^ 21 = (q : ℂ) ^ 5 * (q : ℂ) ^ 16 := by ring
      _ = (q : ℂ) := by rw [hq5, hq16]; ring
  have hq22 : (q : ℂ) ^ 22 = (q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ 22 = (q : ℂ) ^ 5 * (q : ℂ) ^ 17 := by ring
      _ = (q : ℂ) ^ 2 := by rw [hq5, hq17]; ring
  have hq23 : (q : ℂ) ^ 23 = (q : ℂ) ^ 3 := by
    calc
      (q : ℂ) ^ 23 = (q : ℂ) ^ 5 * (q : ℂ) ^ 18 := by ring
      _ = (q : ℂ) ^ 3 := by rw [hq5, hq18]; ring
  have hq24 : (q : ℂ) ^ 24 = (q : ℂ) ^ 4 := by
    calc
      (q : ℂ) ^ 24 = (q : ℂ) ^ 5 * (q : ℂ) ^ 19 := by ring
      _ = (q : ℂ) ^ 4 := by rw [hq5, hq19]; ring
  have hs4 : s ^ 4 = τ ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = τ ^ 2 := by rw [hs]
  have hs5 : s ^ 5 = s * τ ^ 2 := by
    calc
      s ^ 5 = s * (s ^ 2) ^ 2 := by ring
      _ = s * τ ^ 2 := by rw [hs]
  have hq4 : (q : ℂ) ^ 4 = (q : ℂ) ^ 3 - (q : ℂ) ^ 2 +
      (q : ℂ) - 1 := by
    linear_combination h_poly
  have hs2q : s ^ 2 = (q : ℂ) ^ 2 - (q : ℂ) ^ 3 := by
    rw [hs, hτ]
  have hs3q : s ^ 3 = s * ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) := by rw [hs2q]
  have hs4q : s ^ 4 = ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) ^ 2 := by rw [hs2q]
  have hs5q : s ^ 5 = s * ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) ^ 2 := by
    calc
      s ^ 5 = s * (s ^ 2) ^ 2 := by ring
      _ = s * ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) ^ 2 := by rw [hs2q]
  fin_cases i <;> fin_cases j <;>
    simp [pi6_b3, pi6_b4, fibonacciBBlockEntries,
      fibonacciBMatrix_apply_zero_zero,
      fibonacciBMatrix_apply_zero_one,
      fibonacciBMatrix_apply_one_zero,
      fibonacciBMatrix_apply_one_one,
      Matrix.mul_apply, Fin.sum_univ_five,
      hq_inv, hq_pow3, hτ, hs]
  all_goals try rw [hs5q]
  all_goals try rw [hs4q]
  all_goals try rw [hs3q]
  all_goals try rw [hs2q]
  all_goals try rw [hq24]
  all_goals try rw [hq23]
  all_goals try rw [hq22]
  all_goals try rw [hq21]
  all_goals try rw [hq20]
  all_goals try rw [hq19]
  all_goals try rw [hq18]
  all_goals try rw [hq17]
  all_goals try rw [hq16]
  all_goals try rw [hq15]
  all_goals try rw [hq14]
  all_goals try rw [hq13]
  all_goals try rw [hq12]
  all_goals try rw [hq11]
  all_goals try rw [hq10]
  all_goals try rw [hq9]
  all_goals try rw [hq8]
  all_goals try rw [hq7]
  all_goals try rw [hq6]
  all_goals try rw [hq5]
  all_goals ring_nf
  all_goals (try simp [hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11,
    hq12, hq13, hq14, hq15, hq16, hq17, hq18, hq19, hq20, hq21,
    hq22, hq23, hq24, hs2q, hs3q, hs4q, hs5q])
  all_goals ring_nf
  all_goals (try simp only [hq4, hq5, hq6, hq7, hq8, hq9, hq10,
    hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, hq19, hq20,
    hq21, hq22, hq23, hq24, hs2q, hs3q, hs4q, hs5q])
  all_goals ring_nf
  all_goals try linear_combination 6 * h_poly
  all_goals try linear_combination (-4 * s) * h_poly
  all_goals try linear_combination 14 * h_poly
  all_goals try linear_combination (-14) * h_poly
  all_goals try linear_combination (-6) * h_poly

end InfoGeometry.Categorical.FibonacciFourAnyonCarrier
