import InfoGeometry.Categorical.FibonacciFourAnyonCarrier

/-!
# Matrix-level adjacent Artin identities for the six-anyon templates

This owner exposes the two endpoint identities on the native `Basis6` matrix
carrier.  The middle identities remain owned by the corresponding four-anyon
block theorems; no symbolic braid relation is promoted without the explicit
Fibonacci parameter hypotheses.
-/

namespace InfoGeometry.Categorical.FibonacciSixAnyonMatrixArtin

open CategoryTheory
open InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciFourAnyonCarrier

theorem endpointOne_middleTwo_fibonacci_matrix_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    pi6_b1 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b1 (-(q : ℂ)) ((q : ℂ) ^ 3) =
      pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b1 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) := by
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

theorem middleFour_endpointFive_fibonacci_matrix_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b5 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) =
      pi6_b5 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b5 (-(q : ℂ)) ((q : ℂ) ^ 3) := by
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

theorem middleTwo_middleThree_fibonacci_matrix_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) =
      pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) := by
  have h := middleTwo_middleThree_fibonacci_artin q τ s hq_inv hq_pow3
    hq5 h_poly hτ hs
  change (((matrixHom _) ≫ (matrixHom _) ≫ (matrixHom _)) =
    ((matrixHom _) ≫ (matrixHom _) ≫ (matrixHom _))) at h
  have h' := congrArg ModuleCat.Hom.hom h
  apply Matrix.toLin'.injective
  simpa [matrixHom, Matrix.toLin'_mul] using h'

theorem middleThree_middleFour_fibonacci_matrix_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) =
      pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) := by
  have h := middleThree_middleFour_fibonacci_artin q τ s hq_inv hq_pow3
    hq5 h_poly hτ hs
  change (((matrixHom _) ≫ (matrixHom _) ≫ (matrixHom _)) =
    ((matrixHom _) ≫ (matrixHom _) ≫ (matrixHom _))) at h
  have h' := congrArg ModuleCat.Hom.hom h
  apply Matrix.toLin'.injective
  simpa [matrixHom, Matrix.toLin'_mul] using h'

theorem sixAnyon_adjacent_artin_packet
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    (pi6_b1 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b1 (-(q : ℂ)) ((q : ℂ) ^ 3) =
      pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b1 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s)) ∧
    (pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) =
      pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b2 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s)) ∧
    (pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) =
      pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b3 (-(q : ℂ)) ((q : ℂ) ^ 3)
          (fibonacciBBlockEntries q τ s) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s)) ∧
    (pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b5 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) =
      pi6_b5 (-(q : ℂ)) ((q : ℂ) ^ 3) *
        pi6_b4 ((q : ℂ) ^ 3) (fibonacciBBlockEntries q τ s) *
        pi6_b5 (-(q : ℂ)) ((q : ℂ) ^ 3)) := by
  exact ⟨endpointOne_middleTwo_fibonacci_matrix_artin q τ s hq_inv
      hq_pow3 hq5 h_poly hτ hs,
    middleTwo_middleThree_fibonacci_matrix_artin q τ s hq_inv
      hq_pow3 hq5 h_poly hτ hs,
    middleThree_middleFour_fibonacci_matrix_artin q τ s hq_inv
      hq_pow3 hq5 h_poly hτ hs,
    middleFour_endpointFive_fibonacci_matrix_artin q τ s hq_inv
      hq_pow3 hq5 h_poly hτ hs⟩

end InfoGeometry.Categorical.FibonacciSixAnyonMatrixArtin
