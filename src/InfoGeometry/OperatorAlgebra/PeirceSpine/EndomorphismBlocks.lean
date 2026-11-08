import InfoGeometry.OperatorAlgebra.PeirceSpine.CornerChargeSectors

/-!
# Supported blocks of arbitrary endomorphisms

Three orthogonal projections on the additive carrier give nine ordered blocks
of its full endomorphism ring. This construction uses Peirce supports, not
separation of integer eigenvalues, and therefore does not divide by two.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.LieJordan
variable {B : Type*} [Ring B]

/-- Ordered sectors: negative corner, even part, positive corner. -/
def threePeirceProjection (P : B) : Fin 3 → Module.End ℤ B :=
  ![sandwichOp ℤ (1 - P) P, InfoGeometry.Core.PeirceGrading.even P,
    sandwichOp ℤ P (1 - P)]

/-- Output sector i, input sector j. -/
def endomorphismBlock (P : B) (i j : Fin 3) (K : Module.End ℤ B) :
    Module.End ℤ B := threePeirceProjection P i * K * threePeirceProjection P j

theorem threePeirceProjection_sum (P : B) :
    ∑ i, threePeirceProjection P i = 1 := by
  ext X
  simp [Fin.sum_univ_three, threePeirceProjection, sandwichOp_apply,
    InfoGeometry.Core.PeirceGrading.even,
    InfoGeometry.Core.PeirceDecomposition.component11,
    InfoGeometry.Core.PeirceDecomposition.component00,
    InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
    mul_sub, sub_mul]
  abel

theorem threePeirceProjection_mul {P : B} (hP : P * P = P) (i j : Fin 3) :
    threePeirceProjection P i * threePeirceProjection P j =
      if i = j then threePeirceProjection P i else 0 := by
  fin_cases i <;> fin_cases j <;> ext X <;>
    simp [threePeirceProjection, sandwichOp_apply,
      InfoGeometry.Core.PeirceGrading.even,
      InfoGeometry.Core.PeirceDecomposition.component11,
      InfoGeometry.Core.PeirceDecomposition.component00,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
      mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, P_mul_P' hP]

/-- Every additive endomorphism is recovered from its nine supported blocks. -/
theorem endomorphismBlock_sum (P : B) (K : Module.End ℤ B) :
    ∑ i, ∑ j, endomorphismBlock P i j K = K := by
  simp only [endomorphismBlock, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [threePeirceProjection_sum, one_mul, mul_one]

/-- Different ordered support pairs are separated without characteristic assumptions. -/
theorem endomorphismBlock_extract {P : B} (hP : P * P = P)
    (a b i j : Fin 3) (K : Module.End ℤ B) :
    endomorphismBlock P a b (endomorphismBlock P i j K) =
      if a = i ∧ j = b then endomorphismBlock P i j K else 0 := by
  unfold endomorphismBlock
  rw [show threePeirceProjection P a *
      (threePeirceProjection P i * K * threePeirceProjection P j) *
        threePeirceProjection P b =
      (threePeirceProjection P a * threePeirceProjection P i) * K *
        (threePeirceProjection P j * threePeirceProjection P b) by
          simp only [mul_assoc]]
  rw [threePeirceProjection_mul hP, threePeirceProjection_mul hP]
  split_ifs <;> simp_all

/-- Equality is detected by the actual supported blocks. -/
theorem endomorphismBlock_ext (P : B) {K L : Module.End ℤ B}
    (h : ∀ i j, endomorphismBlock P i j K = endomorphismBlock P i j L) : K = L := by
  rw [← endomorphismBlock_sum P K, ← endomorphismBlock_sum P L]
  simp only [h]

/-- Groups of blocks with output-input degrees -2, -1, 0, 1, 2. -/
def fiveSupportedComponent (P : B) (K : Module.End ℤ B) : Fin 5 → Module.End ℤ B :=
  ![endomorphismBlock P 0 2 K,
    endomorphismBlock P 0 1 K + endomorphismBlock P 1 2 K,
    endomorphismBlock P 0 0 K + endomorphismBlock P 1 1 K + endomorphismBlock P 2 2 K,
    endomorphismBlock P 1 0 K + endomorphismBlock P 2 1 K,
    endomorphismBlock P 2 0 K]

theorem fiveSupportedComponent_sum (P : B) (K : Module.End ℤ B) :
    ∑ d, fiveSupportedComponent P K d = K := by
  have h := endomorphismBlock_sum P K
  simp only [Fin.sum_univ_three] at h
  simp [Fin.sum_univ_succ, fiveSupportedComponent]
  abel_nf at h ⊢
  exact h

end InfoGeometry.OperatorAlgebra.PeirceSpine
