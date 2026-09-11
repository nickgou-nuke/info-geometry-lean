import Mathlib.Analysis.Matrix.Order
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.BilinearForm.Properties
import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm

noncomputable section

namespace SouriauOnsagerBKM

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

/-- Multiplication on the left and right by units preserves nonzero elements.
This is the algebraic cancellation lemma used by the strict BKM factorization.
-/
theorem scaling_nonzero_of_units
    {A_op : Type*} [MonoidWithZero A_op]
    (D_left D_right A : A_op)
    (hu_left : IsUnit D_left) (hu_right : IsUnit D_right)
    (hA : A ≠ 0) :
    D_left * A * D_right ≠ 0 := by
  intro hzero
  have hleft : D_left * A = 0 := by
    apply hu_right.mul_right_cancel
    simpa [mul_assoc] using hzero
  have hAzero : A = 0 := by
    apply hu_left.mul_left_cancel
    simpa using hleft
  exact hA hAzero

theorem finiteOperatorTrace_star_mul_self_re_nonneg
    (X : FiniteOperatorAlgebra n) :
    0 ≤ (finiteOperatorTrace (star X * X)).re := by
  unfold finiteOperatorTrace
  change 0 ≤ (Matrix.trace
    (matrixOfOp ((ContinuousLinearMap.adjoint X).comp X))).re
  rw [matrixOfOp_comp, matrixOfOp_adjoint]
  have hpsd :
      ((matrixOfOp X)ᴴ * matrixOfOp X).PosSemidef :=
    posSemidef_conjTranspose_mul_self (matrixOfOp X)
  exact (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1

theorem finiteOperatorTrace_star_mul_self_re_pos
    (X : FiniteOperatorAlgebra n) (hX : X ≠ 0) :
    0 < (finiteOperatorTrace (star X * X)).re := by
  have hM : matrixOfOp X ≠ 0 := by
    intro h
    apply hX
    exact matrixOfOp_injective h
  have htrace : Matrix.trace ((matrixOfOp X)ᴴ * matrixOfOp X) ≠ 0 := by
    intro hz
    apply hM
    exact (trace_conjTranspose_mul_self_eq_zero_iff).mp hz
  have hpsd :
      ((matrixOfOp X)ᴴ * matrixOfOp X).PosSemidef :=
    posSemidef_conjTranspose_mul_self (matrixOfOp X)
  have hre : 0 ≤ (Matrix.trace
      ((matrixOfOp X)ᴴ * matrixOfOp X)).re :=
    (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1
  have hre_ne : (Matrix.trace
      ((matrixOfOp X)ᴴ * matrixOfOp X)).re ≠ 0 := by
    intro hr
    apply htrace
    apply Complex.ext
    · exact hr
    · exact (RCLike.nonneg_iff.mp hpsd.trace_nonneg).2
  rw [show finiteOperatorTrace (star X * X) =
      Matrix.trace ((matrixOfOp X)ᴴ * matrixOfOp X) by
        unfold finiteOperatorTrace
        change Matrix.trace
          (matrixOfOp ((ContinuousLinearMap.adjoint X).comp X)) = _
        rw [matrixOfOp_comp, matrixOfOp_adjoint]]
  exact lt_of_le_of_ne hre (Ne.symm hre_ne)

theorem finiteOperatorTrace_star_mul_self_re_eq_zero_iff
    (X : FiniteOperatorAlgebra n) :
    (finiteOperatorTrace (star X * X)).re = 0 ↔ X = 0 := by
  constructor
  · intro h
    by_contra hX
    have hp := finiteOperatorTrace_star_mul_self_re_pos X hX
    linarith
  · rintro rfl
    simp [finiteOperatorTrace]

theorem FaithfulDensityOperator.rpow_half_mul_self
    (D : FaithfulDensityOperator n) (s : ℝ) :
    D.rpow (s / 2) * D.rpow (s / 2) = D.rpow s := by
  rw [← D.rpow_add]
  congr 1
  ring

theorem FaithfulDensityOperator.rpow_one_sub_half_mul_self
    (D : FaithfulDensityOperator n) (s : ℝ) :
    D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2) = D.rpow (1 - s) := by
  rw [← D.rpow_add]
  congr 1
  ring

theorem FaithfulDensityOperator.kuboMoriIntegrand_self_eq_trace_star_mul_self
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ) :
    D.kuboMoriIntegrand A A s =
      finiteOperatorTrace
        (star (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2)) *
          (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
  have hleft := D.rpow_one_sub_half_mul_self s
  have hright := D.rpow_half_mul_self s
  calc
    D.kuboMoriIntegrand A A s =
        finiteOperatorTrace (D.rpow s * star A * D.rpow (1 - s) * A) := rfl
    _ = finiteOperatorTrace
        ((D.rpow (s / 2) * D.rpow (s / 2)) * star A *
          D.rpow (1 - s) * A) := by rw [hright]
    _ = finiteOperatorTrace
        (D.rpow (s / 2) *
          (D.rpow (s / 2) * star A * D.rpow (1 - s) * A)) := by
      congr 1
    _ = finiteOperatorTrace
        ((D.rpow (s / 2) * star A * D.rpow (1 - s) * A) *
          D.rpow (s / 2)) := finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace
        ((D.rpow (s / 2) * star A *
          (D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2)) * A) *
          D.rpow (s / 2)) := by rw [hleft]
    _ = finiteOperatorTrace
        ((D.rpow (s / 2) * star A * D.rpow ((1 - s) / 2)) *
          (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
      congr 1
    _ = finiteOperatorTrace
        (star (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2)) *
          (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
      congr 1
      simp [mul_assoc]

theorem FaithfulDensityOperator.rpow_sandwich_ne_zero
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (a b : ℝ) (hA : A ≠ 0) :
    D.rpow a * A * D.rpow b ≠ 0 := by
  intro hzero
  have hleft : D.rpow (-a) * D.rpow a = 1 := by
    rw [← D.rpow_add]
    have ha : -a + a = 0 := by ring
    rw [ha, D.rpow_zero]
  have hright : D.rpow b * D.rpow (-b) = 1 := by
    rw [← D.rpow_add]
    have hb : b + -b = 0 := by ring
    rw [hb, D.rpow_zero]
  apply hA
  calc
    A = 1 * A * 1 := by simp
    _ = (D.rpow (-a) * D.rpow a) * A *
        (D.rpow b * D.rpow (-b)) := by rw [hleft, hright]
    _ = D.rpow (-a) * (D.rpow a * A * D.rpow b) * D.rpow (-b) := by
      noncomm_ring
    _ = 0 := by rw [hzero]; simp

theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_pos
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ) (hA : A ≠ 0) :
    0 < (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_pos _
    (D.rpow_sandwich_ne_zero A ((1 - s) / 2) (s / 2) hA)

theorem FaithfulDensityOperator.kuboMoriPairing_self_re_pos
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) (hA : A ≠ 0) :
    0 < (D.kuboMoriPairing A A).re := by
  have hc : Continuous (fun s : ℝ =>
      (D.kuboMoriIntegrand A A s).re) :=
    RCLike.continuous_re.comp
      (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h_rpow)
  have hpos := intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
    hc.continuousOn
    (fun s _ => le_of_lt (D.kuboMoriIntegrand_self_re_pos A s hA))
    ⟨0, by simp, D.kuboMoriIntegrand_self_re_pos A 0 hA⟩
  have hre :
      (D.kuboMoriPairing A A).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A A s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    exact ContinuousLinearMap.intervalIntegral_comp_comm
      (RCLike.reCLM : ℂ →L[ℝ] ℝ)
      ((D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h_rpow).intervalIntegrable 0 1)
  rw [hre]
  exact hpos

theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ) :
    0 ≤ (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_nonneg _

theorem FaithfulDensityOperator.kuboMoriPairing_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    0 ≤ (D.kuboMoriPairing A A).re := by
  have h_integrable :
      IntervalIntegrable (D.kuboMoriIntegrand A A)
        MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h_rpow).intervalIntegrable 0 1
  have hre :
      (D.kuboMoriPairing A A).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A A s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    exact ContinuousLinearMap.intervalIntegral_comp_comm
      (RCLike.reCLM : ℂ →L[ℝ] ℝ) h_integrable
  rw [hre]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num) fun s =>
    D.kuboMoriIntegrand_self_re_nonneg A s

theorem FaithfulDensityOperator.bkmRealBilinForm_isPosSemidef
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    (D.bkmRealBilinForm h_rpow).IsPosSemidef where
  isSymm := D.bkmRealBilinForm_symm h_rpow
  isNonneg := ⟨fun A => by
    simpa only [D.bkmRealBilinForm_apply h_rpow A A] using
      D.kuboMoriPairing_self_re_nonneg A h_rpow⟩

end SouriauOnsagerBKM
