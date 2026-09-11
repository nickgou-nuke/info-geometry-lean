import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity

/-!
# Strict positivity of the finite noncommutative BKM pairing

The pointwise trace factorization and its strictness are owned by
`SouriauOnsagerBKMPositivity`.  This file performs only the analytic lift
from pointwise strict positivity to the interval-integrated pairing.
-/

noncomputable section

namespace SouriauOnsagerBKM

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

theorem FaithfulDensityOperator.kuboMoriPairing_self_pos
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow)
    (hA : A ≠ 0) :
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

theorem FaithfulDensityOperator.kuboMoriPairing_self_re_eq_zero_iff
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    (D.kuboMoriPairing A A).re = 0 ↔ A = 0 := by
  constructor
  · intro h
    by_contra hA
    have hpos := D.kuboMoriPairing_self_pos A h_rpow hA
    linarith
  · rintro rfl
    unfold FaithfulDensityOperator.kuboMoriPairing
    have hzero :
        (fun s : ℝ => FaithfulDensityOperator.kuboMoriIntegrand D 0 0 s) =
          0 := by
      funext s
      simp [FaithfulDensityOperator.kuboMoriIntegrand, finiteOperatorTrace]
    rw [hzero]
    exact congrArg Complex.re (intervalIntegral.integral_zero)

theorem FaithfulDensityOperator.kuboMoriPairing_self_eq_zero_iff
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    (D.kuboMoriPairing A A).re = 0 ↔ A = 0 :=
  D.kuboMoriPairing_self_re_eq_zero_iff A h_rpow

end SouriauOnsagerBKM
