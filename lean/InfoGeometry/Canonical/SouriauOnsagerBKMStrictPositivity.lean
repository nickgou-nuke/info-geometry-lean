import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

/-- Strict positivity of the integrated full noncommutative Kubo--Mori
self-pairing away from the zero operator.

The proof uses only the existing pointwise strict positivity theorem and
Mathlib's strict positivity theorem for interval integrals. -/
theorem FaithfulDensityOperator.kuboMoriPairing_self_pos
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow)
    (hA : A ≠ 0) :
    0 < (D.kuboMoriPairing A A).re := by
  have h_complex_integrable :
      IntervalIntegrable
        (D.kuboMoriIntegrand A A) MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h_rpow).intervalIntegrable 0 1
  have h_real_continuous :
      Continuous (fun s : ℝ => (D.kuboMoriIntegrand A A s).re) :=
    RCLike.continuous_re.comp
      (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h_rpow)
  have h_real_integrable :
      IntervalIntegrable
        (fun s : ℝ => (D.kuboMoriIntegrand A A s).re)
        MeasureTheory.volume 0 1 :=
    h_real_continuous.intervalIntegrable 0 1
  have hre :
      (D.kuboMoriPairing A A).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A A s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    exact
      ContinuousLinearMap.intervalIntegral_comp_comm
        (RCLike.reCLM : ℂ →L[ℝ] ℝ) h_complex_integrable
  rw [hre]
  exact intervalIntegral_pos_of_pos_on h_real_integrable
    (fun s _ => D.kuboMoriIntegrand_self_re_pos A s hA)
    (by norm_num)

/-- The real part of the integrated Kubo--Mori self-pairing vanishes exactly
at the zero operator. -/
theorem FaithfulDensityOperator.kuboMoriPairing_self_re_eq_zero_iff
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    (D.kuboMoriPairing A A).re = 0 ↔ A = 0 := by
  constructor
  · intro hzero
    by_contra hA
    have hpos := D.kuboMoriPairing_self_pos A h_rpow hA
    linarith
  · rintro rfl
    unfold FaithfulDensityOperator.kuboMoriPairing
    simp [FaithfulDensityOperator.kuboMoriIntegrand]

/-- Canonical strict-definiteness surface theorem for the integrated BKM
pairing.  The scalar being tested is its real quadratic form. -/
theorem FaithfulDensityOperator.kuboMoriPairing_self_eq_zero_iff
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    (D.kuboMoriPairing A A).re = 0 ↔ A = 0 :=
  D.kuboMoriPairing_self_re_eq_zero_iff A h_rpow

end SouriauOnsagerBKM
