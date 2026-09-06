import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity

noncomputable section

namespace SouriauOnsagerBKM

open Matrix
open scoped MatrixOrder
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

/-- A faithful density real power is left-cancelled by the opposite power. -/
theorem FaithfulDensityOperator.rpow_neg_mul_rpow_eq_one
    (D : FaithfulDensityOperator n) (s : ℝ) :
    D.rpow (-s) * D.rpow s = 1 := by
  simpa [FaithfulDensityOperator.rpow] using
    (CFC.rpow_neg_mul_rpow s D.strictlyPositive)

/-- A faithful density real power is right-cancelled by the opposite power. -/
theorem FaithfulDensityOperator.rpow_mul_rpow_neg_eq_one
    (D : FaithfulDensityOperator n) (s : ℝ) :
    D.rpow s * D.rpow (-s) = 1 := by
  simpa [FaithfulDensityOperator.rpow] using
    (CFC.rpow_mul_rpow_neg s D.strictlyPositive)

/-- The Hilbert--Schmidt factor used in the diagonal BKM integrand is nonzero
whenever the observable is nonzero. -/
theorem FaithfulDensityOperator.kuboMoriFactor_ne_zero
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ)
    (hA : A ≠ 0) :
    D.rpow ((1 - s) / 2) * A * D.rpow (s / 2) ≠ 0 := by
  intro hX
  apply hA
  have h := congrArg
    (fun T : FiniteOperatorAlgebra n =>
      D.rpow (-((1 - s) / 2)) * T * D.rpow (-(s / 2))) hX
  simpa [mul_assoc, D.rpow_neg_mul_rpow_eq_one,
    D.rpow_mul_rpow_neg_eq_one] using h

/-- The finite trace of `X†X` is strictly positive in real part for `X ≠ 0`. -/
theorem finiteOperatorTrace_star_mul_self_re_pos
    (X : FiniteOperatorAlgebra n) (hX : X ≠ 0) :
    0 < (finiteOperatorTrace (star X * X)).re := by
  unfold finiteOperatorTrace
  rw [matrixOfOp_comp, matrixOfOp_adjoint]
  let M := matrixOfOp X
  have hpos : (Mᴴ * M).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self M
  have hnonneg := RCLike.nonneg_iff.mp hpos.trace_nonneg
  have htrace_ne : Matrix.trace (Mᴴ * M) ≠ 0 := by
    intro htrace
    have hmul : Mᴴ * M = 0 := hpos.trace_eq_zero_iff.mp htrace
    have hM : M = 0 := by
      exact (CStarRing.star_mul_self_eq_zero_iff M).mp (by
        simpa [star_eq_conjTranspose] using hmul)
    apply hX
    apply matrixOfOp_injective
    simpa [M] using hM
  have hre_ne : (Matrix.trace (Mᴴ * M)).re ≠ 0 := by
    intro hre
    apply htrace_ne
    apply Complex.ext
    · simpa using hre
    · simpa using hnonneg.2
  exact lt_of_le_of_ne hnonneg.1 (Ne.symm hre_ne)

/-- For a nonzero observable, the diagonal BKM integrand is pointwise strictly
positive in real part. -/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_pos
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ)
    (hA : A ≠ 0) :
    0 < (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_pos _
    (D.kuboMoriFactor_ne_zero A s hA)

/-- The genuine finite-dimensional BKM pairing is strictly positive on every
nonzero observable. -/
theorem FaithfulDensityOperator.kuboMoriPairing_self_pos
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow)
    (hA : A ≠ 0) :
    0 < (D.kuboMoriPairing A A).re := by
  have hIntegrable :
      IntervalIntegrable (D.kuboMoriIntegrand A A)
        MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h).intervalIntegrable 0 1
  have hre :
      (D.kuboMoriPairing A A).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A A s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    simpa using
      (ContinuousLinearMap.intervalIntegral_comp_comm
        (RCLike.reCLM : ℂ →L[ℝ] ℝ) hIntegrable)
  rw [hre]
  let f : ℝ → ℝ := fun s => (D.kuboMoriIntegrand A A s).re
  have hf_cont : Continuous f := by
    exact Complex.continuous_re.comp
      (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h)
  have hf_int : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    hf_cont.intervalIntegrable 0 1
  have hf_nonneg : 0 ≤ᵐ[MeasureTheory.volume] f :=
    Filter.Eventually.of_forall fun s =>
      (D.kuboMoriIntegrand_self_re_pos A s hA).le
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int]
  constructor
  · norm_num
  · have hsupp : Set.Ioc (0 : ℝ) 1 ⊆ Function.support f := by
      intro s hs
      exact Function.mem_support.mpr
        (ne_of_gt (D.kuboMoriIntegrand_self_re_pos A s hA))
    have hinter : Function.support f ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 1 :=
      Set.inter_eq_right.mpr hsupp
    rw [hinter]
    simp

/-- Vanishing of the BKM quadratic form is equivalent to vanishing of the
observable. -/
theorem FaithfulDensityOperator.kuboMoriPairing_self_eq_zero_iff
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow) :
    (D.kuboMoriPairing A A).re = 0 ↔ A = 0 := by
  constructor
  · intro hzero
    by_contra hA
    exact ne_of_gt (D.kuboMoriPairing_self_pos A h hA) hzero
  · rintro rfl
    rw [D.kuboMoriPairing_eq_trace_kuboMoriTransform 0 0 h]
    simp [FaithfulDensityOperator.kuboMoriTransform]

end SouriauOnsagerBKM
