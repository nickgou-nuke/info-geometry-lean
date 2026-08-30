import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint

noncomputable section

namespace SouriauOnsagerBKM

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

variable {n : ℕ}

theorem algebraMap_nonneg_cstar
    [NeZero n] (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ algebraMap ℝ (FiniteOperatorAlgebra n) t := by
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg
    (R := ℝ) (algebraMap ℝ (FiniteOperatorAlgebra n) t)
    (ha := by
      simpa using
        (algebraMap_star_comm t
          (A := FiniteOperatorAlgebra n)).symm)]
  intro x hx
  have hx' := (CFC.spectrum_algebraMap_eq t :
    spectrum ℝ (algebraMap ℝ (FiniteOperatorAlgebra n) t) = {t})
  rw [hx'] at hx
  simpa using hx ▸ ht

theorem strictlyPositive_add_nonneg_scalar
    [NeZero n] (X : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (ht : 0 ≤ t) :
    IsStrictlyPositive
      (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) := by
  exact hX.add_nonneg (algebraMap_nonneg_cstar t ht)

/-- The CFC resolvent of a self-adjoint operator at a nonnegative parameter.
This uses the CFC negative first power, since the operator carrier is not a
division ring and therefore has no ambient `Inv.inv` operation. -/
def cfcResolvent (X : FiniteOperatorAlgebra n) (t : ℝ) :
    FiniteOperatorAlgebra n :=
  CFC.rpow (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) (-1 : ℝ)

theorem continuousOn_cfcResolvent
    [NeZero n] (t : ℝ) (ht : 0 ≤ t) :
    ContinuousOn (fun X : FiniteOperatorAlgebra n => cfcResolvent X t)
      {X | IsStrictlyPositive X} := by
  have hadd : ContinuousOn
      (fun X : FiniteOperatorAlgebra n =>
        X + algebraMap ℝ (FiniteOperatorAlgebra n) t) {X | IsStrictlyPositive X} :=
    continuousOn_id.add continuousOn_const
  simpa [cfcResolvent, Function.comp_def] using
    (CFC.continuousOn_rpow (-1 : ℝ)).comp' hadd (by
      intro X hX
      exact strictlyPositive_add_nonneg_scalar X t hX ht)

theorem cfcResolvent_isUnit
    [NeZero n]
    (X : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (ht : 0 ≤ t) :
    IsUnit (cfcResolvent X t) := by
  have hY := strictlyPositive_add_nonneg_scalar X t hX ht
  exact hY.isUnit.cfcRpow (-1 : ℝ) hY.nonneg

theorem cfcResolvent_mul_shifted
    [NeZero n]
    (X : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (ht : 0 ≤ t) :
    cfcResolvent X t *
      (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) = 1 := by
  unfold cfcResolvent
  have hY := strictlyPositive_add_nonneg_scalar X t hX ht
  simpa only [CFC.rpow_one _ hY.nonneg] using
    (CFC.rpow_neg_mul_rpow 1 hY.isUnit hY.nonneg :
      CFC.rpow (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) (-1 : ℝ) *
        CFC.rpow (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) (1 : ℝ) = 1)

theorem shifted_mul_cfcResolvent
    [NeZero n]
    (X : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (ht : 0 ≤ t) :
    (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) * cfcResolvent X t = 1 := by
  unfold cfcResolvent
  have hY := strictlyPositive_add_nonneg_scalar X t hX ht
  simpa only [CFC.rpow_one _ hY.nonneg] using
    (CFC.rpow_mul_rpow_neg 1 hY.isUnit hY.nonneg :
      CFC.rpow (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) (1 : ℝ) *
        CFC.rpow (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) (-1 : ℝ) = 1)

end SouriauOnsagerBKM
