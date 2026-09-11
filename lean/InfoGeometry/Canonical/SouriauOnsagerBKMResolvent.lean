import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

theorem complex_algebraMap_realCast
    (t : ℝ) :
    algebraMap ℂ (FiniteOperatorAlgebra n) (t : ℂ) =
      algebraMap ℝ (FiniteOperatorAlgebra n) t := by
  change algebraMap ℂ (FiniteOperatorAlgebra n)
      (algebraMap ℝ ℂ t) = _
  rw [IsScalarTower.algebraMap_apply ℝ ℂ (FiniteOperatorAlgebra n) t]

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

theorem cfcResolvent_isSelfAdjoint
    [NeZero n]
    (X : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (ht : 0 ≤ t) :
    IsSelfAdjoint (cfcResolvent X t) := by
  have hY := strictlyPositive_add_nonneg_scalar X t hX ht
  rw [cfcResolvent]
  change IsSelfAdjoint
    ((X + algebraMap ℝ (FiniteOperatorAlgebra n) t) ^ (-1 : ℝ))
  rw [CFC.rpow_eq_cfc_real hY.nonneg]
  exact IsSelfAdjoint.cfc

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

/-! ### The noncommutative resolvent difference identity -/

theorem cfcResolvent_diff_mul_shift_diff_mul_cfcResolvent
    [NeZero n]
    (X Y : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (ht : 0 ≤ t) :
    cfcResolvent X t *
        ((Y + algebraMap ℝ (FiniteOperatorAlgebra n) t) -
          (X + algebraMap ℝ (FiniteOperatorAlgebra n) t)) *
        cfcResolvent Y t =
      cfcResolvent X t - cfcResolvent Y t := by
  calc
    cfcResolvent X t *
          ((Y + algebraMap ℝ (FiniteOperatorAlgebra n) t) -
            (X + algebraMap ℝ (FiniteOperatorAlgebra n) t)) *
          cfcResolvent Y t =
        cfcResolvent X t *
            (Y + algebraMap ℝ (FiniteOperatorAlgebra n) t) *
            cfcResolvent Y t -
          cfcResolvent X t *
            (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) *
            cfcResolvent Y t := by
      rw [mul_sub, sub_mul]
    _ = cfcResolvent X t - cfcResolvent Y t := by
      simp only [mul_assoc, shifted_mul_cfcResolvent Y t hY ht,
        cfcResolvent_mul_shifted X t hX ht, mul_one, one_mul]

theorem cfcResolvent_diff_mul_sub_mul_cfcResolvent
    [NeZero n]
    (X Y : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (ht : 0 ≤ t) :
    cfcResolvent X t * (Y - X) * cfcResolvent Y t =
      cfcResolvent X t - cfcResolvent Y t := by
  have hshift :
      (Y + algebraMap ℝ (FiniteOperatorAlgebra n) t) -
          (X + algebraMap ℝ (FiniteOperatorAlgebra n) t) = Y - X := by
    abel
  rw [← hshift]
  exact cfcResolvent_diff_mul_shift_diff_mul_cfcResolvent X Y t hX hY ht

theorem cfcResolvent_diff_sub_left_linearization
    [NeZero n]
    (X Y : FiniteOperatorAlgebra n) (t : ℝ)
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (ht : 0 ≤ t) :
    (cfcResolvent X t - cfcResolvent Y t) -
        cfcResolvent X t * (Y - X) * cfcResolvent X t =
      cfcResolvent X t * (Y - X) *
        (cfcResolvent Y t - cfcResolvent X t) := by
  calc
    (cfcResolvent X t - cfcResolvent Y t) -
        cfcResolvent X t * (Y - X) * cfcResolvent X t =
      cfcResolvent X t * (Y - X) * cfcResolvent Y t -
        cfcResolvent X t * (Y - X) * cfcResolvent X t := by
          rw [cfcResolvent_diff_mul_sub_mul_cfcResolvent X Y t hX hY ht]
    _ = cfcResolvent X t * (Y - X) *
        (cfcResolvent Y t - cfcResolvent X t) := by
          simp only [sub_mul, mul_sub]

end SouriauOnsagerBKM
