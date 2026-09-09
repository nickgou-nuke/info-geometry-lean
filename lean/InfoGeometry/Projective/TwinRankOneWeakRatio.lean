import InfoGeometry.Analysis.RankOneTrace
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-!
# Twin-state rank-one traces with independent homogeneous rescaling

Dyads and finite-dimensional trace are Mathlib objects in the coefficient
algebra. Both vector slots of the nonassociative Zorn carrier stay arbitrary.
The ratio is undefined at zero overlap and need not be a positive state.
-/

noncomputable section
namespace InfoGeometry.Projective.TwinRankOneWeakRatio

open InfoGeometry.Canonical
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev dyad (u : H) : H →L[ℂ] H := InnerProductSpace.rankOne ℂ u u

def weakRatio (Q : H →L[ℂ] H) (psi phi : H) : Option ℂ :=
  if ⟪phi, psi⟫_ℂ = 0 then none else some (⟪phi, Q psi⟫_ℂ / ⟪phi, psi⟫_ℂ)

theorem rankOne_sandwich (u v x y : H) (Q : H →L[ℂ] H) :
    (InnerProductSpace.rankOne ℂ u v).comp
        (Q.comp (InnerProductSpace.rankOne ℂ x y)) =
      ⟪v, Q x⟫_ℂ • InnerProductSpace.rankOne ℂ u y := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    map_smul, inner_smul_right, ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  ring

theorem dyad_square (u : H) : (dyad u).comp (dyad u) = ⟪u,u⟫_ℂ • dyad u := by
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.id_apply] using
    rankOne_sandwich u u u u (ContinuousLinearMap.id ℂ H)

@[simp] theorem weakRatio_none_iff (Q : H →L[ℂ] H) (psi phi : H) :
    weakRatio Q psi phi = none ↔ ⟪phi,psi⟫_ℂ = 0 := by
  unfold weakRatio
  split_ifs <;> simp_all

theorem weakRatio_independent_rescaling (Q : H →L[ℂ] H) (psi phi : H)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    weakRatio Q (a • psi) (b • phi) = weakRatio Q psi phi := by
  have hb' : starRingEnd ℂ b ≠ 0 := by simpa using hb
  have hc : starRingEnd ℂ b * a ≠ 0 := mul_ne_zero hb' ha
  have hden : ⟪b • phi,a • psi⟫_ℂ =
      (starRingEnd ℂ b * a) * ⟪phi,psi⟫_ℂ := by
    simp only [inner_smul_left, inner_smul_right]
    ring
  have hnum : ⟪b • phi,Q (a • psi)⟫_ℂ =
      (starRingEnd ℂ b * a) * ⟪phi,Q psi⟫_ℂ := by
    rw [map_smul]
    simp only [inner_smul_left, inner_smul_right]
    ring
  unfold weakRatio
  rw [hden, hnum]
  by_cases h : ⟪phi,psi⟫_ℂ = 0
  · simp [h]
  · simp only [mul_eq_zero, hc, false_or, h, if_false]
    congr 1
    exact mul_div_mul_left _ _ hc

def twinPotential (psi phi : H) (U V : OperatorVector (H →L[ℂ] H)) :
    OperatorZornMatrix (H →L[ℂ] H) :=
  operatorZornCoordinates (dyad psi) (dyad phi) U V

@[simp] theorem twinPotential_diagonal_plus (psi phi : H)
    (U V : OperatorVector (H →L[ℂ] H)) : (twinPotential psi phi U V).n_plus = dyad psi := rfl

@[simp] theorem twinPotential_diagonal_minus (psi phi : H)
    (U V : OperatorVector (H →L[ℂ] H)) : (twinPotential psi phi U V).n_minus = dyad phi := rfl

section Trace
variable [FiniteDimensional ℂ H]

def operatorTrace (T : H →L[ℂ] H) : ℂ := LinearMap.trace ℂ H T.toLinearMap

@[simp] theorem operatorTrace_rankOne (x y : H) :
    operatorTrace (InnerProductSpace.rankOne ℂ x y) = ⟪y,x⟫_ℂ :=
  InnerProductSpace.trace_rankOne x y

@[simp] theorem operatorTrace_smul (c : ℂ) (T : H →L[ℂ] H) :
    operatorTrace (c • T) = c * operatorTrace T := by
  change LinearMap.trace ℂ H (c • T.toLinearMap) = _
  rw [map_smul]
  rfl

theorem twin_trace_numerator (Q : H →L[ℂ] H) (psi phi : H) :
    operatorTrace ((dyad phi).comp (Q.comp (dyad psi))) =
      ⟪phi,Q psi⟫_ℂ * ⟪psi,phi⟫_ℂ := by
  rw [rankOne_sandwich, operatorTrace_smul, operatorTrace_rankOne]

theorem twin_trace_denominator (psi phi : H) :
    operatorTrace ((dyad phi).comp (dyad psi)) =
      ⟪phi,psi⟫_ℂ * ⟪psi,phi⟫_ℂ := by
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.id_apply] using
    twin_trace_numerator (ContinuousLinearMap.id ℂ H) psi phi

theorem twin_trace_denominator_zero_iff (psi phi : H) :
    operatorTrace ((dyad phi).comp (dyad psi)) = 0 ↔ ⟪phi,psi⟫_ℂ = 0 := by
  rw [twin_trace_denominator, mul_eq_zero]
  have hs : ⟪psi,phi⟫_ℂ = 0 ↔ ⟪phi,psi⟫_ℂ = 0 := inner_eq_zero_symm
  rw [hs, or_self]

def traceWeakRatio (Q : H →L[ℂ] H) (psi phi : H) : Option ℂ :=
  if operatorTrace ((dyad phi).comp (dyad psi)) = 0 then none
  else some (operatorTrace ((dyad phi).comp (Q.comp (dyad psi))) /
    operatorTrace ((dyad phi).comp (dyad psi)))

theorem traceWeakRatio_eq_weakRatio (Q : H →L[ℂ] H) (psi phi : H) :
    traceWeakRatio Q psi phi = weakRatio Q psi phi := by
  by_cases h : ⟪phi,psi⟫_ℂ = 0
  · have hz : operatorTrace ((dyad phi).comp (dyad psi)) = 0 :=
      (twin_trace_denominator_zero_iff psi phi).mpr h
    simp [traceWeakRatio, weakRatio, hz, h]
  · have hz : operatorTrace ((dyad phi).comp (dyad psi)) ≠ 0 := by
      intro hz
      exact h ((twin_trace_denominator_zero_iff psi phi).mp hz)
    simp only [traceWeakRatio, weakRatio, hz, h, if_false]
    rw [twin_trace_numerator, twin_trace_denominator]
    have hr : ⟪psi,phi⟫_ℂ ≠ 0 := by
      intro hz
      exact h (inner_eq_zero_symm.mp hz)
    congr 1
    exact mul_div_mul_right _ _ hr

theorem traceWeakRatio_independent_rescaling (Q : H →L[ℂ] H) (psi phi : H)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    traceWeakRatio Q (a • psi) (b • phi) = traceWeakRatio Q psi phi := by
  simp only [traceWeakRatio_eq_weakRatio]
  exact weakRatio_independent_rescaling Q psi phi a b ha hb

theorem twinPotential_trace_ratio (Q : H →L[ℂ] H) (psi phi : H)
    (U V : OperatorVector (H →L[ℂ] H)) :
    (if operatorTrace ((twinPotential psi phi U V).n_minus.comp
        (twinPotential psi phi U V).n_plus) = 0 then none
     else some (operatorTrace ((twinPotential psi phi U V).n_minus.comp
        (Q.comp (twinPotential psi phi U V).n_plus)) /
       operatorTrace ((twinPotential psi phi U V).n_minus.comp
        (twinPotential psi phi U V).n_plus))) = weakRatio Q psi phi :=
  traceWeakRatio_eq_weakRatio Q psi phi

end Trace
end InfoGeometry.Projective.TwinRankOneWeakRatio
