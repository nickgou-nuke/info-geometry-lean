import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric

noncomputable section

namespace InfoGeometry.Canonical.FiniteGibbsQGTBridge

open scoped BigOperators InnerProductSpace
open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

variable {State : Type*} [Fintype State] [Nonempty State]

abbrev GibbsHilbert (State : Type*) := EuclideanSpace ℂ State

def diagonalObservable (f : State → ℝ) : GibbsHilbert State →L[ℂ] GibbsHilbert State :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp (2 : ENNReal) (fun x => (f x : ℂ) * v x)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro x
        simp [PiLp.toLp_apply, mul_add]
      map_smul' := by
        intro c v
        apply PiLp.ext
        intro x
        simp [PiLp.toLp_apply]
        ring }

def gibbsState (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    NormalizedState (GibbsHilbert State) where
  vec := WithLp.toLp (2 : ENNReal)
    (fun x => (Real.sqrt (realGibbsWeight D beta x) : ℂ))
  norm_sq := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
    simp only [← starRingEnd_apply]
    have hstar : ∀ x : State,
        starRingEnd ℂ (Real.sqrt (realGibbsWeight D beta x) : ℂ) =
          (Real.sqrt (realGibbsWeight D beta x) : ℂ) := by
      intro x
      change star (Real.sqrt (realGibbsWeight D beta x) : ℂ) = _
      exact RCLike.conj_ofReal _
    simp_rw [hstar]
    change (∑ x : State,
      (Real.sqrt (realGibbsWeight D beta x) : ℂ) *
        (Real.sqrt (realGibbsWeight D beta x) : ℂ)) = 1
    simp_rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum]
    congr 1
    calc
      (∑ x : State, Real.sqrt (realGibbsWeight D beta x) *
          Real.sqrt (realGibbsWeight D beta x)) =
          ∑ x : State, Real.sqrt (realGibbsWeight D beta x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [pow_two]
      _ = ∑ x : State, realGibbsWeight D beta x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Real.sq_sqrt (le_of_lt (realGibbsWeight_pos D beta x))]
      _ = 1 := realGibbsWeight_sum_eq_one D beta

theorem gibbsState_norm_sq (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    ⟪(gibbsState D beta).vec, (gibbsState D beta).vec⟫_ℂ = 1 :=
  (gibbsState D beta).norm_sq

end InfoGeometry.Canonical.FiniteGibbsQGTBridge
