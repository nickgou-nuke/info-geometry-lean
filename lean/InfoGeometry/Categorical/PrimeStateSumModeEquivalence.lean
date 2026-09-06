import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeOccupationAlgebra
import InfoGeometry.Categorical.PrimeThermodynamicDirectLimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit
import InfoGeometry.Categorical.PrimeThermodynamicReadoutCones

noncomputable section

namespace InfoGeometry.Categorical.PrimeStateSumModeEquivalence

open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Categorical.PrimeThermodynamicDirectLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit
open InfoGeometry.Categorical.PrimeThermodynamicReadoutCones

@[rep_depth thermo]
abbrev StateSumStage (n : ℕ) := PrimeStage n

def stateBondAlg (n : ℕ) : StateSumStage n →ₐ[ℂ] StateSumStage (n + 1) :=
  primeBondAlg n

def stateBond (n : ℕ) : StateSumStage n →+* StateSumStage (n + 1) :=
  primeBond n

def bondMapAlg {n m : ℕ} (h : n ≤ m) : StateSumStage n →ₐ[ℂ] StateSumStage m :=
  InfoGeometry.Arithmetic.PrimeOccupationAlgebra.bondMapAlg h

def stateSumPrimeModeEquiv (n : ℕ) : StateSumStage n ≃ₐ[ℂ] PrimeStage n :=
  AlgEquiv.refl

theorem stateSumPrimeModeEquiv_natural {n m : ℕ} (h : n ≤ m) :
    (stateSumPrimeModeEquiv m).toLinearMap.comp (bondMapAlg h).toLinearMap =
      (bondMapAlg h).toLinearMap.comp (stateSumPrimeModeEquiv n).toLinearMap := by
  rfl

abbrev StateSumAlgebra := DirectLimitSuperClosure stateBond
abbrev StateSumUniversalSpace := StateSumAlgebra

def stateSumToPrimeMode : StateSumUniversalSpace →+* PrimonAlgebra :=
  directLimitLift stateBond
    (fun n => directLimitOf primeBond n)
    (by
      intro n x
      change directLimitOf primeBond (n + 1) (primeBond n x) = directLimitOf primeBond n x
      exact directLimitOf_bond primeBond n x)

def primeModeToStateSum : PrimonAlgebra →+* StateSumUniversalSpace :=
  directLimitLift primeBond
    (fun n => directLimitOf stateBond n)
    (by
      intro n x
      change directLimitOf stateBond (n + 1) (stateBond n x) = directLimitOf stateBond n x
      exact directLimitOf_bond stateBond n x)

theorem stateSumToPrimeMode_comp_of (n : ℕ) (x : StateSumStage n) :
    stateSumToPrimeMode (directLimitOf stateBond n x) = directLimitOf primeBond n x := by
  exact directLimitLift_of stateBond (fun n => directLimitOf primeBond n) _ n x

theorem primeModeToStateSum_comp_of (n : ℕ) (x : PrimeStage n) :
    primeModeToStateSum (directLimitOf primeBond n x) = directLimitOf stateBond n x := by
  exact directLimitLift_of primeBond (fun n => directLimitOf stateBond n) _ n x

theorem stateSumPrimeMode_leftInverse :
    primeModeToStateSum.comp stateSumToPrimeMode = RingHom.id StateSumUniversalSpace := by
  apply DirectLimit.Ring.hom_ext
  intro n
  apply RingHom.ext
  intro (x : StateSumStage n)
  change primeModeToStateSum (stateSumToPrimeMode (directLimitOf stateBond n x)) = directLimitOf stateBond n x
  rw [stateSumToPrimeMode_comp_of n x, primeModeToStateSum_comp_of n x]

theorem stateSumPrimeMode_rightInverse :
    stateSumToPrimeMode.comp primeModeToStateSum = RingHom.id PrimonAlgebra := by
  apply DirectLimit.Ring.hom_ext
  intro n
  apply RingHom.ext
  intro (x : PrimeStage n)
  change stateSumToPrimeMode (primeModeToStateSum (directLimitOf primeBond n x)) = directLimitOf primeBond n x
  rw [primeModeToStateSum_comp_of n x, stateSumToPrimeMode_comp_of n x]

def stateSumPrimeModeColimitEquiv : StateSumUniversalSpace ≃+* PrimonAlgebra :=
  RingEquiv.ofRingHom
    stateSumToPrimeMode
    primeModeToStateSum
    stateSumPrimeMode_leftInverse
    stateSumPrimeMode_rightInverse

def stageStateSumActivityEval (z s : ℂ) (n : ℕ) : StateSumStage n →ₐ[ℂ] ℂ :=
  stageActivityEval z s n

def stateSumActivityCone (z s : ℂ) :
    CompatibleCone stateBond (fun n => (stageStateSumActivityEval z s n).toRingHom) := by
  intro n x
  change (stageStateSumActivityEval z s (n + 1)).toRingHom (stateBond n x) =
    (stageStateSumActivityEval z s n).toRingHom x
  exact stageActivityEval_comp_bond z s n x

def universalStateSumActivityEval (z s : ℂ) : StateSumUniversalSpace →+* ℂ :=
  directLimitLift stateBond (fun n => (stageStateSumActivityEval z s n).toRingHom)
    (stateSumActivityCone z s)

theorem universalActivityEval_stateSumPrimeMode (z s : ℂ) (x : StateSumUniversalSpace) :
    universalActivityEval z s (stateSumPrimeModeColimitEquiv x) =
      universalStateSumActivityEval z s x := by
  have h_hom : (universalActivityEval z s).comp stateSumToPrimeMode = universalStateSumActivityEval z s := by
    apply DirectLimit.Ring.hom_ext
    intro n
    apply RingHom.ext
    intro (y : StateSumStage n)
    change universalActivityEval z s (stateSumToPrimeMode (directLimitOf stateBond n y)) = universalStateSumActivityEval z s (directLimitOf stateBond n y)
    rw [stateSumToPrimeMode_comp_of n y]
    have h1 : universalActivityEval z s (directLimitOf primeBond n y) = stageActivityEval z s n y := universalActivityEval_stage z s n y
    rw [h1]
    have hl := directLimitLift_of stateBond
      (fun n => (stageStateSumActivityEval z s n).toRingHom)
      (stateSumActivityCone z s) n y
    exact hl.symm
  exact RingHom.congr_fun h_hom x

theorem universalActivityEval_natural (z s : ℂ) :
    (universalActivityEval z s).comp stateSumPrimeModeColimitEquiv.toRingHom =
      universalStateSumActivityEval z s := by
  apply RingHom.ext
  intro x
  exact universalActivityEval_stateSumPrimeMode z s x

def universalStateSumDerivedReadout (z s : ℂ) (D : ℂ → ℂ) : StateSumUniversalSpace → ℂ :=
  D ∘ universalStateSumActivityEval z s

theorem universalDerivedReadout_stateSumPrimeMode (z s : ℂ) (D : ℂ → ℂ) (x : StateSumUniversalSpace) :
    universalDerivedReadout z s D (stateSumPrimeModeColimitEquiv x) =
      universalStateSumDerivedReadout z s D x := by
  unfold universalDerivedReadout universalStateSumDerivedReadout
  rw [Function.comp_apply, Function.comp_apply]
  rw [universalActivityEval_stateSumPrimeMode z s x]

end InfoGeometry.Categorical.PrimeStateSumModeEquivalence
