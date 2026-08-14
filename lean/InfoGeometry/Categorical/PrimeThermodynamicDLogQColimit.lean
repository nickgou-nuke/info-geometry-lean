import Mathlib.Tactic
import InfoGeometry.Categorical.PrimeThermodynamicReadoutCones

noncomputable section

namespace InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit

open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Categorical.PrimeThermodynamicLimitCapstone
open InfoGeometry.Categorical.PrimeThermodynamicReadoutCones
open InfoGeometry.Categorical.PrimeThermodynamicDirectLimit

def stageDerivedReadout (z s : ℂ) (D : ℂ → ℂ) (n : ℕ) : PrimeStage n → ℂ :=
  D ∘ stageActivityEval z s n

def universalDerivedReadout (z s : ℂ) (D : ℂ → ℂ) : BostConnesUniversalSpace → ℂ :=
  D ∘ universalActivityEval z s

theorem stageDerivedReadout_comp_bond (z s : ℂ) (D : ℂ → ℂ) (n : ℕ) (x : PrimeStage n) :
    stageDerivedReadout z s D (n + 1) (primeBondAlg n x) = stageDerivedReadout z s D n x := by
  unfold stageDerivedReadout
  rw [Function.comp_apply, Function.comp_apply]
  rw [stageActivityEval_comp_bond]

theorem universalDerivedReadout_comp_of (z s : ℂ) (D : ℂ → ℂ) (n : ℕ) (x : PrimeStage n) :
    universalDerivedReadout z s D (stageLimitOf n x) = stageDerivedReadout z s D n x := by
  unfold universalDerivedReadout stageDerivedReadout
  rw [Function.comp_apply, Function.comp_apply]
  rw [universalActivityEval_stage]

end InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit
