import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.PrimeThermodynamicDirectLimit
import InfoGeometry.Categorical.PrimeThermodynamicStateEquivalence
import InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit
import InfoGeometry.Categorical.PrimeStateSumModeEquivalence
import InfoGeometry.Categorical.PrimeThermodynamicReadoutCones
import InfoGeometry.Categorical.PrimeThermodynamicLimitCapstone

noncomputable section
namespace InfoGeometry.Categorical.PrimonParafermionGrandCanonicalColimitCapstone

open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Categorical.PrimeThermodynamicDirectLimit
open InfoGeometry.Categorical.PrimeThermodynamicStateEquivalence
open InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit
open InfoGeometry.Categorical.PrimeStateSumModeEquivalence
open InfoGeometry.Categorical.PrimeThermodynamicReadoutCones
open InfoGeometry.Categorical.PrimeThermodynamicLimitCapstone

theorem primonThermodynamicColimitCapstone (z s : ℂ) (D : ℂ → ℂ) :
    ∃ (StateSum PrimeMode : Type) (_instS : CommRing StateSum)
      (_instP : CommRing PrimeMode) (Equiv : StateSum ≃+* PrimeMode)
      (Q_state : StateSum →+* ℂ) (Q_mode : PrimeMode →+* ℂ)
      (D_state : StateSum → ℂ) (D_mode : PrimeMode → ℂ),
      (∀ x, Q_mode (Equiv x) = Q_state x) ∧
      (∀ x, D_mode (Equiv x) = D_state x) := by
  use StateSumUniversalSpace, BostConnesUniversalSpace, inferInstance, inferInstance
  use stateSumPrimeModeColimitEquiv
  use universalStateSumActivityEval z s, universalActivityEval z s
  use D ∘ universalStateSumActivityEval z s, universalDerivedReadout z s D
  constructor
  · exact universalActivityEval_stateSumPrimeMode z s
  · intro x
    unfold universalDerivedReadout
    simp only [Function.comp_apply]
    rw [universalActivityEval_stateSumPrimeMode]

end InfoGeometry.Categorical.PrimonParafermionGrandCanonicalColimitCapstone
