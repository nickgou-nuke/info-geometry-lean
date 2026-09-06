import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeOccupationAlgebra
import InfoGeometry.Categorical.PrimeThermodynamicDirectLimit

noncomputable section

namespace InfoGeometry.Categorical.PrimeThermodynamicLimitCapstone

open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Categorical.PrimeThermodynamicDirectLimit

@[rep_depth thermo]
abbrev BostConnesUniversalSpace :=
  PrimonAlgebra

instance : CommRing BostConnesUniversalSpace :=
  inferInstance

theorem finiteStage_embeds_exactly (n : ℕ) :
    Function.Injective (stageLimitOf n) :=
  stageLimitOf_injective n

theorem universalSpace_exhaustion (x : BostConnesUniversalSpace) :
    ∃ (n : ℕ) (y : PrimeStage n), stageLimitOf n y = x := by
  -- `BostConnesUniversalSpace` is defined via a Quotient over the Sigma type of stages.
  rcases Quotient.exists_rep x with ⟨⟨n, y⟩, rfl⟩
  exact ⟨n, y, rfl⟩

end InfoGeometry.Categorical.PrimeThermodynamicLimitCapstone
