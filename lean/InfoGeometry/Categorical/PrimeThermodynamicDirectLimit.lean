import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeOccupationAlgebra
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

noncomputable section

namespace InfoGeometry.Categorical.PrimeThermodynamicDirectLimit

open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

@[rep_depth thermo]
abbrev PrimonAlgebra :=
  DirectLimitSuperClosure primeBond

@[rep_depth thermo]
def stageLimitOf (n : ℕ) : PrimeStage n →+* PrimonAlgebra :=
  directLimitOf primeBond n

@[simp]
theorem stageLimitOf_bond (n : ℕ) (x : PrimeStage n) :
    stageLimitOf (n + 1) (primeBond n x) = stageLimitOf n x :=
  directLimitOf_bond primeBond n x

theorem stageLimitOf_injective (n : ℕ) :
    Function.Injective (stageLimitOf n) := by
  apply directLimitOf_injective
  exact primeBond_injective

end InfoGeometry.Categorical.PrimeThermodynamicDirectLimit
