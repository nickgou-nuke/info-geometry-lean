import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

theorem stageLimitOf_surjective (x : PrimonAlgebra) :
    ∃ (n : ℕ) (y : PrimeStage n), stageLimitOf n y = x := by
  rcases Quotient.exists_rep x with ⟨⟨n, y⟩, rfl⟩
  exact ⟨n, y, rfl⟩

theorem stageLimitOf_eq_iff {n : ℕ} {x y : PrimeStage n} :
    stageLimitOf n x = stageLimitOf n y ↔ x = y := by
  exact directLimitOf_eq_iff_of_injective primeBond primeBond_injective

theorem stageLimitOf_eq_zero_iff {n : ℕ} {x : PrimeStage n} :
    stageLimitOf n x = 0 ↔ x = 0 := by
  exact directLimitOf_eq_zero_iff_of_injective primeBond primeBond_injective

theorem stageLimitOf_powZero_iff (n k : ℕ) (x : PrimeStage n) :
    stageLimitOf n x ^ k = 0 ↔ x ^ k = 0 := by
  constructor
  · intro h
    apply (directLimitOf_eq_zero_iff_of_injective primeBond primeBond_injective).mp
    rw [map_pow]
    exact h
  · intro h
    rw [← map_pow, h]
    exact map_zero (stageLimitOf n)

end InfoGeometry.Categorical.PrimeThermodynamicDirectLimit
