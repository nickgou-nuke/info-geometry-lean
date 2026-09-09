import Mathlib.Tactic
import InfoGeometry.Categorical.PrimeThermodynamicReadoutCones

noncomputable section

namespace InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit

open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Categorical.PrimeThermodynamicReadoutCones
open InfoGeometry.Categorical.PrimeThermodynamicDirectLimit

def stageDerivedReadout (z s : ℂ) (D : ℂ → ℂ) (n : ℕ) : PrimeStage n → ℂ :=
  D ∘ stageActivityEval z s n

def universalDerivedReadout (z s : ℂ) (D : ℂ → ℂ) : PrimonAlgebra → ℂ :=
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

/-! Every readout value on the quotient carrier is represented by a finite
stage readout.  This is the finite exhaustion form of the colimit bridge; it
does not assert an analytic limit or a completed thermodynamic state. -/
theorem universalDerivedReadout_exhaustion
    (z s : ℂ) (D : ℂ → ℂ) (x : PrimonAlgebra) :
    ∃ (n : ℕ) (y : PrimeStage n),
      universalDerivedReadout z s D x = stageDerivedReadout z s D n y := by
  rcases stageLimitOf_surjective x with ⟨n, y, hy⟩
  refine ⟨n, y, ?_⟩
  rw [← hy]
  exact universalDerivedReadout_comp_of z s D n y

/-- The derived readout is independent of the finite representative chosen
for a point of the native direct-limit carrier. -/
theorem stageDerivedReadout_eq_of_stageLimit_eq
    (z s : ℂ) (D : ℂ → ℂ)
    {n m : ℕ} (x : PrimeStage n) (y : PrimeStage m)
    (hxy : stageLimitOf n x = stageLimitOf m y) :
    stageDerivedReadout z s D n x = stageDerivedReadout z s D m y := by
  calc
    stageDerivedReadout z s D n x =
        universalDerivedReadout z s D (stageLimitOf n x) := by
      symm
      exact universalDerivedReadout_comp_of z s D n x
    _ = universalDerivedReadout z s D (stageLimitOf m y) := by rw [hxy]
    _ = stageDerivedReadout z s D m y :=
      universalDerivedReadout_comp_of z s D m y

end InfoGeometry.Categorical.PrimeThermodynamicDLogQColimit
