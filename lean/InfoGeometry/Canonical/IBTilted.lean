import InfoGeometry.Canonical.IBNormalize
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# InfoGeometry.Canonical.IBTilted

Mathlib-aligned exponential-tilting/Jaynes layer for frozen IB updates.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.IB

variable {T : Type} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

/-- A PMF measure is counting measure with density given by the PMF weights. -/
theorem pmf_toMeasure_eq_count_withDensity
    (p : FinProb T) :
    p.toMeasure = Measure.count.withDensity (fun t => p t) := by
  ext s hs
  rw [p.toMeasure_apply hs, withDensity_apply (fun t => p t) hs,
    ← MeasureTheory.lintegral_indicator hs, MeasureTheory.lintegral_count]

section IB

variable {X Y : Type} [Fintype X] [Fintype Y]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- Frozen Gibbs/Jaynes potential on the target alphabet at a fixed source slice. -/
noncomputable def frozenPotential
    (prob : IBProblem (X := X) (Y := Y))
    (mY_givenT : T → FinProb Y)
    (x : X) : T → ℝ := fun t =>
  -prob.beta * (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal

/-- The corresponding exponential weight in `ℝ≥0∞`. -/
noncomputable def frozenWeight
    (prob : IBProblem (X := X) (Y := Y))
    (mY_givenT : T → FinProb Y)
    (x : X) : T → ℝ≥0∞ := fun t =>
  ENNReal.ofReal (Real.exp (frozenPotential prob mY_givenT x t))

@[simp] theorem frozenWeight_apply
    (prob : IBProblem (X := X) (Y := Y))
    (mY_givenT : T → FinProb Y)
    (x : X) (t : T) :
    frozenWeight prob mY_givenT x t
      =
    ENNReal.ofReal
      (Real.exp
        (-prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)) := by
  simp [frozenWeight, frozenPotential]

@[simp] theorem baScoreFrozen_eq_prior_mul_frozenWeight
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) (t : T) :
    baScoreFrozen prob qT mY_givenT x t
      = qT t * frozenWeight prob mY_givenT x t := by
  simp [baScoreFrozen, frozenWeight, frozenPotential]

theorem integrable_exp_frozenPotential
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    Integrable (fun t => Real.exp (frozenPotential prob mY_givenT x t)) qT.toMeasure :=
  Integrable.of_finite

/--
The unnormalized frozen BA score measure is the prior measure with density given
by the frozen exponential weight.
-/
theorem baScoreFrozenMeasure_toMeasure_eq_priorWithDensity
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    ((baScoreFrozenMeasure prob qT mY_givenT x : FiniteMeasure T) : Measure T)
      =
    qT.toMeasure.withDensity (frozenWeight prob mY_givenT x) := by
  rw [baScoreFrozenMeasure, discreteScoreMeasure_toMeasure, pmf_toMeasure_eq_count_withDensity]
  simpa [baScoreFrozen_eq_prior_mul_frozenWeight] using
    (withDensity_mul Measure.count
      (f := fun t => qT t)
      (g := frozenWeight prob mY_givenT x)
      (by fun_prop) (by fun_prop))

/--
The frozen exponential partition function is exactly the real total mass of the
unnormalized frozen BA score.
-/
theorem integral_exp_frozenPotential_eq_baScoreFrozen_tsum_toReal
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    ∫ t, Real.exp (frozenPotential prob mY_givenT x t) ∂qT.toMeasure
      =
    ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
  rw [PMF.integral_eq_sum]
  calc
    ∑ t : T, (qT t).toReal • Real.exp (frozenPotential prob mY_givenT x t)
      =
    ∑ t : T, (baScoreFrozen prob qT mY_givenT x t).toReal := by
        refine Finset.sum_congr rfl ?_
        intro t _
        rw [baScoreFrozen_eq_prior_mul_frozenWeight]
        simp [frozenWeight, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
          mul_assoc, mul_left_comm, mul_comm, (Real.exp_pos _).le]
    _ = ((∑ t : T, baScoreFrozen prob qT mY_givenT x t).toReal) := by
        symm
        exact ENNReal.toReal_sum (fun t _ => baScoreFrozen_ne_top prob qT mY_givenT x t)
    _ = ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
        rw [tsum_fintype]

/--
Singleton formula for the frozen tilted prior. This is the exact measure-level
Esscher/Jaynes update corresponding to the frozen BA step.
-/
theorem baFrozenTilted_apply_singleton
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) (t : T) :
    (qT.toMeasure.tilted (frozenPotential prob mY_givenT x)) {t}
      =
    ENNReal.ofReal
      (Real.exp (frozenPotential prob mY_givenT x t) /
        ((∑' s, baScoreFrozen prob qT mY_givenT x s).toReal))
      * qT t := by
  rw [tilted_apply' (μ := qT.toMeasure) (f := frozenPotential prob mY_givenT x)
      (hs := measurableSet_singleton t)]
  rw [MeasureTheory.lintegral_singleton]
  rw [PMF.toMeasure_apply_singleton qT t (measurableSet_singleton t)]
  congr 1
  rw [integral_exp_frozenPotential_eq_baScoreFrozen_tsum_toReal]

end IB

end InfoGeometry.Canonical.IB
