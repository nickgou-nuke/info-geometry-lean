import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn

namespace Basic

noncomputable section

open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-- Cantor space as the countable product of two-point discrete spaces. -/
abbrev CantorSpace : Type :=
  ℕ → Bool

/-- The fair one-bit probability measure, implemented by mathlib's finite uniform measure. -/
def bernoulliHalf : Measure Bool :=
  ProbabilityTheory.uniformOn (Set.univ : Set Bool)

instance bernoulliHalf_isProbabilityMeasure :
    IsProbabilityMeasure bernoulliHalf := by
  unfold bernoulliHalf
  infer_instance

/-- Each Boolean singleton has fair-bit mass `1 / 2`. -/
theorem bernoulliHalf_singleton (b : Bool) :
    bernoulliHalf {b} = (1 / 2 : ℝ≥0∞) := by
  unfold bernoulliHalf
  rw [ProbabilityTheory.uniformOn_univ]
  norm_num [Fintype.card_bool]

/-- The canonical Bernoulli product measure on Cantor space. -/
def fractalMeasure : Measure CantorSpace :=
  Measure.infinitePi (fun _ : ℕ => bernoulliHalf)

instance fractalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure fractalMeasure := by
  unfold fractalMeasure
  infer_instance

/-- A finite-coordinate cylinder in Cantor space. -/
def cylinderSet (s : Finset ℕ) (f : ℕ → Bool) : Set CantorSpace :=
  {x | ∀ i ∈ s, x i = f i}

/--
The Bernoulli product measure of a finite coordinate cylinder is `(1 / 2) ^ |s|`.
This is exactly mathlib's `Measure.infinitePi_pi` specialized to Boolean
singletons.
-/
theorem measure_cylinderSet (s : Finset ℕ) (f : ℕ → Bool) :
    fractalMeasure (cylinderSet s f) = (1 / 2 : ℝ≥0∞) ^ s.card := by
  unfold fractalMeasure cylinderSet
  classical
  let t : (i : ℕ) → Set Bool := fun i => {f i}
  have hset : {x : (i : ℕ) → Bool | ∀ i ∈ s, x i = f i} = Set.pi s t := by
    ext x
    simp [t]
  rw [hset]
  rw [Measure.infinitePi_pi]
  · rw [Finset.prod_congr rfl (fun i _hi => bernoulliHalf_singleton (f i))]
    rw [Finset.prod_const]
  · intro i _hi
    exact measurableSet_singleton (f i)

end

end Basic
