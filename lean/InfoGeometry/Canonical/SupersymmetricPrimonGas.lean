import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.PrimonGas

/--
A three-way finite grading type used to label the values `1`, `-1`, and `0`.

In this canonical file it is only a discrete classifier. Interpretive links to
other geometric or physical sectors live outside this theorem surface.
-/
inductive Trifactor
| boson   -- (+1) branch of the classifier
| fermion -- (-1) branch of the classifier
| ghost   -- fallback / zero branch of the classifier

/--
Classifier from an integer readout into the three discrete labels.

This definition does not prove that the input comes from the Möbius function or
from any arithmetic/physical state space; it only sends `1 ↦ boson`, `-1 ↦
fermion`, and everything else to `ghost`.
-/
def classify_state (mu_val : ℤ) : Trifactor :=
  if mu_val = 1 then Trifactor.boson
  else if mu_val = -1 then Trifactor.fermion
  else Trifactor.ghost

/--
A state space equipped with an integer grading constrained to lie in `{1,-1,0}`.

The key datum is the explicit field `grading_bound`; this structure does not say
that the states are integers or that the grading is the Möbius function.
-/
structure SupersymmetricStateSpace where
  states : Type*
  chiral_grading : states → ℤ
  -- The grading must strictly take values in {-1, 0, 1}
  grading_bound : ∀ s, chiral_grading s = 1 ∨ chiral_grading s = -1 ∨ chiral_grading s = 0

/--
Every state in a `SupersymmetricStateSpace` is classified as boson, fermion, or
ghost, provided by the explicit hypothesis `grading_bound`.

This theorem is a finite trichotomy readout from the assumed value range
`{1,-1,0}`; it does not construct the grading from arithmetic data.
-/
theorem complete_trifactor_mapping (S : SupersymmetricStateSpace) (s : S.states) :
    classify_state (S.chiral_grading s) = Trifactor.boson ∨
    classify_state (S.chiral_grading s) = Trifactor.fermion ∨
    classify_state (S.chiral_grading s) = Trifactor.ghost := by
  have h_bound := S.grading_bound s
  rcases h_bound with h1 | h_neg1 | h0
  · -- Case: μ(n) = 1 (Boson)
    left
    dsimp [classify_state]
    rw [if_pos h1]
  · -- Case: μ(n) = -1 (Fermion)
    right; left
    dsimp [classify_state]
    -- Since it's -1, it's not 1
    have h_not_1 : S.chiral_grading s ≠ 1 := by omega
    rw [if_neg h_not_1, if_pos h_neg1]
  · -- Case: μ(n) = 0 (Ghost)
    right; right
    dsimp [classify_state]
    have h_not_1 : S.chiral_grading s ≠ 1 := by omega
    have h_not_neg1 : S.chiral_grading s ≠ -1 := by omega
    rw [if_neg h_not_1, if_neg h_not_neg1]

end InfoGeometry.PrimonGas
