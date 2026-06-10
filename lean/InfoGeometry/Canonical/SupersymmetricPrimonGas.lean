import Mathlib

namespace InfoGeometry.PrimonGas

/--
The Algebraic Trifactor type representing the Supersymmetry grading.
This maps exactly to the {-1, 0, 1} roots of the geometric signature.
-/
inductive Trifactor
| boson   -- (+1) : The J-even sector (Completed Xi)
| fermion -- (-1) : The J-odd sector (Supercharge driver)
| ghost   -- (0)  : The Cuntz boundary (Annihilated states)

/--
In the Supersymmetric Primon Gas, the state space (the integers) is partitioned
into three distinct sectors by the chiral grading operator (-1)^F, which evaluates
to the Möbius function μ(n).
-/
def classify_state (mu_val : ℤ) : Trifactor :=
  if mu_val = 1 then Trifactor.boson
  else if mu_val = -1 then Trifactor.fermion
  else Trifactor.ghost

/--
The definition of a Supersymmetric State Space for the Primon Gas.
The key constraint is that the chiral grading MUST strictly collapse into the trifactor,
proving that there are no "leaks" outside of the Boson/Fermion/Ghost classification.
-/
structure SupersymmetricStateSpace where
  states : Type*
  chiral_grading : states → ℤ
  -- The grading must strictly take values in {-1, 0, 1}
  grading_bound : ∀ s, chiral_grading s = 1 ∨ chiral_grading s = -1 ∨ chiral_grading s = 0

/--
Theorem: Every valid quantum state in the Supersymmetric Primon Gas maps uniquely
to one of the three topological sectors of the algebraic trifactor.
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
