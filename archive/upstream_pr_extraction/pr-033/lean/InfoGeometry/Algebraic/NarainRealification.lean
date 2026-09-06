/-
InfoGeometry/Algebraic/NarainRealification.lean

Realification layer between the integral Narain charge lattice and the real
split Clifford substrate.

This file does not identify the lattice with the split module definitionally.
It only records the normalization theorem for the explicit realification map.
-/

import InfoGeometry.Algebraic.SplitCliffordCarrier

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Algebraic.SplitSignature

/--
The explicit realification map from Narain charges into the split module.

This is just the transport map from `NarainCharge n` to `SplitModule n`.
The normalization theorem is proved separately.
-/
def narainRealification {n : ℕ} : NarainCharge n → SplitModule n :=
  narainToSplit

/--
The split quadratic form of the realified Narain charge expands to a sum of
pairwise momentum-winding couplings.

This is the unnormalized realification identity.
-/
theorem narainRealification_splitQuadraticForm_eq_four_sum
    {n : ℕ} (v : NarainCharge n) :
    splitQuadraticForm n (narainRealification v) =
      ∑ i : Fin n, (4 : ℝ) * ((v.1 i : ℤ) : ℝ) * ((v.2 i : ℤ) : ℝ) := by
  classical
  rw [narainRealification, splitQuadraticForm_apply]
  simp [narainToSplit, Fintype.sum_sum_type, ← Finset.sum_add_distrib, - Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [splitWeight]
  ring

/--
Normalization theorem for the realification layer.

The chosen `narainRealification` is unnormalized, so the split quadratic form
returns `4 * ∑ mᵢ wᵢ`, i.e. `2 * narainQuadratic`.
-/
theorem narainRealification_splitQuadraticForm_eq_two_mul_narainQuadratic
    {n : ℕ} (v : NarainCharge n) :
    splitQuadraticForm n (narainRealification v) =
      (2 : ℝ) * ((narainQuadratic n v : ℤ) : ℝ) := by
  calc
    splitQuadraticForm n (narainRealification v)
        = ∑ i : Fin n, (4 : ℝ) * ((v.1 i : ℤ) : ℝ) * ((v.2 i : ℤ) : ℝ) := by
            exact narainRealification_splitQuadraticForm_eq_four_sum v
    _ = (2 : ℝ) * ((narainQuadratic n v : ℤ) : ℝ) := by
      rw [narainQuadratic]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/--
The realification map is compatible with the split Clifford generator map.
-/
theorem narainCliffordVector_sq
    {n : ℕ} (v : NarainCharge n) :
    splitCliffordVector n (narainRealification v) *
        splitCliffordVector n (narainRealification v) =
      algebraMap ℝ (Cl_nn n)
        ((2 : ℝ) * ((narainQuadratic n v : ℤ) : ℝ)) := by
  rw [splitCliffordVector_sq]
  exact congrArg (algebraMap ℝ (Cl_nn n)) (narainRealification_splitQuadraticForm_eq_two_mul_narainQuadratic v)

end InfoGeometry.Algebraic.SplitSignature
