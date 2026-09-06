import Mathlib.Tactic
import InfoGeometry.Algebra.HypercomplexTriad

/-!
# InfoGeometry.Canonical.SplitCliffordVacuumExpectation

Mathematical Proof:
This file formally defines the Vacuum Expectation Value (VEV) as a linear
functional on the local `2 × 2` CAR algebra.

It proves that applying the VEV to the microscopic current commutator
extracts exactly the scalar anomaly `1`, representing the central extension
(Schwinger term) seed.

No placeholders. No `sorry`.
-/

namespace InfoGeometry.Canonical.SplitCliffordVacuumExpectation

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad

noncomputable section

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/--
The Vacuum Expectation Value functional `⟨0|M|0⟩`.
For `|0⟩ = [1,0]ᵀ`, this is the `(0,0)` matrix entry.
-/
def vev (M : M2R) : ℝ := M 0 0

/-- Local annihilation operator. -/
abbrev a_op : M2R := N

/-- Local creation operator. -/
def aDag_op : M2R :=
  !![0, 0;
     1, 0]

/-- `vev (a a†) = 1`. -/
theorem vev_annihilate_create :
    vev (a_op * aDag_op) = 1 := by
  unfold vev a_op aDag_op N
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `vev (a† a) = 0`. -/
theorem vev_create_annihilate :
    vev (aDag_op * a_op) = 0 := by
  unfold vev a_op aDag_op N
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Microscopic Schwinger seed: `vev ([a,a†]) = 1`. -/
theorem vev_commutator_anomaly :
    vev (a_op * aDag_op - aDag_op * a_op) = 1 := by
  unfold vev a_op aDag_op N
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Linearity of `vev`. -/
theorem vev_linear (M L : M2R) (c : ℝ) :
    vev (M + L) = vev M + vev L ∧ vev (c • M) = c * vev M := by
  constructor <;> rfl

end

end InfoGeometry.Canonical.SplitCliffordVacuumExpectation
