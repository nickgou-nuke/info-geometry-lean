import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite Jaynes exponential states

This is the finite algebraic/statistical owner for a reference surprisal `K`
and one supplied constraint observable `F`.  It proves positivity,
normalization, and the logarithmic state identity.  It does not claim a KMS
existence theorem, a BKM Hessian theorem, or a spectral-projector curvature
result.
-/

open scoped BigOperators

namespace InfoGeometry.Thermo

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Unnormalized Jaynes weight `exp (-K + θ F)`. -/
noncomputable def jaynesWeight
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-K ω + theta * F ω)

/-- Finite Jaynes partition function. -/
noncomputable def jaynesPartition
    (K F : Ω → ℝ) (theta : ℝ) : ℝ :=
  ∑ ω, jaynesWeight K F theta ω

/-- Normalized finite Jaynes state. -/
noncomputable def jaynesState
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) : ℝ :=
  jaynesWeight K F theta ω / jaynesPartition K F theta

theorem jaynesWeight_pos (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    0 < jaynesWeight K F theta ω := by
  unfold jaynesWeight
  exact Real.exp_pos _

theorem jaynesPartition_pos (K F : Ω → ℝ) (theta : ℝ) :
    0 < jaynesPartition K F theta := by
  classical
  unfold jaynesPartition
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Ω))
      (f := fun ω => jaynesWeight K F theta ω)
      (by intro ω hω; exact jaynesWeight_pos K F theta ω)
      Finset.univ_nonempty)

theorem jaynesState_pos (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    0 < jaynesState K F theta ω := by
  unfold jaynesState
  exact div_pos (jaynesWeight_pos K F theta ω) (jaynesPartition_pos K F theta)

theorem jaynesState_sum_one (K F : Ω → ℝ) (theta : ℝ) :
    ∑ ω, jaynesState K F theta ω = 1 := by
  classical
  unfold jaynesState
  have hZ : jaynesPartition K F theta ≠ 0 :=
    (jaynesPartition_pos K F theta).ne'
  calc
    ∑ ω, jaynesWeight K F theta ω / jaynesPartition K F theta =
        (∑ ω, jaynesWeight K F theta ω) / jaynesPartition K F theta := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset Ω))
              (f := fun ω => jaynesWeight K F theta ω)
              (a := jaynesPartition K F theta))
    _ = jaynesPartition K F theta / jaynesPartition K F theta := by
          rfl
    _ = 1 := by exact div_self hZ

theorem jaynes_logState
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    Real.log (jaynesState K F theta ω) =
      -K ω + theta * F ω - Real.log (jaynesPartition K F theta) := by
  unfold jaynesState jaynesWeight
  rw [Real.log_div (by positivity) (jaynesPartition_pos K F theta).ne']
  rw [Real.log_exp]

theorem jaynes_logState_eq_reference_surprisal
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    -Real.log (jaynesState K F theta ω) =
      K ω - theta * F ω + Real.log (jaynesPartition K F theta) := by
  rw [jaynes_logState]
  ring

end InfoGeometry.Thermo
