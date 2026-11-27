/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.BostConnesKMSPhaseTransition

/-!
# Boundary of the abstract Bost--Connes generator axioms

The `BostConnesSystem` structure records algebraic generator equations, but
does not encode a C*-algebra, a time-evolution action, a state, or a KMS
condition. The constant-one model below satisfies every field and makes every
mode projection the identity. Thus those generator equations alone cannot
imply properness or nontriviality of a mode projection.
-/

namespace InfoGeometry.Algebra.BostConnesKMSPhaseTransitionCounterexamples

open InfoGeometry.Algebra.BostConnesKMSPhaseTransition

/-- The trivial one-dimensional representation of all listed generators. -/
def unitModeSystem : BostConnesSystem ℝ where
  x := fun _ => 1
  x_star := fun _ => 1
  e := fun _ => 1
  x_star_x := by intros; norm_num
  x_mul := by intros; norm_num
  x_star_mul := by intros; norm_num
  e_zero := by norm_num
  e_add := by intros; norm_num
  e_periodic := by intro; norm_num

/-- In this model every range projection is exactly the identity. -/
theorem unitModeSystem_projection_eq_one (n : ℕ+) :
    unitModeSystem.x n * unitModeSystem.x_star n = 1 := by
  simp [unitModeSystem]

/-- The axioms permit a mode whose projection is not proper. -/
theorem generator_axioms_do_not_force_proper_projection :
    ∃ g : BostConnesSystem ℝ, ∃ n : ℕ+,
      g.x n * g.x_star n = 1 :=
  ⟨unitModeSystem, 1, unitModeSystem_projection_eq_one 1⟩

end InfoGeometry.Algebra.BostConnesKMSPhaseTransitionCounterexamples
