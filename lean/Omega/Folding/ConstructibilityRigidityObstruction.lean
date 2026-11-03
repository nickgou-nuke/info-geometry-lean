/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber
import Omega.Folding.MicrostateResidualWindowReachability
import Omega.Folding.Rewrite

namespace Omega.Folding

open scoped BigOperators

/-- The Dirac mass at a stable target `x`, used to specialize the residual-window theorem. -/
noncomputable def pointMass {m : ℕ} (x : X m) : X m → ℝ :=
  by
    classical
    exact fun y => if y = x then 1 else 0

lemma pointMass_nonneg {m : ℕ} (x : X m) : ∀ y, 0 ≤ pointMass x y := by
  classical
  intro y
  by_cases hy : y = x <;> simp [pointMass, hy]

lemma pointMass_sum {m : ℕ} (x : X m) : ∑ y, pointMass x y = 1 := by
  classical
  simp [pointMass]

lemma residualWindow_pointMass {m : ℕ} (x : X m) :
    residualWindow (pointMass x) X.fiberMultiplicity = Real.log (X.fiberMultiplicity x : ℝ) := by
  classical
  unfold residualWindow pointMass
  simp

/-- The fold is surjective and stable, irreducible digit configurations are unique
within each value class, and the point-mass residual profile attains every
scaled value in the fiber window.

The final clause includes the pointwise residual bounds, weighted identity,
entropy decomposition, and both interval bounds. These are the properties
proved here; no separate impossibility or trichotomy assertion is made. -/
theorem fold_structure_and_point_mass_residual_window
    (m : ℕ) (x : X m) :
    Function.Surjective (Fold (m := m)) ∧
      Fold x.1 = x ∧
      (∀ a b : Rewrite.DigitCfg, Rewrite.Irreducible a → Rewrite.Irreducible b →
        Rewrite.value a = Rewrite.value b → a = b) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∃ fiberResidual : X m → ℝ,
          (∀ y, fiberResidual y = t * Real.log (X.fiberMultiplicity y : ℝ)) ∧
          (∀ y, 0 ≤ fiberResidual y ∧
            fiberResidual y ≤ Real.log (X.fiberMultiplicity y : ℝ)) ∧
          (∑ y, pointMass x y * fiberResidual y =
            t * Real.log (X.fiberMultiplicity x : ℝ)) ∧
          (0 ≤ t * Real.log (X.fiberMultiplicity x : ℝ) ∧
            t * Real.log (X.fiberMultiplicity x : ℝ) ≤
              Real.log (X.fiberMultiplicity x : ℝ)) ∧
          (Real.log (X.fiberMultiplicity x : ℝ) -
              t * Real.log (X.fiberMultiplicity x : ℝ) =
            (1 - t) * Real.log (X.fiberMultiplicity x : ℝ)) ∧
          (0 ≤ (1 - t) * Real.log (X.fiberMultiplicity x : ℝ) ∧
            (1 - t) * Real.log (X.fiberMultiplicity x : ℝ) ≤
              Real.log (X.fiberMultiplicity x : ℝ)) := by
  refine ⟨Fold_surjective m, Fold_stable x, ?_, ?_⟩
  · intro a b hIrrA hIrrB hVal
    exact Rewrite.irreducible_eq_of_value_eq hIrrA hIrrB hVal
  · intro t ht0 ht1
    obtain ⟨fiberResidual, hResidual, hPointwiseBounds, hWeighted, hInterval, hAffine,
        hEntropy⟩ :=
      paper_fold_microstate_residual_window_reachability
        (pi := pointMass x) (d := X.fiberMultiplicity) (Hpi := 0)
        (pointMass_nonneg x) (by simpa using pointMass_sum x) X.fiberMultiplicity_pos t ht0 ht1
    refine ⟨fiberResidual, hResidual, hPointwiseBounds, ?_, ?_, ?_, ?_⟩
    · simpa [residualWindow_pointMass x] using hWeighted
    · simpa [residualWindow_pointMass x] using hInterval
    · simpa [residualWindow_pointMass x] using hAffine
    · simpa [residualWindow_pointMass x] using hEntropy

end Omega.Folding
