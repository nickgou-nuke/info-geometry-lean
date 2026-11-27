/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The group of smooth measure-preserving automorphisms

Smoothness in both directions and preservation of the chosen measure define a
native subgroup of the homeomorphism group. Closure under composition and
inversion is proved from Mathlib's calculus and measure transport theorems.
Preservation of a measure may include orientation-reversing maps; preservation
of an oriented volume form is a separate condition.
No infinite-dimensional manifold or Lie-group structure is asserted.
-/

namespace InfoGeometry.Canonical

open MeasureTheory
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Smooth automorphisms preserving a specified measure, with native group laws. -/
def smoothVolumePreservingSubgroup (μ : Measure E) : Subgroup (E ≃ₜ E) where
  carrier := {e | ContDiff ℝ ∞ (e : E → E) ∧
    ContDiff ℝ ∞ (e.symm : E → E) ∧ MeasurePreserving e μ μ}
  one_mem' := ⟨contDiff_id, contDiff_id, MeasurePreserving.id μ⟩
  mul_mem' := by
    intro f g hf hg
    exact ⟨hf.1.comp hg.1, hg.2.1.comp hf.2.1, hf.2.2.comp hg.2.2⟩
  inv_mem' := by
    intro f hf
    exact ⟨hf.2.1, hf.1, MeasurePreserving.symm f.toMeasurableEquiv hf.2.2⟩

end InfoGeometry.Canonical
