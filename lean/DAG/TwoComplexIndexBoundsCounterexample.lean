/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.SelfLoopIncidenceRegression
import Mathlib.Tactic

/-! A concrete malformed indexed complex and a precise validity contract. -/
namespace DAG.TwoComplexIndexBoundsCounterexample

open SelfLoopIncidenceRegression

/-- Three vertices but an edge whose target index is outside the vertex carrier. -/
def outOfRangeTarget : TwoComplex Nat :=
  { oneLoop with
    base := { oneLoop.base with
      toGraph := { oneLoop.base.toGraph with nodes := #[0, 1, 2] } }
    edges := #[(0, 3)] }

/-- The malformed edge violates the endpoint portion of the explicit contract. -/
theorem out_of_range_target_not_valid :
    ¬ DAG.HasValidIndices outOfRangeTarget := by
  intro h
  have htarget := h.1 ⟨0, by decide⟩ |>.2
  norm_num [outOfRangeTarget, oneLoop] at htarget

/-- Totalized matrix incidence silently drops the out-of-carrier target and retains
the source coefficient. This is the counterexample to interpreting arbitrary
`TwoComplex` payloads as cellular maps without `HasValidIndices`. -/
theorem array_incidence_truncates_out_of_range_target :
    DAG.boundary1 outOfRangeTarget = #[#[-1, 0, 0]] := by
  apply Array.ext
  · rfl
  · intro i hi₁ hi₂
    have hi0 : i < 1 := by
      simpa [DAG.boundary1, outOfRangeTarget, oneLoop] using hi₁
    have hi0' : i = 0 := by omega
    clear hi0
    subst i
    apply Array.ext
    · rfl
    · intro j hj₁ hj₂
      have hj3 : j < 3 := by
        simpa [DAG.boundary1, outOfRangeTarget, oneLoop] using hj₂
      have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with h | h | h <;> subst j
      all_goals norm_num [DAG.boundary1, DAG.incidenceBoundaryCoeff,
        outOfRangeTarget, oneLoop]

theorem matrix_incidence_truncates_out_of_range_target :
    DAG.boundary1Matrix outOfRangeTarget
        (⟨0, by decide⟩ : Fin outOfRangeTarget.edges.size)
        (⟨1, by decide⟩ : Fin outOfRangeTarget.base.toGraph.nodes.size) = 0 := by
  norm_num [DAG.boundary1Matrix, DAG.incidenceBoundaryCoeff,
    outOfRangeTarget, oneLoop]

end DAG.TwoComplexIndexBoundsCounterexample
