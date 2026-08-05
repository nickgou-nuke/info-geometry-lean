import Mathlib
import InfoGeometry.Canonical.TripotentFiveGradingDecomposition
import InfoGeometry.Topology.SymbolicLatentSpace

/-!
# Symbolic latent packaging for the tripotent five-grade labels

This file does not claim a new grading theorem.  It packages the finite
five-grade label space as a discrete symbolic-latent system, so the existing
topological latent-space API can read the five-grade index as a closed and
continuous observable family.
-/

namespace InfoGeometry.Topology.TripotentFiveGradeSymbolicLatent

open InfoGeometry.Canonical
open InfoGeometry.Topology

noncomputable section

local instance : TopologicalSpace FiveGrade := ⊥
local instance : DiscreteTopology FiveGrade := discreteTopology_bot FiveGrade

/-- One-hot observable attached to a single five-grade label. -/
def fiveGradeIndicator (k : FiveGrade) : SymbolicLatentObservable FiveGrade :=
  ⟨fun g => if g = k then (1 : ℝ) else 0, continuous_of_discreteTopology⟩

/-- The finite symbolic latent system of five one-hot grade observables. -/
def fiveGradeSystem : FiniteSymbolicLatentSystem FiveGrade FiveGrade :=
  fun k => fiveGradeIndicator k

@[simp] theorem fiveGradeIndicator_apply_self (k : FiveGrade) :
    fiveGradeIndicator k k = 1 := by
  simp [fiveGradeIndicator]

@[simp] theorem fiveGradeIndicator_apply_ne {k g : FiveGrade} (h : g ≠ k) :
    fiveGradeIndicator k g = 0 := by
  simp [fiveGradeIndicator, h]

/-- The one-hot observation map is injective on the five-grade labels. -/
theorem fiveGradeObservationMap_injective :
    Function.Injective (symbolicObservationMap fiveGradeSystem) := by
  intro x y hxy
  by_cases h : x = y
  · exact h
  · exfalso
    have hyx : y ≠ x := by
      intro hyx
      apply h
      exact hyx.symm
    have hx := congrArg (fun f => f x) hxy
    simp [symbolicObservationMap, fiveGradeSystem, fiveGradeIndicator, hyx] at hx

/-- Each one-hot grade observable has a singleton 1-fiber. -/
theorem fiveGradeIndicator_fiber_one (k : FiveGrade) :
    (fiveGradeIndicator k).fiber 1 = {k} := by
  ext g
  constructor
  · intro hg
    by_cases h : g = k
    · exact h
    · exfalso
      have hbad := hg
      simp [SymbolicLatentObservable.fiber, fiveGradeIndicator, h] at hbad
  · intro hg
    subst hg
    simp [SymbolicLatentObservable.fiber, fiveGradeIndicator]

/-- The one-hot solution set is a singleton and therefore compact. -/
theorem fiveGradeSystem_solutionSet_singleton (k : FiveGrade) :
    fiveGradeSystem.solutionSet (fun j => if j = k then (1 : ℝ) else 0) = {k} := by
  ext x
  constructor
  · intro hx
    by_cases h : x = k
    · exact h
    · exfalso
      have hxk := hx k
      simp [fiveGradeSystem, fiveGradeIndicator, h] at hxk
  · intro hx
    subst x
    intro j
    by_cases h : j = k
    · simp [fiveGradeSystem, fiveGradeIndicator, h, eq_comm]
    · simp [fiveGradeSystem, fiveGradeIndicator, h, eq_comm]

theorem fiveGradeSystem_solutionSet_isCompact (k : FiveGrade) :
    IsCompact (fiveGradeSystem.solutionSet (fun j => if j = k then (1 : ℝ) else 0)) := by
  rw [fiveGradeSystem_solutionSet_singleton]
  exact isCompact_singleton

end

end InfoGeometry.Topology.TripotentFiveGradeSymbolicLatent
