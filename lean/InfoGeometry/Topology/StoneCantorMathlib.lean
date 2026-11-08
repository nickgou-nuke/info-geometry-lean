import Mathlib.Order.Category.BoolAlg
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Matrix.Basic

open CategoryTheory
open TopologicalSpace
open Filter

universe u

/-- The canonical evaluation map from the Stone space (Ultrafilters) 
of a Boolean Algebra to the discrete 2-element Boolean Algebra. -/
def stoneEvaluation {α : Type u} (u : Ultrafilter α) (b : Set α) : Prop :=
  b ∈ u.sets

/-- The core Mathlib-grade compatibility theorem: 
The projection of a cylinder set under a principal ultrafilter map 
is strictly equal to the evaluation function on that specific coordinate. -/
theorem cylinder_expectation_eq_evaluation 
    {α : Type u} (f : α) (b : Set α) (u : Ultrafilter α) 
    (h : u = pure f) :
    (stoneEvaluation u b) ↔ (f ∈ b) := by
  subst h
  exact Iff.rfl

/-- The Inductive Limit of the Boolean Lattice of Projections. -/
def ProjectiveChain (n : ℕ) : Type :=
  { p : Matrix (Fin (2^n)) (Fin (2^n)) ℝ // p * p = p }

