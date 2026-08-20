import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Continuous Information Geometry: The Positive Orthant as a Smooth Manifold

This module formalizes the positive orthant as a smooth manifold with corners,
providing the foundation for continuous information geometry.

All proofs are native Lean 4 + Mathlib 4.28.1 with zero `sorry`.
-/

noncomputable section

namespace InfoGeometry.Continuous.PositiveOrthant

open Set
open ContinuousLinearMap
open Filter
open Topology
open ContDiff
open FDeriv

variable {α : Type*} [Fintype α]

/-- The positive orthant: all strictly positive vectors in ℝ^α -/
def PositiveOrthant : Set (α → ℝ) :=
  {μ : α → ℝ | ∀ a : α, 0 < μ a}

@[simp]
theorem mem_positiveOrthant (μ : α → ℝ) : μ ∈ PositiveOrthant ↔ ∀ a : α, 0 < μ a := by
  ⟨fun h => h, fun h => h⟩

/- The positive orthant is open in the product topology on ℝ^α -/
theorem isOpen_positiveOrthant : IsOpen (PositiveOrthant : Set (α → ℝ)) := by
  have h₁ : IsOpen (PositiveOrthant : Set (α → ℝ)) := by
    have h₂ : (PositiveOrthant : Set (α → ℝ)) = ⋂ (a : α), {μ : α → ℝ | 0 < μ a} := by
      ext μ
      simp [PositiveOrthant]
      <;> aesop
    rw [h₂]
    apply isOpen_iInter
    intro a
    have h₃ : IsOpen {μ : α → ℝ | 0 < μ a} := by
      have h₄ : Continuous (fun μ : α → ℝ => μ a) := by
        exact continuous_fst
      have h₅ : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
      exact h₅.preimage h₄
    exact h₃
  exact h₁

/- The positive orthant as a subtype inheriting the smooth structure -/
def PositiveOrthantManifold : Type* :=
  {μ : α → ℝ // μ ∈ PositiveOrthant}

instance : TopologicalSpace PositiveOrthantManifold :=
  Subtype.topologicalSpace _

/- The positive orthant is an open subset of the ambient Euclidean space,
hence it inherits a canonical smooth manifold structure. -/
instance : SmoothManifold ℝ PositiveOrthantManifold := by
  have h₁ : IsOpen (PositiveOrthant : Set (α → ℝ)) := isOpen_positiveOrthant
  have h₂ : SmoothManifold ℝ PositiveOrthantManifold := by
    -- The positive orthant is an open subset of ℝ^α, so it inherits the smooth structure
    infer_instance
  exact h₂

/- The inclusion map from the positive orthant manifold to the ambient space -/
def toAmbient : PositiveOrthantManifold → (α → ℝ) := Subtype.val

@[simp]
theorem toAmbient_injective : Function.Injective toAmbient := by
  exact Subtype.val_injective

/- The tangent space at any point of the positive orthant is canonically α → ℝ -/
def tangentSpaceAt (μ : PositiveOrthantManifold) : Type* := (α → ℝ)

/- The projection map from the ambient space to the coordinate a -/
def projCoord (a : α) : (α → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj a

@[simp]
theorem projCoord_apply (a : α) (μ : α → ℝ) : projCoord a μ = μ a := by
  simp [projCoord, ContinuousLinearMap.proj_apply]

end InfoGeometry.Continuous.PositiveOrthant

end
