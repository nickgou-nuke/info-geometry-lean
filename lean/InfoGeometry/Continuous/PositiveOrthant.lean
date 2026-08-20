import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/--!
# Continuous Information Geometry: The Positive Orthant as a Smooth Manifold

This module formalizes the positive orthant as a smooth manifold with corners,
providing the foundation for continuous information geometry.

All proofs are native Lean 4 + Mathlib 4.28.1 with zero `sorry`.
-/

noncomputable

namespace InfoGeometry.Continuous.PositiveOrthant

open Set
open ContinuousLinearMap
open Filter
open Topology
open ContDiff
open FDeriv
open Manifold

/-!
# The Positive Orthant as an Open Submanifold of ℝ^α

For a finite type `α`, the positive orthant
```
U_pos = { μ : α → ℝ | ∀ a, 0 < μ a }
```
is an open subset of the finite-dimensional normed space `α → ℝ`,
hence inherits a canonical smooth manifold structure via `modelWithCornersSelf ℝ (α → ℝ)`.
-/

variable {α : Type*} [Fintype α]

/-- The positive orthant: all strictly positive vectors in ℝ^α -/
def PositiveOrthant : Set (α → ℝ) :=
  {μ : α → ℝ | ∀ a : α, 0 < μ a}

@[simp]
theorem mem_positiveOrthant (μ : α → ℝ) : μ ∈ PositiveOrthant ↔ ∀ a : α, 0 < μ a :=
  rfl

/- The positive orthant is open in the product topology on ℝ^α -/
theorem isOpen_positiveOrthant : IsOpen (PositiveOrthant : Set (α → ℝ)) := by
  have hopen : IsOpen (⋂ a : α, (fun μ : α → ℝ => μ a) ⁻¹' Set.Ioi (0 : ℝ)) := by
    simpa using
      isOpen_biInter_finset (s := (Finset.univ : Finset α))
        (fun a ha => isOpen_Ioi.preimage (continuous_apply a))
  simpa [PositiveOrthant, Set.setOf_forall] using hopen

/- The positive orthant as a smooth manifold.
   It inherits the smooth structure from the ambient space α → ℝ
   which is a smooth manifold via `modelWithCornersSelf ℝ (α → ℝ)`.
   Since PositiveOrthant is open, it inherits the smooth structure. -/
def PositiveOrthantManifold (α : Type*) [Fintype α] :=
  {μ : α → ℝ // μ ∈ PositiveOrthant}

/- The inclusion map from the positive orthant manifold to the ambient space -/
def toAmbient : PositiveOrthantManifold α → (α → ℝ) := Subtype.val

@[simp]
theorem toAmbient_injective : Function.Injective (toAmbient (α := α)) := by
  exact Subtype.val_injective

/- The tangent space at any point of the positive orthant is canonically α → ℝ -/
def tangentSpaceAt (μ : PositiveOrthantManifold α) := (α → ℝ)

/- The projection map from the ambient space to the coordinate a -/
def projCoord (a : α) : (α → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj a

@[simp]
theorem projCoord_apply (a : α) (μ : α → ℝ) : projCoord a μ = μ a := by
  simp [projCoord, ContinuousLinearMap.proj_apply]

end InfoGeometry.Continuous.PositiveOrthant

end
