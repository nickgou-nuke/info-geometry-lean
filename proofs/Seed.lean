import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib
import Mathlib

open CategoryTheory
open CategoryTheory.Limits

/-!
# The Causal Cone as a Filtered Colimit

We formalize the pipeline of conservative extensions as a directed, filtered category.
Each extension $\mathbb{L}_n$ is an object, and the conservative inclusion $\mathbb{L}_n \preceq \mathbb{L}_{n+1}$ is a morphism.
The apex (the compiled theory) is the filtered colimit of this diagram.
-/

universe v u

-- Let `TheoryStage` represent the category of formalization stages.
-- For now, we stub this out as an arbitrary category that is filtered.
variable {TheoryStage : Type u} [Category.{v} TheoryStage] [IsFiltered TheoryStage]

-- The functor mapping each stage to its formalized content (e.g., types, rings, operators)
variable {C : Type u} [Category.{v} C]
variable (F : TheoryStage ⥤ C)

-- If the target category has filtered colimits, we can construct the apex of our theory.
variable [HasFilteredColimits C]

/-- 
The apex of the confabulation process. 
This is the native direct filtered inductive colimit of our theory stages.
-/
noncomputable def TheoryApex : C := colimit F

/-!
# The Fibonacci Seed (Golden Rule)

At the base of this filtered colimit, we have our initial seed operators.
-/

inductive Obj : Type
| I : Obj
| τ : Obj

open Obj

-- The Fusion Rule: τ ⊗ τ = I ⊕ τ
def fusion : Obj → Obj → List Obj
| I, I => [I]
| I, τ => [τ]
| τ, I => [τ]
| τ, τ => [I, τ]
