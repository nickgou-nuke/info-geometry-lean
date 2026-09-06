import Mathlib.CategoryTheory.Category.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy

open CategoryTheory

universe v u

/-- The nerve of a category is a simplicial set. -/
def nerve_SSet (C : Type u) [SmallCategory C] : SSet.{u} :=
  nerve C
