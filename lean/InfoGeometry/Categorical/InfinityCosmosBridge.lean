import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

open CategoryTheory

universe v u

/-- The nerve of a category is a simplicial set. -/
def nerve_SSet (C : Type u) [SmallCategory C] : SSet.{u} :=
  nerve C
