import Mathlib.CategoryTheory.Category.Basic

namespace InfoGeometry.Categorical

universe v u

/-- 
  A placeholder for an infinity category until fully specified by the InfinityCosmos formalization.
  We use a standard category for the structural definition of Giraud's Axioms.
-/
class InfinityCategory (C : Type u) extends CategoryTheory.Category.{v} C

end InfoGeometry.Categorical
