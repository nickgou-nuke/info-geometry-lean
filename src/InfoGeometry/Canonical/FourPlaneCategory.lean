import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import InfoGeometry.Canonical.FourPlaneD4Incidence

open CategoryTheory

namespace InfoGeometry.Canonical

/-- Define a `Quiver` instance over `FourPlaneVertex` using the graph adjacency. -/
instance d4StarQuiver : Quiver FourPlaneVertex where
  Hom v w := PLift (d4StarGraph.Adj v w)

/-- The Path category of the incidence graph. -/
abbrev D4StarPathCategory := Paths FourPlaneVertex

/-- Object map: assign each vertex its corresponding `fourPlaneSector` in `ModuleCat ℤ`. -/
def fourPlaneSectorObj (v : FourPlaneVertex) : ModuleCat ℤ :=
  ModuleCat.of ℤ (fourPlaneSector v)

/-- A specific prefunctor from the incidence graph's quiver into `ModuleCat ℤ`. -/
def d4StarPrefunctor : Prefunctor FourPlaneVertex (ModuleCat ℤ) where
  obj := fourPlaneSectorObj
  map {_ _} _ := 0 -- the zero homomorphism between submodules

/-- The canonical path functor into `ModuleCat ℤ`. -/
def d4StarFunctor : D4StarPathCategory ⥤ ModuleCat ℤ :=
  Paths.lift d4StarPrefunctor

end InfoGeometry.Canonical
