import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Proof-bearing relations for a presented path category

The declaration dependency graph is only a graph. A categorical relation is
kept separately and is a proposition on parallel paths; consequently a graph
edge never becomes a commuting triangle merely because both declarations are
reachable in the dependency DAG.
-/

namespace InfoGeometry.DAG.Category

open CategoryTheory

/-- Generating arrows for a free path category. -/
class GeneratingGraph (V : Type*) extends Quiver V

attribute [instance] GeneratingGraph.toQuiver

/-- Certified relations are propositions about parallel free paths. -/
structure CertifiedRelations (V : Type*) [GeneratingGraph V] where
  Rel : ∀ {X Y : V}, Quiver.Path X Y → Quiver.Path X Y → Prop

/-- A relation is admissible as a Mathlib quotient relation. -/
def CertifiedRelations.homRel {V : Type*} [GeneratingGraph V]
    (R : CertifiedRelations V) :
      @HomRel (Paths V) (Paths.categoryPaths V).toCategoryStruct.toQuiver :=
  fun {_ _} P Q => R.Rel P Q

end InfoGeometry.DAG.Category
