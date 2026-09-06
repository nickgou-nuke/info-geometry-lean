import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.IsLimit
import InfoGeometry.Causal.ProofDAGRepresentation
import InfoGeometry.Canonical.RealBoundaryHomologyQuotient
import InfoGeometry.Canonical.CategoryTheoryConeUniqueness
import InfoGeometry.Canonical.PenrosePosetCategoryFoundation

namespace InfoGeometry.Canonical.DAGHomologyCategoryCapstone

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Causal.ProofDAGRepresentation
open InfoGeometry.Canonical.RealHomologyCohomologyDictionary
open InfoGeometry.Canonical.CategoryTheoryConeUniqueness
open InfoGeometry.Canonical.PenrosePosetCategoryFoundation

variable {α : Type*} (G : ProofDAG α)
variable {C_mod : Type*} [AddCommGroup C_mod] [Module ℝ C_mod]
variable (B : RealBoundaryOperator C_mod)
variable {J : Type*} [Category J]
variable {C_cat : Type*} [Category C_cat]

theorem dag_homology_category_canonical_capstone
    (a : α) {F : J ⥤ C_cat} {s t : Cocone F}
    (hs : IsColimit s) (ht : IsColimit t) :
    (a ∈ forwardCone G a ∩ backwardCone G a) ∧
    (B.boundaries ≤ B.cycles) ∧
    (∃ (f : s.pt ⟶ t.pt) (g : t.pt ⟶ s.pt),
      f ≫ g = 𝟙 s.pt ∧ g ≫ f = 𝟙 t.pt) := by
  exact ⟨⟨forwardCone_self G a, backwardCone_self G a⟩,
    B.boundaries_le_cycles,
    colimitCocone_apex_inversePair hs ht⟩

end InfoGeometry.Canonical.DAGHomologyCategoryCapstone
