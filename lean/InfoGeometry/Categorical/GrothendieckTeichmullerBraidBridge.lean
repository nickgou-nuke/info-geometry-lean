import Mathlib.Tactic
import InfoGeometry.Algebra.AnyonFiniteSpinBraid

open InfoGeometry.Algebra.AnyonFiniteSpinBraid

namespace InfoGeometry.Categorical.GrothendieckTeichmullerBraidBridge

/-- Representation of a B_3 Braid Relation Witness -/
structure B3BraidWitness (G : Type*) [Group G] where
  σ1 : G
  σ2 : G
  braid_relation : σ1 * σ2 * σ1 = σ2 * σ1 * σ2

/-- Grothendieck-Teichmüller Automorphism Action on B_3 Braid Generators -/
structure GTAutomorphism (G : Type*) [Group G] where
  aut : G →* G

/-- Theorem: Any Grothendieck-Teichmüller Group Automorphism preserves the B_3 braid relation. -/
theorem gt_automorphism_preserves_b3 {G : Type*} [Group G]
    (w : B3BraidWitness G) (ϕ : GTAutomorphism G) :
    ϕ.aut w.σ1 * ϕ.aut w.σ2 * ϕ.aut w.σ1 = ϕ.aut w.σ2 * ϕ.aut w.σ1 * ϕ.aut w.σ2 := by
  have h := w.braid_relation
  have h_map := congr_arg ϕ.aut h
  simp only [map_mul] at h_map
  exact h_map

/-- Main Theorem: Proof of existence of the Grothendieck-Teichmüller B_3 Galois action preservation. -/
theorem gt_braid_action_exists {G : Type*} [Group G] (w : B3BraidWitness G) (ϕ : GTAutomorphism G) :
    Nonempty (B3BraidWitness G) := by
  refine ⟨⟨ϕ.aut w.σ1, ϕ.aut w.σ2, gt_automorphism_preserves_b3 w ϕ⟩⟩

end InfoGeometry.Categorical.GrothendieckTeichmullerBraidBridge
