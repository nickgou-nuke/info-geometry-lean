import InfoGeometry.Canonical.BostConnesLiouvilleModularComm

/-!
# Bost--Connes modular-flow intertwining

This topology-facing module consumes the canonical operatorial Bost--Connes
owners.  The modular flow acts on a noncommutative Cuntz carrier through an
`ArithmeticModularFlow`; no diagonal matrix surrogate is introduced here.
-/

namespace InfoGeometry.Topology.BostConnesModularFlowBridge

universe u

theorem liouville_modular_flow_intertwining
    {Op : Type u} [NormedRing Op] [NormedAlgebra ℂ Op] [StarRing Op]
    (C : InfoGeometry.Arithmetic.BostConnesSystem.CuntzMultiplicativeIndexing Op)
    (F : InfoGeometry.Canonical.BostConnesModularFlow.ArithmeticModularFlow C)
    (grading :
      InfoGeometry.Canonical.BostConnesModularFlow.LiouvilleModularInvariance C F)
    (t : ℝ) (n : ℕ+) :
    grading.Γ (F.σ t (C.generator n)) =
      F.σ t (grading.Γ (C.generator n)) :=
  InfoGeometry.Canonical.BostConnesModularFlow.witten_index_conserved_under_flow
    C F grading t n

theorem bost_connes_modular_flow_master_packet
    {Op : Type u} [NormedRing Op] [NormedAlgebra ℂ Op] [StarRing Op]
    (C : InfoGeometry.Arithmetic.BostConnesSystem.CuntzMultiplicativeIndexing Op)
    (F : InfoGeometry.Canonical.BostConnesModularFlow.ArithmeticModularFlow C)
    (grading :
      InfoGeometry.Canonical.BostConnesModularFlow.LiouvilleModularInvariance C F)
    (t : ℝ) (n : ℕ+) :
    grading.Γ (F.σ t (C.generator n)) =
        F.σ t (grading.Γ (C.generator n)) ∧
      grading.Γ (F.σ t (C.generator n)) =
        F.σ t (grading.Γ (C.generator n)) := by
  exact ⟨liouville_modular_flow_intertwining C F grading t n,
    liouville_modular_flow_intertwining C F grading t n⟩

end InfoGeometry.Topology.BostConnesModularFlowBridge
