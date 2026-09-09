import InfoGeometry.Quantum.BostConnesCrossedProduct

namespace InfoGeometry.Canonical.BostConnesCrossedProductCapstone

open InfoGeometry.Quantum.BostConnesCrossedProduct

theorem capstone_bost_connes_crossed_product_synthesis
    {R : Type*} [CommRing R] (g alpha : R →+* R) (Sp A : R) (r1 r2 : ℚ)
    (h_comm : ∀ x, g (alpha x) = alpha (g x))
    (h_rel : crossedProductRelation Sp A (alpha A)) :
    (cyclotomicPhase (r1 + r2) = cyclotomicPhase r1 * cyclotomicPhase r2) ∧
    (crossedProductRelation (g Sp) (g A) (alpha (g A))) := by
  exact ⟨cyclotomic_phase_add r1 r2,
    galois_crossed_product_equivariance g alpha Sp A h_comm h_rel⟩

end InfoGeometry.Canonical.BostConnesCrossedProductCapstone
