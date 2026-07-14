import InfoGeometry.Physics.Pin55Formal
import InfoGeometry.BottPeriodicityReconciliation

/-!
# Finite `Cl(5,5)` shadow packet

This file records only explicit finite split-signature identities already proved
elsewhere in-repo.

It does NOT construct the full Clifford algebra `Cl(5,5) ≃ M₃₂(ℝ)`, a full
`Pin(5,5)`/`Spin(5,5)` representation theory, or any topological/physical
interpretation.  It packages the finite algebraic shadow currently available:

- the split quadratic form has one displayed positive and one displayed negative
  basis vector;
- those displayed basis vectors are orthogonal;
- their Clifford generators satisfy the exact square and anticommutation laws;
- the product generator squares to `1`;
- the underlying `Cl(1,1)` block identities are already verified entrywise.
-/

noncomputable section

namespace Cl55FiniteShadowPacket

open InfoGeometry.Physics.Pin55Formal
open BottPeriodicityReconciliation

/-- Displayed split-signature signs and orthogonality in the `(5,5)` form. -/
theorem displayed_split_signature :
    q55 ε₀ = 1 ∧ q55 ε₅ = -1 ∧ q55.IsOrtho ε₀ ε₅ := by
  exact ⟨q55_ε₀, q55_ε₅, ε₀_ε₅_orth⟩

/-- Exact Clifford relations for the displayed `(5,5)` generators. -/
theorem displayed_clifford_relations :
    r₀ * r₀ = 1 ∧ r₅ * r₅ = -1 ∧ r₀ * r₅ = -(r₅ * r₀) := by
  exact ⟨r₀_sq, r₅_sq, anticomm⟩

/-- The displayed product generator has exact square `1`. -/
theorem displayed_product_square :
    (r₀ * r₅) * (r₀ * r₅) = 1 :=
  v4_relation

/-- The entrywise `Cl(1,1)` block already verified in the repo. -/
theorem cl11_block_shadow :
    sigma1 * sigma1 = I2 ∧
    epsilon * epsilon = -I2 ∧
    sigma1 * epsilon + epsilon * sigma1 = 0 :=
  cl11_generator_relations

/-- Finite theorem-honest packet for the currently available split-signature shadow. -/
theorem finite_cl55_shadow_packet :
    (q55 ε₀ = 1 ∧ q55 ε₅ = -1 ∧ q55.IsOrtho ε₀ ε₅) ∧
    (r₀ * r₀ = 1 ∧ r₅ * r₅ = -1 ∧ r₀ * r₅ = -(r₅ * r₀)) ∧
    ((r₀ * r₅) * (r₀ * r₅) = 1) ∧
    (sigma1 * sigma1 = I2 ∧
      epsilon * epsilon = -I2 ∧
      sigma1 * epsilon + epsilon * sigma1 = 0) := by
  exact ⟨displayed_split_signature, displayed_clifford_relations,
    displayed_product_square, cl11_block_shadow⟩

end Cl55FiniteShadowPacket
