import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.AsanoRuelleEndpoint
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/-!
# InfoGeometry.Canonical.AsanoRuelleNondegenerateBridge

Bridge from endpoint/topological disjunction to product-set membership for the
nondegenerate contracted root.
-/

namespace InfoGeometry.Canonical.AsanoRuelle

open Set InfoGeometry.Canonical.AsanoRuelleEndpoint
open InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/--
If `0 ∉ K₂`, the zero-free property evaluated at `z₂ = 0` forces
`-A/B ∈ K₁`.
-/
theorem asano_zero_slice_left
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hB : B ≠ 0)
    (h0_notin_K2 : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (-A / B) ∈ K1 := by
  by_contra h_notin
  have h_eval := h_zerofree (-A / B) 0 h_notin h0_notin_K2
  have h_zero : A + B * (-A / B) + C * 0 + D * (-A / B) * 0 = 0 := by
    calc A + B * (-A / B) + C * 0 + D * (-A / B) * 0
       = A + B * (-A / B) := by ring
     _ = A + (-A / B) * B := by ring
     _ = A + -A := by rw [div_mul_cancel₀ (-A) hB]
     _ = 0 := by ring
  exact h_eval h_zero

/--
If `0 ∉ K₁`, the zero-free property evaluated at `z₁ = 0` forces
`-A/C ∈ K₂`.
-/
theorem asano_zero_slice_right
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hC : C ≠ 0)
    (h0_notin_K1 : (0 : ℂ) ∉ K1)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (-A / C) ∈ K2 := by
  by_contra h_notin
  have h_eval := h_zerofree 0 (-A / C) h0_notin_K1 h_notin
  have h_zero : A + B * 0 + C * (-A / C) + D * 0 * (-A / C) = 0 := by
    calc A + B * 0 + C * (-A / C) + D * 0 * (-A / C)
       = A + C * (-A / C) := by ring
     _ = A + (-A / C) * C := by ring
     _ = A + -A := by rw [div_mul_cancel₀ (-A) hC]
     _ = 0 := by ring
  exact h_eval h_zero

/--
Nondegenerate bridge: from endpoint disjunction plus zero-slice roots to
product-set membership for the contracted root.
-/
theorem asano_nondegenerate_bridge
    (A B C D z : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0)
    (hz : A + D * z = 0) :
    z ∈ negProductSet K1 K2 := by
  have hDz : D * z = -A := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hz)
  have hz_eq : z = -A / D := by
    calc
      z = (z * D) / D := (mul_div_cancel_right₀ z hD).symm
      _ = (D * z) / D := by rw [mul_comm]
      _ = -A / D := by rw [hDz]

  have h_disj :=
    asano_endpoint_disjunction_left A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd hK1_no_zero h_zerofree

  rcases h_disj with ⟨hC, hC_in⟩ | ⟨hB, hB_in⟩
  · have hA_in := asano_zero_slice_right A B C D K1 K2 hC hK1_no_zero h_zerofree
    have hz_prod : (-A / D) = - ((-C / D) * (-A / C)) := by
      field_simp [hC, hD]
    have h_prod : (-A / D) ∈ negProductSet K1 K2 :=
      contracted_root_mem_negProductSet_of_endpoint K1 K2 hC_in hA_in hz_prod
    simpa [hz_eq] using h_prod
  · have hA_in := asano_zero_slice_left A B C D K1 K2 hB hK2_no_zero h_zerofree
    have hz_prod : (-A / D) = - ((-A / B) * (-B / D)) := by
      field_simp [hB, hD]
    have h_prod : (-A / D) ∈ negProductSet K1 K2 :=
      contracted_root_mem_negProductSet_of_endpoint K1 K2 hA_in hB_in hz_prod
    simpa [hz_eq] using h_prod

end InfoGeometry.Canonical.AsanoRuelle
