import Mathlib.Data.Complex.Basic
import InfoGeometry.Canonical.AsanoRuelleEndpoint
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint
import InfoGeometry.Canonical.AsanoRuelleNondegenerateBridge
import InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint

/-!
# InfoGeometry.Canonical.AsanoRuelleNondegenerateClosure

Final nondegenerate closure layer for Asano-Ruelle contraction.

This file exposes the closure theorem under a stable canonical name by
reusing the already proved bridge theorem.
-/

namespace InfoGeometry.Canonical.AsanoRuelle

open Set
open InfoGeometry.Canonical.AsanoRuelleEndpoint
open InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint
open InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint

/--
Nondegenerate Asano-Ruelle closure with bounded `K₂`.

This is the direct closure theorem:
if `A + D*z = 0` under the nondegenerate/zero-free hypotheses, then
`z ∈ -(K₁K₂)`.
-/
theorem asano_nondegenerate_closure_left_bdd
    (A B C D z : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0)
    (hz : A + D * z = 0) :
    z ∈ negProductSet K1 K2 :=
  asano_nondegenerate_bridge
    A B C D z K1 K2
    hD hNondeg hK1_closed hK2_bdd hK1_no_zero hK2_no_zero h_zerofree hz

/--
Nondegenerate Asano-Ruelle closure with combined boundedness:
`Bornology.IsBounded K₁ ∨ Bornology.IsBounded K₂`.
-/
theorem asano_nondegenerate_closure_bdd_or
    (A B C D z : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_closed : IsClosed K2)
    (h_bdd_or : Bornology.IsBounded K1 ∨ Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0)
    (hz : A + D * z = 0) :
    z ∈ negProductSet K1 K2 := by
  rcases h_bdd_or with hK1_bdd | hK2_bdd
  · have h_disj :
      (C ≠ 0 ∧ (-C / D) ∈ K1) ∨ (B ≠ 0 ∧ (-B / D) ∈ K2) :=
      asano_endpoint_disjunction_combined
        A B C D K1 K2 hD hNondeg hK1_closed hK2_closed
        (Or.inl hK1_bdd) hK1_no_zero hK2_no_zero h_zerofree
    have hDz : D * z = -A := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hz)
    have hz_eq : z = -A / D := by
      calc
        z = (z * D) / D := (mul_div_cancel_right₀ z hD).symm
        _ = (D * z) / D := by rw [mul_comm]
        _ = -A / D := by rw [hDz]
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
  · exact
      asano_nondegenerate_closure_left_bdd
        A B C D z K1 K2 hD hNondeg hK1_closed hK2_bdd
        hK1_no_zero hK2_no_zero h_zerofree hz

/--
Contrapositive nondegenerate closure (bounded `K₂`):
if `z ∉ -(K₁K₂)` then `A + D*z ≠ 0`.
-/
theorem asano_nondegenerate_not_root_of_not_mem_negProductSet_left_bdd
    (A B C D z : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0)
    (hz_not : z ∉ negProductSet K1 K2) :
    A + D * z ≠ 0 := by
  intro hz
  exact hz_not <|
    asano_nondegenerate_closure_left_bdd
      A B C D z K1 K2 hD hNondeg hK1_closed hK2_bdd
      hK1_no_zero hK2_no_zero h_zerofree hz

/--
Contrapositive nondegenerate closure (combined boundedness):
if `z ∉ -(K₁K₂)` then `A + D*z ≠ 0`.
-/
theorem asano_nondegenerate_not_root_of_not_mem_negProductSet_bdd_or
    (A B C D z : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_closed : IsClosed K2)
    (h_bdd_or : Bornology.IsBounded K1 ∨ Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0)
    (hz_not : z ∉ negProductSet K1 K2) :
    A + D * z ≠ 0 := by
  intro hz
  exact hz_not <|
    asano_nondegenerate_closure_bdd_or
      A B C D z K1 K2 hD hNondeg hK1_closed hK2_closed h_bdd_or
      hK1_no_zero hK2_no_zero h_zerofree hz

end InfoGeometry.Canonical.AsanoRuelle
