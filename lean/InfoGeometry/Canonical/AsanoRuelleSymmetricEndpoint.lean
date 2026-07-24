import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Module.Basic
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/-!
# InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint

Symmetric counterpart of the topological endpoint limit argument.
-/

namespace InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint

open Set Filter Topology
open InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/--
Right-pole inclusion from boundedness of `K₁` (symmetric to left-pole theorem).
-/
theorem asano_right_pole_in_K2
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK2_closed : IsClosed K2)
    (hK1_bdd : Bornology.IsBounded K1)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (-B / D) ∈ K2 := by
  by_contra h_notin

  rcases Metric.isBounded_iff_subset_ball 0 |>.mp hK1_bdd with ⟨M, hM_ball⟩
  let p := -B / D

  have hp_nhds : K2ᶜ ∈ 𝓝 p := (isOpen_compl_iff.mpr hK2_closed).mem_nhds h_notin
  have hp_punctured : K2ᶜ ∈ 𝓝[≠] p := nhdsWithin_le_nhds hp_nhds

  have h_ineq : ∀ᶠ z in 𝓝[≠] p, ‖A + C * z‖ ≤ M * ‖B + D * z‖ := by
    filter_upwards [hp_punctured, self_mem_nhdsWithin] with z hz_notin hz_neq
    have h_denom : B + D * z ≠ 0 := by
      intro h_eq
      have hzval : D * z = -B := by
        exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h_eq)
      have : z = p := by
        calc
          z = (D * z) / D := by field_simp [hD]
          _ = -B / D := by rw [hzval]
      exact hz_neq this

    let w := -(A + C * z) / (B + D * z)

    have hw_in : w ∈ K1 := by
      by_contra hw_notin
      have h_root : A + B * w + C * z + D * w * z = 0 := by
        calc
          A + B * w + C * z + D * w * z
              = A + C * z + w * (B + D * z) := by ring
          _ = A + C * z + (-(A + C * z)) := by rw [div_mul_cancel₀ _ h_denom]
          _ = 0 := by ring
      exact h_zerofree w z hw_notin hz_notin h_root

    have hw_bdd : ‖w‖ ≤ M := by
      have hw_dist_lt : dist w 0 < M := hM_ball hw_in
      have hw_dist : dist w 0 ≤ M := le_of_lt hw_dist_lt
      rwa [dist_zero_right] at hw_dist

    have h_num : ‖A + C * z‖ = ‖w‖ * ‖B + D * z‖ := by
      have h1 : w * (B + D * z) = -(A + C * z) :=
        div_mul_cancel₀ (-(A + C * z)) h_denom
      have h2 : ‖w * (B + D * z)‖ = ‖-(A + C * z)‖ := congrArg norm h1
      rw [norm_mul, norm_neg] at h2
      exact h2.symm

    rw [h_num]
    exact mul_le_mul_of_nonneg_right hw_bdd (norm_nonneg _)

  have t_LHS : Tendsto (fun z => ‖A + C * z‖) (𝓝[≠] p) (𝓝 ‖A + C * p‖) :=
    Tendsto.mono_left ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).norm)
      nhdsWithin_le_nhds

  have t_RHS : Tendsto (fun z => M * ‖B + D * z‖) (𝓝[≠] p) (𝓝 (M * ‖B + D * p‖)) :=
    Tendsto.mono_left (tendsto_const_nhds.mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).norm) nhdsWithin_le_nhds

  have h_le : ‖A + C * p‖ ≤ M * ‖B + D * p‖ := le_of_tendsto_of_tendsto t_LHS t_RHS h_ineq

  have hp_eval : B + D * p = 0 := by
    calc
      B + D * (-B / D) = B - (B / D) * D := by ring
      _ = B - B := by rw [div_mul_cancel₀ B hD]
      _ = 0 := by ring

  rw [hp_eval, norm_zero, mul_zero] at h_le

  have h_num_zero : A + C * p = 0 := norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _))

  have h_det : (A + C * p) * D = A * D - B * C := by
    calc
      (A + C * (-B / D)) * D = A * D - C * ((B / D) * D) := by ring
      _ = A * D - C * B := by rw [div_mul_cancel₀ B hD]
      _ = A * D - B * C := by ring

  rw [h_num_zero, zero_mul] at h_det
  exact hNondeg h_det.symm

/--
If `-B/D ∈ K₂` and `0 ∉ K₂`, then `B ≠ 0`.
-/
theorem right_pole_nonzero
    (B D : ℂ) (K2 : Set ℂ)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_in : (-B / D) ∈ K2) :
    B ≠ 0 := by
  intro hB
  rw [hB, neg_zero, zero_div] at h_in
  exact hK2_no_zero h_in

/--
Combined endpoint disjunction:
if `K₁`, `K₂` are closed and at least one is bounded, then the nondegenerate
endpoint disjunction holds.
-/
theorem asano_endpoint_disjunction_combined
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_closed : IsClosed K2)
    (h_bdd_or : Bornology.IsBounded K1 ∨ Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (C ≠ 0 ∧ (-C / D) ∈ K1) ∨ (B ≠ 0 ∧ (-B / D) ∈ K2) := by
  rcases h_bdd_or with hK1_bdd | hK2_bdd
  · have h_in := asano_right_pole_in_K2 A B C D K1 K2 hD hNondeg hK2_closed hK1_bdd h_zerofree
    exact Or.inr ⟨right_pole_nonzero B D K2 hK2_no_zero h_in, h_in⟩
  · exact asano_endpoint_disjunction_left
      A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd hK1_no_zero h_zerofree

end InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint
