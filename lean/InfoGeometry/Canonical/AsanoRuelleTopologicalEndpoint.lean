import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Module.Basic

/-!
# InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

Mathematical Proof:
This file executes the formal topological limit for the Asano-Ruelle
contraction (nondegenerate branch).

It proves that the algebraic metric inequality bounding the roots, when
evaluated at the non-degenerate pole over a punctured neighborhood filter,
forces the pole directly into the forbidden set `K₁`.

This establishes the exact endpoint disjunction required by Ruelle A.1,
ready to feed into the algebraic product lemmas.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

open Set Filter Topology

/--
Topological Pole Inclusion (The Limit Contradiction).

If `K₂` is bounded, the root `w = -(A+Bz)/(C+Dz)` cannot escape to infinity.
Evaluating this bound over the punctured neighborhood of the pole `-C/D`
forces the numerator to vanish, contradicting non-degeneracy.
Therefore, the pole must lie inside the closed set `K₁`.
-/
theorem asano_left_pole_in_K1
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (-C / D) ∈ K1 := by
  by_contra h_notin

  -- 1. K2 is bounded, so it is contained in a closed ball of radius M around 0.
  rcases Metric.isBounded_iff_subset_ball 0 |>.mp hK2_bdd with ⟨M, hM_ball⟩

  let p := -C / D

  -- 2. Construct the punctured neighborhood filter around the pole.
  have hp_nhds : K1ᶜ ∈ 𝓝 p := (isOpen_compl_iff.mpr hK1_closed).mem_nhds h_notin
  have hp_punctured : K1ᶜ ∈ 𝓝[≠] p := nhdsWithin_le_nhds hp_nhds

  -- 3. Establish the metric root bound eventually around the pole.
  have h_ineq : ∀ᶠ z in 𝓝[≠] p, ‖A + B * z‖ ≤ M * ‖C + D * z‖ := by
    filter_upwards [hp_punctured, self_mem_nhdsWithin] with z hz_notin hz_neq

    -- z is not the pole, so the denominator is non-zero.
    have h_denom : C + D * z ≠ 0 := by
      intro h_eq
      have hDz : D * z = -C := by
        exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h_eq)
      have hzdiv : (D * z) / D = z := by field_simp [hD]
      have hzpole : z = p := by
        calc
          z = (D * z) / D := hzdiv.symm
          _ = -C / D := by rw [hDz]
      exact hz_neq hzpole

    let w := -(A + B * z) / (C + D * z)

    -- The root map `w` must lie in K2, otherwise it violates zero-freeness.
    have hw_in : w ∈ K2 := by
      by_contra hw_notin
      have h_root : A + B * z + C * w + D * z * w = 0 := by
        calc A + B * z + C * w + D * z * w
           = A + B * z + w * (C + D * z) := by ring
         _ = A + B * z + (-(A + B * z)) := by rw [div_mul_cancel₀ _ h_denom]
         _ = 0 := by ring
      exact h_zerofree z w hz_notin hw_notin h_root

    -- Since w ∈ K2, its norm is bounded by M.
    have hw_bdd : ‖w‖ ≤ M := by
      have hw_dist_lt : dist w 0 < M := hM_ball hw_in
      have hw_dist : dist w 0 ≤ M := le_of_lt hw_dist_lt
      rw [dist_zero_right] at hw_dist
      exact hw_dist

    -- Algebraic factorization linking the norms.
    have h_num : ‖A + B * z‖ = ‖w‖ * ‖C + D * z‖ := by
      have h1 : w * (C + D * z) = -(A + B * z) := by
        exact div_mul_cancel₀ (-(A + B * z)) h_denom
      have h2 : ‖w * (C + D * z)‖ = ‖-(A + B * z)‖ := congrArg norm h1
      rw [norm_mul, norm_neg] at h2
      exact h2.symm

    rw [h_num]
    exact mul_le_mul_of_nonneg_right hw_bdd (norm_nonneg _)

  -- 4. Evaluate the continuous limits at the pole `p`.
  have t_LHS : Tendsto (fun z => ‖A + B * z‖) (𝓝[≠] p) (𝓝 ‖A + B * p‖) :=
    Tendsto.mono_left ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).norm) nhdsWithin_le_nhds

  have t_RHS : Tendsto (fun z => M * ‖C + D * z‖) (𝓝[≠] p) (𝓝 (M * ‖C + D * p‖)) :=
    Tendsto.mono_left (tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).norm) nhdsWithin_le_nhds

  have h_le : ‖A + B * p‖ ≤ M * ‖C + D * p‖ := le_of_tendsto_of_tendsto t_LHS t_RHS h_ineq

  -- 5. Force the contradiction.
  have hp_eval : C + D * p = 0 := by
    calc C + D * (-C / D) = C - (C / D) * D := by ring
         _ = C - C := by rw [div_mul_cancel₀ C hD]
         _ = 0 := by ring

  rw [hp_eval, norm_zero, mul_zero] at h_le

  have h_num_zero : A + B * p = 0 := norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _))

  have h_det : (A + B * p) * D = A * D - B * C := by
    calc (A + B * (-C / D)) * D = A * D - B * ((C / D) * D) := by ring
         _ = A * D - B * C := by rw [div_mul_cancel₀ C hD]

  rw [h_num_zero, zero_mul] at h_det
  exact hNondeg h_det.symm

/--
Trivial lemma isolating the origin avoidance requirement.
If `-C/D ∈ K1` but `0 ∉ K1`, then `C ≠ 0`.
-/
theorem left_pole_nonzero
    (C D : ℂ) (K1 : Set ℂ)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (h_in : (-C / D) ∈ K1) :
    C ≠ 0 := by
  intro hC
  rw [hC, neg_zero, zero_div] at h_in
  exact hK1_no_zero h_in

/--
The Nondegenerate Endpoint Disjunction (Left Branch).

Derived purely from closed/bounded and zero-free hypotheses.
This perfectly matches the Ruelle A.1 endpoint statement, ready to be
fed into `contracted_root_mem_negProductSet_of_endpoint_root`.
-/
theorem asano_endpoint_disjunction_left
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (C ≠ 0 ∧ (-C / D) ∈ K1) ∨ (B ≠ 0 ∧ (-B / D) ∈ K2) := by
  have h_in := asano_left_pole_in_K1 A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd h_zerofree
  exact Or.inl ⟨left_pole_nonzero C D K1 hK1_no_zero h_in, h_in⟩

end InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint
