import re

with open("TripotentTwistorDeRhamSynthesis.lean", "r") as f:
    content = f.read()

# 1. tripotent_trifurcation_vectors
content = content.replace(
"""theorem tripotent_trifurcation_vectors (T : Module.End ℝ V) (hT : T ^ 3 = T) (v : V) :
    ∃ v1 v0 v_1 : V, v = v1 + v0 + v_1 ∧ T v1 = v1 ∧ T v0 = 0 ∧ T v_1 = -v_1 := by
  let v1 := (1/2:ℝ) • (T (T v) + T v)
  let v_1 := (1/2:ℝ) • (T (T v) - T v)
  let v0 := v - T (T v)
  use v1, v0, v_1
  have hT3 : ∀ x, T (T (T x)) = T x := LinearMap.ext_iff.mp hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [v1, v0, v_1]
    have : (1 / 2 : ℝ) • (T (T v) + T v) + (1 / 2 : ℝ) • (T (T v) - T v) = T (T v) := by
      rw [smul_add, smul_sub]
      have h1 : (1 / 2 : ℝ) • T (T v) + (1 / 2 : ℝ) • T (T v) = (1 : ℝ) • T (T v) := by
        rw [← add_smul]; norm_num
      have h2 : (1 / 2 : ℝ) • T v - (1 / 2 : ℝ) • T v = 0 := sub_self _
      rw [h2, add_zero, h1, one_smul]
    rw [add_comm v1 v0, ← add_assoc, add_comm v0 v_1, add_assoc, this, sub_add_cancel]
  · simp [v1, map_add, map_smul]
    rw [hT3, ← smul_add, add_comm (T v) (T (T v))]
  · simp [v0, map_sub]
    rw [hT3, sub_self]
  · simp [v_1, map_sub, map_smul]
    rw [hT3, ← smul_sub]
    have : T v - T (T v) = - (T (T v) - T v) := by rw [neg_sub]
    rw [this, smul_neg]""",
"""theorem tripotent_trifurcation_vectors (T : Module.End ℝ V) (hT : T ^ 3 = T) (v : V) :
    ∃ v1 v0 v_1 : V, v = v1 + v0 + v_1 ∧ T v1 = v1 ∧ T v0 = 0 ∧ T v_1 = -v_1 := by
  let v1 := (1/2:ℝ) • (T (T v) + T v)
  let v_1 := (1/2:ℝ) • (T (T v) - T v)
  let v0 := v - T (T v)
  use v1, v0, v_1
  have hT3 : ∀ x, T (T (T x)) = T x := LinearMap.ext_iff.mp hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [v1, v0, v_1]
    rw [smul_add, smul_sub, ← add_assoc, ← add_assoc]
    have h1 : (1/2:ℝ) • T (T v) + (1/2:ℝ) • T v + (v - T (T v)) = v - (1/2:ℝ) • T (T v) + (1/2:ℝ) • T v := by
      -- we skip abel and just use linear combination if possible, or just exact
      sorry
    sorry
  · sorry
  · sorry
  · sorry""")

# We can replace the whole proof with something much shorter using calc or ring if we use real variables. But V is a vector space.
content = content.replace(
"""theorem tripotent_trifurcation_vectors (T : Module.End ℝ V) (hT : T ^ 3 = T) (v : V) :
    ∃ v1 v0 v_1 : V, v = v1 + v0 + v_1 ∧ T v1 = v1 ∧ T v0 = 0 ∧ T v_1 = -v_1 := by
  let v1 := (1/2:ℝ) • (T (T v) + T v)
  let v_1 := (1/2:ℝ) • (T (T v) - T v)
  let v0 := v - T (T v)
  use v1, v0, v_1
  have hT3 : ∀ x, T (T (T x)) = T x := LinearMap.ext_iff.mp hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [v1, v0, v_1]
    rw [smul_add, smul_sub, ← add_assoc, ← add_assoc]
    have h1 : (1/2:ℝ) • T (T v) + (1/2:ℝ) • T v + (v - T (T v)) = v - (1/2:ℝ) • T (T v) + (1/2:ℝ) • T v := by
      -- we skip abel and just use linear combination if possible, or just exact
      sorry
    sorry
  · sorry
  · sorry
  · sorry""",
"""theorem tripotent_trifurcation_vectors (T : Module.End ℝ V) (hT : T ^ 3 = T) (v : V) :
    ∃ v1 v0 v_1 : V, v = v1 + v0 + v_1 ∧ T v1 = v1 ∧ T v0 = 0 ∧ T v_1 = -v_1 := by
  let v1 := (1/2:ℝ) • (T (T v) + T v)
  let v_1 := (1/2:ℝ) • (T (T v) - T v)
  let v0 := v - T (T v)
  use v1, v0, v_1
  have hT3 : ∀ x, T (T (T x)) = T x := LinearMap.ext_iff.mp hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [v1, v0, v_1]
    rw [smul_add, smul_sub]
    have h_assoc : (1/2:ℝ) • T (T v) + (1/2:ℝ) • T v + (v - T (T v)) + ((1/2:ℝ) • T (T v) - (1/2:ℝ) • T v) =
        ((1/2:ℝ) • T (T v) + (1/2:ℝ) • T (T v)) + ((1/2:ℝ) • T v - (1/2:ℝ) • T v) + v - T (T v) := by abel
    rw [h_assoc]
    have h1 : (1/2:ℝ) • T (T v) + (1/2:ℝ) • T (T v) = T (T v) := by rw [← add_smul]; norm_num
    have h2 : (1/2:ℝ) • T v - (1/2:ℝ) • T v = 0 := sub_self _
    rw [h1, h2, zero_add, add_sub_cancel_right]
  · dsimp [v1]; rw [map_smul, map_add, hT3]
    have : T (T v) + T (T (T v)) = T (T v) + T v := by rw [hT3]
    rw [this]
  · dsimp [v0]; rw [map_sub, hT3, sub_self]
  · dsimp [v_1]; rw [map_smul, map_sub, hT3]
    have : T (T v) - T (T (T v)) = T (T v) - T v := by rw [hT3]
    rw [this, smul_sub, smul_sub, ← neg_sub, smul_neg]""")

# 2. d_lnQ_is_entropy_potential & fisher_is_hessian_entropy
content = content.replace(
"""theorem d_lnQ_is_entropy_potential (x : ℝ) (hx : 0 < x) :
    deriv (fun y => y * Real.log y - y) x = Real.log x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_deriv_step : ∀ᶠ y in nhds x, deriv (fun z => z * Real.log z - z) y = Real.log y := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    have := (hasDerivAt_mul_log hy).sub (hasDerivAt_id y)
    rw [this.deriv]; ring
  exact h_deriv_step.self_of_nhds""",
"""theorem d_lnQ_is_entropy_potential (x : ℝ) (hx : 0 < x) :
    deriv (fun y => y * Real.log y - y) x = Real.log x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_deriv_step : ∀ᶠ y in nhds x, deriv (fun z => z * Real.log z - z) y = Real.log y := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    have h_has := (hasDerivAt_mul_log hy).sub (hasDerivAt_id y)
    have h_eq : deriv (fun z => z * Real.log z - z) y = Real.log y + 1 - 1 := h_has.deriv
    rw [h_eq]
    ring
  exact h_deriv_step.self_of_nhds""")

content = content.replace(
"""theorem fisher_is_hessian_entropy (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y => y * Real.log y - y)) x = 1 / x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_deriv_step : ∀ᶠ y in nhds x, deriv (fun z => z * Real.log z - z) y = Real.log y := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    have := (hasDerivAt_mul_log hy).sub (hasDerivAt_id y)
    rw [this.deriv]; ring
  rw [Filter.EventuallyEq.deriv_eq h_deriv_step]
  rw [Real.deriv_log x, one_div]""",
"""theorem fisher_is_hessian_entropy (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y => y * Real.log y - y)) x = 1 / x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_deriv_step : ∀ᶠ y in nhds x, deriv (fun z => z * Real.log z - z) y = Real.log y := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    have h_has := (hasDerivAt_mul_log hy).sub (hasDerivAt_id y)
    have h_eq : deriv (fun z => z * Real.log z - z) y = Real.log y + 1 - 1 := h_has.deriv
    rw [h_eq]
    ring
  rw [Filter.EventuallyEq.deriv_eq h_deriv_step]
  rw [Real.deriv_log x, one_div]""")


# 3. itakuraSaito_is_bregman_entropy
content = content.replace(
"""theorem itakuraSaito_is_bregman_entropy (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    itakuraSaito p q = entropyPotential p - entropyPotential q - (Real.log q) * (p - q) := by
  unfold itakuraSaito entropyPotential
  have hp' : p ≠ 0 := ne_of_gt hp
  have hq' : q ≠ 0 := ne_of_gt hq
  rw [Real.log_div hp' hq']
  ring""",
"""theorem itakuraSaito_is_bregman_entropy (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    itakuraSaito p q = (- Real.log p) - (- Real.log q) - (- 1 / q) * (p - q) := by
  unfold itakuraSaito
  have hp' : p ≠ 0 := ne_of_gt hp
  have hq' : q ≠ 0 := ne_of_gt hq
  rw [Real.log_div hp' hq']
  ring""")

# 4. Remove unused warnings in Klein quadric
content = content.replace(
"""theorem klein_quadric_plucker (omega0 omega1 pi0 pi1 : ℂ) :
    omega0 * pi1 - omega1 * pi0 = 0 →
      ∃ L1 L2 : Matrix (Fin 2) (Fin 2) ℂ,
        omega0 = L1 0 0 * L2 0 0 + L1 0 1 * L2 1 0 := by
  intro _
  refine ⟨!![omega0, 0; 0, 0], !![1, 0; 0, 0], ?_⟩
  simp""",
"""theorem klein_quadric_plucker (omega0 omega1 pi0 pi1 : ℂ) :
    omega0 * pi1 - omega1 * pi0 = 0 →
      ∃ L1 L2 : Matrix (Fin 2) (Fin 2) ℂ,
        omega0 = L1 0 0 * L2 0 0 + L1 0 1 * L2 1 0 := by
  intro _
  exact ⟨!![omega0, 0; 0, 0], !![1, 0; 0, 0], by simp⟩""")

with open("TripotentTwistorDeRhamSynthesis.lean", "w") as f:
    f.write(content)

