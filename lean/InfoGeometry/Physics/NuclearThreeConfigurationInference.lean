/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfigurationTransition

/-!
# Joint energy and transition inference in the real three-configuration model

`a`, `c`, and `g` are model parameters; `a` is also the dark eigenenergy.
`E` is the lower bright eigenenergy. The measured strength is the normalized
operator readout already constructed from the two graph embeddings. A known
nonzero probe calibration `kappa` makes `c` and `g^2` identifiable from `a`,
`E`, and that strength. The sign of `g` remains a basis convention.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationInference

open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationTransition

theorem lower_branch_energy (a c g E : ℝ) (hac : a < c) (hg : g ≠ 0)
    (hwindow : E < (a + c) / 2)
    (heig : hamiltonian a c g (graphMap c g E brightModel) =
      E • graphMap c g E brightModel) :
    E < c ∧ E < a ∧ (a - E) * (c - E) = 2 * g ^ 2 := by
  have hEc : E < c := by linarith only [hac, hwindow]
  have hid := (bright_eigen_equation_iff a c g E (ne_of_lt hEc)).mp heig
  have hg2 : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hEa : E < a := by
    by_contra hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_gt hn)) (le_of_lt (sub_pos.mpr hEc))
    nlinarith
  exact ⟨hEc, hEa, hid⟩

/-- The spectral constraint reduces the derived readout, with no new
observation-law premise. -/
theorem measuredStrength_on_branch (a c g E κ : ℝ)
    (hEc : E < c) (hEa : E < a)
    (hid : (a - E) * (c - E) = 2 * g ^ 2) :
    measuredStrength a c g E κ =
      κ ^ 2 * (c - E) / ((c - E) + (a - E)) := by
  have hD : c - E ≠ 0 := ne_of_gt (sub_pos.mpr hEc)
  have hsum : (c - E) + (a - E) ≠ 0 := by linarith only [hEc, hEa]
  have hfactor : (E - c) ^ 2 + 2 * g ^ 2 =
      (c - E) * ((c - E) + (a - E)) := by
    rw [← hid]
    ring
  rw [measuredStrength_closed_form a c g E κ (ne_of_lt hEc), hfactor]
  field_simp [hD, hsum]
  <;> ring

/-- On the lower branch with `a<c`, the calibrated strength has a strict
admissible interval. In particular the inverse observation map has no pole. -/
theorem measuredStrength_bounds (a c g E κ : ℝ)
    (hac : a < c) (hg : g ≠ 0) (hκ : κ ≠ 0)
    (hwindow : E < (a + c) / 2)
    (heig : hamiltonian a c g (graphMap c g E brightModel) =
      E • graphMap c g E brightModel) :
    κ ^ 2 / 2 < measuredStrength a c g E κ ∧
      measuredStrength a c g E κ < κ ^ 2 := by
  obtain ⟨hEc, hEa, hid⟩ := lower_branch_energy a c g E hac hg hwindow heig
  rw [measuredStrength_on_branch a c g E κ hEc hEa hid]
  have hsum : 0 < (c - E) + (a - E) := by linarith
  have hk2 : 0 < κ ^ 2 := sq_pos_of_ne_zero hκ
  constructor
  · apply (lt_div_iff₀ hsum).mpr
    nlinarith [mul_pos hk2 (sub_pos.mpr hac)]
  · apply (div_lt_iff₀ hsum).mpr
    nlinarith [mul_pos hk2 (sub_pos.mpr hEa)]

/-- Recovery of the omitted diagonal energy and coupling magnitude from
two eigenenergies and the actual normalized transition strength. -/
theorem recover_parameters (a c g E κ : ℝ)
    (hac : a < c) (hg : g ≠ 0) (hκ : κ ≠ 0)
    (hwindow : E < (a + c) / 2)
    (heig : hamiltonian a c g (graphMap c g E brightModel) =
      E • graphMap c g E brightModel) :
    c = E + (a - E) * measuredStrength a c g E κ /
        (κ ^ 2 - measuredStrength a c g E κ) ∧
    g ^ 2 = (a - E) ^ 2 * measuredStrength a c g E κ /
        (2 * (κ ^ 2 - measuredStrength a c g E κ)) := by
  obtain ⟨hEc, hEa, hid⟩ := lower_branch_energy a c g E hac hg hwindow heig
  have hread := measuredStrength_on_branch a c g E κ hEc hEa hid
  have hsum : (c - E) + (a - E) ≠ 0 := by linarith
  have hdelta : a - E ≠ 0 := ne_of_gt (sub_pos.mpr hEa)
  have hk2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  have hpole : κ ^ 2 - measuredStrength a c g E κ ≠ 0 :=
    ne_of_gt (sub_pos.mpr (measuredStrength_bounds a c g E κ
      hac hg hκ hwindow heig).2)
  have hcancel : κ ^ 2 - measuredStrength a c g E κ =
      κ ^ 2 * (a - E) / ((c - E) + (a - E)) := by
    rw [hread]
    field_simp
    <;> ring
  constructor
  · rw [hcancel, hread]
    field_simp [hsum, hdelta, hk2]
    <;> ring
  · rw [hcancel, hread]
    field_simp [hsum, hdelta, hk2]
    nlinarith [hid]

/-- The joint observation map is injective up to the real coupling sign. -/
theorem joint_identifiability (a E κ c₁ c₂ g₁ g₂ : ℝ)
    (ha₁ : a < c₁) (ha₂ : a < c₂) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hκ : κ ≠ 0) (hw₁ : E < (a + c₁) / 2) (hw₂ : E < (a + c₂) / 2)
    (he₁ : hamiltonian a c₁ g₁ (graphMap c₁ g₁ E brightModel) =
      E • graphMap c₁ g₁ E brightModel)
    (he₂ : hamiltonian a c₂ g₂ (graphMap c₂ g₂ E brightModel) =
      E • graphMap c₂ g₂ E brightModel)
    (hB : measuredStrength a c₁ g₁ E κ = measuredStrength a c₂ g₂ E κ) :
    c₁ = c₂ ∧ (g₁ = g₂ ∨ g₁ = -g₂) := by
  obtain ⟨hc₁, hs₁⟩ := recover_parameters a c₁ g₁ E κ ha₁ hg₁ hκ hw₁ he₁
  obtain ⟨hc₂, hs₂⟩ := recover_parameters a c₂ g₂ E κ ha₂ hg₂ hκ hw₂ he₂
  have hc : c₁ = c₂ := by rw [hc₁, hc₂, hB]
  have hs : g₁ ^ 2 = g₂ ^ 2 := by rw [hs₁, hs₂, hB]
  exact ⟨hc, (sq_eq_sq_iff_eq_or_eq_neg).mp hs⟩

end InfoGeometry.Physics.NuclearThreeConfigurationInference
