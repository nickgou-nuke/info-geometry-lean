import Mathlib.Tactic
import InfoGeometry.Analysis.AsanoMobiusPole
import InfoGeometry.Canonical.LeeYangAsanoScaleBlowupBridge

/-!
# Explicit bounded escape for the scaled Asano root

This owner complements the filter-based pole argument with a concrete positive
real scale.  It proves only the finite bounded-set consequence of the
inverse-scale formula; no limit, compactification, Weyl metric, or colimit is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoScaleBoundedEscapeBridge

open Set
open InfoGeometry.Canonical.LeeYangAsanoNativeCore
open InfoGeometry.Canonical.LeeYangAsanoScaleBlowupBridge
open InfoGeometry.Analysis.AsanoMobiusPole

/-! ## A supplied norm threshold gives an explicit escape witness -/

theorem asanoRootMap_poleScale_not_mem_of_norm_bound
    {A B C D v : ℂ} {K : Set ℂ} {M lam : ℝ}
    (hD : D ≠ 0) (hv : v ≠ 0) (hlam : 0 < lam)
    (hK : ∀ z ∈ K, ‖z‖ < M)
    (hscale : M + ‖B / D‖ <
      ‖-(A * D - B * C) / (D ^ 2 * v)‖ / lam) :
    asanoRootMap A B C D (poleScalePoint C D lam v) ∉ K := by
  intro hmem
  have hnorm :
      ‖asanoRootMap A B C D (poleScalePoint C D lam v)‖ < M :=
    hK _ hmem
  have hroot := asanoRootMap_poleScale_eq_inverseScale
    (A := A) (B := B) (C := C) (D := D) (v := v)
    hD hv (ne_of_gt hlam)
  rw [hroot] at hnorm
  have hreverse := norm_sub_norm_le
    (-(A * D - B * C) / (D ^ 2 * v) / (lam : ℂ)) (B / D)
  have hscale_norm :
      ‖-(A * D - B * C) / (D ^ 2 * v) / (lam : ℂ)‖ =
        ‖-(A * D - B * C) / (D ^ 2 * v)‖ / lam := by
    rw [norm_div]
    simp [abs_of_pos hlam]
  have hscale' : M <
      ‖-(A * D - B * C) / (D ^ 2 * v) / (lam : ℂ)‖ - ‖B / D‖ := by
    rw [hscale_norm]
    linarith
  have hnorm_lower : M <
      ‖-(A * D - B * C) / (D ^ 2 * v) / (lam : ℂ) - B / D‖ :=
    lt_of_lt_of_le hscale' hreverse
  exact (not_lt_of_ge (le_of_lt hnorm_lower)) hnorm

/-! ## Bounded sets admit a positive scale escape witness -/

theorem exists_positive_poleScalePoint_root_not_mem
    {A B C D v : ℂ} {K : Set ℂ}
    (hD : D ≠ 0) (hv : v ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK_bdd : Bornology.IsBounded K) :
    ∃ lam : ℝ, 0 < lam ∧
      asanoRootMap A B C D (poleScalePoint C D lam v) ∉ K := by
  by_cases hK_empty : K.Nonempty
  · rcases Metric.isBounded_iff_subset_ball 0 |>.mp hK_bdd with ⟨M, hKM⟩
    obtain ⟨z₀, hz₀⟩ := hK_empty
    have hz₀_bound : ‖z₀‖ < M := by
      simpa [Metric.mem_ball, dist_zero_right] using hKM hz₀
    have hM : 0 < M := lt_of_le_of_lt (norm_nonneg z₀) hz₀_bound
    let a : ℝ := ‖-(A * D - B * C) / (D ^ 2 * v)‖
    let q : ℝ := M + ‖B / D‖ + 1
    have ha : 0 < a := by
      dsimp [a]
      exact norm_pos_iff.mpr
        (asanoRootMap_poleScale_coefficient_ne_zero hD hv hNondeg)
    have hq : 0 < q := by
      dsimp [q]
      positivity
    let lam : ℝ := a / q / 2
    have hlam : 0 < lam := by
      dsimp [lam]
      positivity
    refine ⟨lam, hlam, ?_⟩
    apply asanoRootMap_poleScale_not_mem_of_norm_bound
      (K := K) (M := M) hD hv hlam
    · intro z hz
      simpa [Metric.mem_ball, dist_zero_right] using hKM hz
    · have hscale : M + ‖B / D‖ < a / lam := by
        dsimp [lam]
        field_simp [ne_of_gt ha, ne_of_gt hq]
        nlinarith
      simpa [a] using hscale
  · exact ⟨1, one_pos, by simp [Set.not_nonempty_iff_eq_empty.mp hK_empty]⟩

/-! ## Escape below a prescribed source radius -/

theorem exists_positive_lt_poleScalePoint_root_not_mem
    {A B C D v : ℂ} {K : Set ℂ} {δ : ℝ}
    (hD : D ≠ 0) (hv : v ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK_bdd : Bornology.IsBounded K) (hδ : 0 < δ) :
    ∃ lam : ℝ, 0 < lam ∧ lam < δ ∧
      asanoRootMap A B C D (poleScalePoint C D lam v) ∉ K := by
  rcases Metric.isBounded_iff_subset_ball 0 |>.mp hK_bdd with ⟨M, hKM⟩
  by_cases hK_empty : K.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hK_empty
    have hz₀_bound : ‖z₀‖ < M := by
      simpa [Metric.mem_ball, dist_zero_right] using hKM hz₀
    have hM : 0 < M := lt_of_le_of_lt (norm_nonneg z₀) hz₀_bound
    let a : ℝ := ‖-(A * D - B * C) / (D ^ 2 * v)‖
    let q : ℝ := M + ‖B / D‖ + 1
    let den : ℝ := q + a / δ + 1
    let lam : ℝ := a / den
    have ha : 0 < a := by
      dsimp [a]
      exact norm_pos_iff.mpr
        (asanoRootMap_poleScale_coefficient_ne_zero hD hv hNondeg)
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hden : 0 < den := by
      dsimp [den]
      positivity
    have hlam : 0 < lam := by
      dsimp [lam]
      positivity
    have hlam_eq : a / lam = den := by
      dsimp [lam]
      field_simp [ne_of_gt ha, ne_of_gt hden]
    have hδdiv : δ * (a / δ) = a := by
      field_simp [ne_of_gt hδ]
    have hlamδ : lam < δ := by
      dsimp [lam]
      field_simp [ne_of_gt hden]
      dsimp [den]
      nlinarith
    refine ⟨lam, hlam, hlamδ, ?_⟩
    apply asanoRootMap_poleScale_not_mem_of_norm_bound
      (K := K) (M := M) hD hv hlam
    · intro z hz
      simpa [Metric.mem_ball, dist_zero_right] using hKM hz
    · rw [show ‖-(A * D - B * C) / (D ^ 2 * v)‖ = a by rfl]
      rw [hlam_eq]
      dsimp [den, q]
      nlinarith
  · exact ⟨δ / 2, half_pos hδ, by linarith,
      by simp [Set.not_nonempty_iff_eq_empty.mp hK_empty]⟩

/-! ## Explicit bounded-set proof of the left pole endpoint -/

theorem asano_left_pole_in_K1_of_explicit_scale
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 →
      A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (-C / D) ∈ K1 := by
  by_contra h_notin
  have h_notin' : -(C / D) ∉ K1 := by
    convert h_notin using 1 <;> ring
  have hp_nhds : K1ᶜ ∈ nhds (-(C / D)) :=
    (isOpen_compl_iff.mpr hK1_closed).mem_nhds
      (by simpa only [mem_compl_iff] using h_notin')
  rcases Metric.mem_nhds_iff.mp hp_nhds with ⟨δ, hδ, hδK⟩
  obtain ⟨lam, hlam, hlamδ, hroot_not⟩ :=
    exists_positive_lt_poleScalePoint_root_not_mem
      (A := A) (B := B) (C := C) (D := D) (v := (1 : ℂ))
      (K := K2) hD one_ne_zero hNondeg hK2_bdd hδ
  have hz_ball :
      poleScalePoint C D lam (1 : ℂ) ∈
        Metric.ball (-(C / D)) δ := by
    rw [Metric.mem_ball]
    simpa [poleScalePoint, dist_eq_norm, abs_of_pos hlam] using hlamδ
  have hz_not : poleScalePoint C D lam (1 : ℂ) ∉ K1 :=
    hδK hz_ball
  have hden : C + D * poleScalePoint C D lam (1 : ℂ) ≠ 0 := by
    exact denominator_ne_zero_off_pole hD
      (poleScalePoint_ne_pole one_ne_zero (ne_of_gt hlam))
  have hzero :
      asanoPhi A B C D (poleScalePoint C D lam (1 : ℂ))
        (asanoRootMap A B C D (poleScalePoint C D lam (1 : ℂ))) = 0 := by
    simpa [asanoPhi] using
      (asanoPhi_rootMap_zero (A := A) (B := B) (C := C) (D := D)
        (z1 := poleScalePoint C D lam (1 : ℂ)) hden)
  have hroot_mem :
      asanoRootMap A B C D (poleScalePoint C D lam (1 : ℂ)) ∈ K2 := by
    by_contra hroot_not'
    exact (h_zerofree
      (poleScalePoint C D lam (1 : ℂ))
      (asanoRootMap A B C D (poleScalePoint C D lam (1 : ℂ)))
      hz_not hroot_not') hzero
  exact hroot_not hroot_mem

end InfoGeometry.Canonical.LeeYangAsanoScaleBoundedEscapeBridge
