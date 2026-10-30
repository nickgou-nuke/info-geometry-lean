/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local Lean 4.34.1 port of the generic group-theoretic lemmas at the start of
`CFSG.LieType.Simplicity.TitsSimple`. These are used by the external Tits
group normal-subgroup argument and do not depend on a scalar or matrix model.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.QuasisimpleTransport
public import Mathlib.GroupTheory.Sylow

public section

namespace InfoGeometry.Exceptional.CFSGPort.Simplicity

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_commutator_top_of_sup_zpowers
    {D : Subgroup G} [hD : D.Normal] {g : G}
    (h : D ⊔ Subgroup.zpowers g = ⊤) :
    commutator G ≤ ⁅D, ⊤⁆ := by
  set N := ⁅D, (⊤ : Subgroup G)⁆
  have hN : N.Normal := Subgroup.commutator_normal D ⊤
  have hcen : ∀ d ∈ D, ∀ w : G,
      Commute (QuotientGroup.mk' N d) (QuotientGroup.mk' N w) := by
    intro d hd w
    have hc : ⁅d, w⁆ ∈ N :=
      Subgroup.commutator_mem_commutator hd (Subgroup.mem_top w)
    have h1 : QuotientGroup.mk' N ⁅d, w⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hdec : ∀ x : G, ∃ d ∈ D, ∃ k : ℤ, x = d * g ^ k := by
    intro x
    have hx : x ∈ D ⊔ Subgroup.zpowers g := h ▸ Subgroup.mem_top x
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨d, hd, k, rfl⟩
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨d₁, hd₁, a, rfl⟩ := hdec x
  obtain ⟨d₂, hd₂, b, rfl⟩ := hdec y
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  simp only [map_mul, map_zpow]
  have hg : Commute (QuotientGroup.mk' N g ^ a) (QuotientGroup.mk' N g ^ b) :=
    Commute.zpow_zpow_self _ a b
  have h1 := hcen d₁ hd₁ (d₂ * g ^ b)
  have h2 := hcen d₂ hd₂ (g ^ a)
  simp only [map_mul, map_zpow] at h1 h2
  exact (h1.mul_left (h2.symm.mul_right hg)).eq

theorem commutator_le_of_isNilpotent_quotient {N : Subgroup G} [N.Normal]
    (hnil : Group.IsNilpotent (G ⧸ N))
    (h : commutator G ≤ ⁅commutator G, ⊤⁆) : commutator G ≤ N := by
  have hle : ∀ n, commutator G ≤ (⊤ : Subgroup G).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact h.trans (Subgroup.commutator_mono ih le_rfl)
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 hnil
  have hmap : ((⊤ : Subgroup G).lowerCentralSeries n).map
      (QuotientGroup.mk' N) ≤ ⊥ := by
    rw [Subgroup.map_lowerCentralSeries, ← hn]
    exact Subgroup.lowerCentralSeries_mono n le_top
  rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hmap
  exact (hle n).trans hmap

theorem mul_inv_mem_of_sup_zpowers {D : Subgroup G} [D.Normal] {g : G}
    (h : D ⊔ Subgroup.zpowers g = ⊤) (hg2 : g ^ 2 ∈ D)
    {s : G} (hs : s ∉ D) : s * g⁻¹ ∈ D := by
  have hx : s ∈ D ⊔ Subgroup.zpowers g := h ▸ Subgroup.mem_top s
  obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · exfalso
    apply hs
    refine mul_mem hd ?_
    rw [zpow_mul]
    exact zpow_mem (by exact_mod_cast hg2) j
  · have e : d * g ^ (2 * j + 1) * g⁻¹ = d * (g ^ 2) ^ j := by
      rw [zpow_add_one, mul_assoc, mul_assoc, mul_inv_cancel, mul_one, zpow_mul]
      norm_cast
    rw [e]
    exact mul_mem hd (zpow_mem hg2 j)

theorem false_of_swapped_factors [Finite G]
    {D A B P : Subgroup G} [hD : D.Normal] {g x : G}
    (h : D ⊔ Subgroup.zpowers g = ⊤) (hgD : g ∉ D) (hg2 : g ^ 2 ∈ D)
    (hgp : IsPGroup 2 (Subgroup.zpowers g))
    (hAD : A ≤ D) (hBD : B ≤ D)
    (hA : ∀ d ∈ D, ∀ a ∈ A, d * a * d⁻¹ ∈ A)
    (hB : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ ∈ B)
    (hAB : A ⊓ B = ⊥) (hsup : A ⊔ B = D)
    (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ B)
    (hxA : x ∈ A) (S : Sylow 2 G) (hP : P ≠ ⊤)
    (hNx : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ P)
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBP : B ≤ P := by
    intro b hb
    apply hNx
    apply Subgroup.centralizer_le_normalizer
    have hc : x * b = b * x := by
      have h1 : ⁅x, b⁆ ∈ A ⊓ B := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          have : b * x⁻¹ * b⁻¹ ∈ A := hA b (hBD hb) _ (inv_mem hxA)
          have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
          rw [e]
          exact mul_mem hxA this
        · rw [commutatorElement_def]
          exact mul_mem (hB x (hAD hxA) b hb) (inv_mem hb)
      rw [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute x b from hc) k).eq
  have hSD : ¬ (S : Subgroup G) ≤ D := by
    intro hle
    obtain ⟨Q, hQ⟩ := hgp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S Q
    apply hgD
    have hgQ : g ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g)
    rw [← hc, Sylow.coe_subgroup_smul] at hgQ
    obtain ⟨y, hy, rfl⟩ := hgQ
    exact hD.conj_mem y (hle hy) c
  obtain ⟨s, hsS, hsD⟩ := Set.not_subset.1 hSD
  have hsP : s ∈ P := hNS (Subgroup.le_normalizer hsS)
  have hd : s * g⁻¹ ∈ D := mul_inv_mem_of_sup_zpowers h hg2 hsD
  have hAP : A ≤ P := by
    intro a ha
    set d := s * g⁻¹
    have hb : g * (d⁻¹ * a * d) * g⁻¹ ∈ B := by
      have h1 : d⁻¹ * a * d ∈ A := by
        have := hA d⁻¹ (inv_mem hd) a ha
        rwa [inv_inv] at this
      exact hgA _ h1
    have hb' : (g ^ 2)⁻¹ * (g * (d⁻¹ * a * d) * g⁻¹) * g ^ 2 ∈ B := by
      have := hB (g ^ 2)⁻¹ (inv_mem hg2) _ hb
      rwa [inv_inv] at this
    have e : a = s * ((g ^ 2)⁻¹ * (g * (d⁻¹ * a * d) * g⁻¹) * g ^ 2) * s⁻¹ := by
      simp only [d]
      group
    rw [e]
    exact mul_mem (mul_mem hsP (hBP hb')) (inv_mem hsP)
  have hDP : D ≤ P := hsup ▸ sup_le hAP hBP
  apply hP
  rw [eq_top_iff, ← h]
  refine sup_le hDP ?_
  rw [Subgroup.zpowers_le]
  have e : g = (s * g⁻¹)⁻¹ * s := by group
  rw [e]
  exact mul_mem (inv_mem (hDP hd)) hsP

end InfoGeometry.Exceptional.CFSGPort.Simplicity

end
