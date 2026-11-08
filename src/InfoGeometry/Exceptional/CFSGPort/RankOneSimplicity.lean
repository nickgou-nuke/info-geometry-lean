/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.QuasisimpleTransport

/-!
# Rank-one simplicity criterion port

Local port of the generic normal-core argument in
`CFSG.LieType.Simplicity.RankOne`. The criterion is stated over an actual
group and its subgroups; exceptional-family applications still need their
operator-carrier Bruhat, solvability, conjugation, and generation proofs.
-/

public section

namespace InfoGeometry.Exceptional.CFSGPort.Simplicity

variable {Γ : Type*} [Group Γ]

theorem eq_top_of_le_of_not_le {B P : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hBP : B ≤ P) (hP : ¬ P ≤ B) : P = ⊤ := by
  obtain ⟨g, hgP, hgB⟩ := Set.not_subset.1 hP
  rcases hbruhat g with h | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact absurd h hgB
  · have hn : n ∈ P := by
      have e : n = b₁⁻¹ * (b₁ * n * b₂) * b₂⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hBP hb₁)) hgP) (inv_mem (hBP hb₂))
    rw [eq_top_iff]
    intro x _
    rcases hbruhat x with h | ⟨c₁, hc₁, c₂, hc₂, rfl⟩
    · exact hBP h
    · exact mul_mem (mul_mem (hBP hc₁) hn) (hBP hc₂)

theorem le_normalCore_or_eq_top_of_rankOne {B : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hperf : Group.IsPerfect Γ) (hB : Group.IsSolvable B)
    (M : Subgroup Γ) [M.Normal] : M ≤ B.normalCore ∨ M = ⊤ := by
  by_cases hMB : M ≤ B
  · exact .inl (Subgroup.normal_le_normalCore.2 hMB)
  · exact .inr (eq_top_of_sup_eq_top hperf hB
      (eq_top_of_le_of_not_le hbruhat le_sup_right fun h =>
        hMB (le_sup_left.trans h)))

theorem le_center_of_inf_eq_bot {B U C : Subgroup Γ} [hC : C.Normal]
    (hCB : C ≤ B) (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hCU : C ⊓ U = ⊥) (hgen : Subgroup.normalClosure (U : Set Γ) = ⊤) :
    C ≤ Subgroup.center Γ := by
  have hcomm : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c := by
    intro c hc u hu
    have h1 : c * u * c⁻¹ * u⁻¹ ∈ C := by
      have hu' : u * c⁻¹ * u⁻¹ ∈ C := hC.conj_mem c⁻¹ (inv_mem hc) u
      have e : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
      rw [e]
      exact mul_mem hc hu'
    have h2 : c * u * c⁻¹ * u⁻¹ ∈ U :=
      mul_mem (hUB c (hCB hc) u hu) (inv_mem hu)
    have h3 : c * u * c⁻¹ * u⁻¹ = 1 := by
      have hmem : c * u * c⁻¹ * u⁻¹ ∈ C ⊓ U := ⟨h1, h2⟩
      rw [hCU] at hmem
      exact hmem
    calc
      c * u = c * u * c⁻¹ * u⁻¹ * (u * c) := by group
      _ = u * c := by rw [h3, one_mul]
  have hconj : (U : Set Γ) ⊆ (Subgroup.centralizer (C : Set Γ) : Set Γ) := by
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro c hc
    exact hcomm c hc u hu
  have hle : Subgroup.normalClosure (U : Set Γ) ≤ Subgroup.centralizer (C : Set Γ) :=
    Subgroup.normalClosure_le_normal hconj
  rw [hgen, top_le_iff] at hle
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (C : Set Γ) := hle ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.1 hg c hc).symm

theorem isSimpleGroup_quotient_center_of_rankOne [Nontrivial Γ]
    {B U : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hperf : Group.IsPerfect Γ) (hB : Group.IsSolvable B)
    (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hCU : B.normalCore ⊓ U = ⊥)
    (hgen : Subgroup.normalClosure (U : Set Γ) = ⊤) :
    IsSimpleGroup (Γ ⧸ Subgroup.center Γ) := by
  have hcore : B.normalCore ≤ Subgroup.center Γ :=
    le_center_of_inf_eq_bot (Subgroup.normalCore_le B) hUB hCU hgen
  exact isSimpleGroup_quotient_center_of_forall hperf fun M _ => by
    rcases le_normalCore_or_eq_top_of_rankOne hbruhat hperf hB M with h | h
    · exact .inl (h.trans hcore)
    · exact .inr h

theorem isQuasisimple_of_rankOne [Nontrivial Γ] {B U : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hperf : Group.IsPerfect Γ) (hB : Group.IsSolvable B)
    (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hUn : ∀ u ∈ U, n * u * n⁻¹ ∈ B → u = 1) (hU : U ≠ ⊥) :
    IsQuasisimple Γ := by
  have hCU : B.normalCore ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hc, hu⟩
    rw [Subgroup.mem_bot]
    exact hUn u hu
      (Subgroup.normalCore_le B (B.normalCore_normal.conj_mem u hc n))
  have hgen : Subgroup.normalClosure (U : Set Γ) = ⊤ := by
    rcases le_normalCore_or_eq_top_of_rankOne hbruhat hperf hB
        (Subgroup.normalClosure (U : Set Γ)) with h | h
    · have hUbot : U = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have hmem : u ∈ B.normalCore ⊓ U :=
          ⟨h (Subgroup.subset_normalClosure hu), hu⟩
        rw [hCU] at hmem
        exact hmem
      exact (hU hUbot).elim
    · exact h
  have hcore : B.normalCore ≤ Subgroup.center Γ :=
    le_center_of_inf_eq_bot (Subgroup.normalCore_le B) hUB hCU hgen
  apply isQuasisimple_of_forall hperf
  intro M hM
  rcases le_normalCore_or_eq_top_of_rankOne hbruhat hperf hB M with h | h
  · exact .inl (h.trans hcore)
  · exact .inr h

theorem isQuasisimple_of_rankOne_subgroup {D B U : Subgroup Γ} {n : Γ}
    (hn : n ∈ D) (hBD : B ≤ D) (hUD : U ≤ D)
    (hbruhat : ∀ g ∈ D,
      g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hperf : Group.IsPerfect D) (hB : Group.IsSolvable B)
    (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hUn : ∀ u ∈ U, n * u * n⁻¹ ∈ B → u = 1) (hU : U ≠ ⊥) :
    IsQuasisimple D := by
  obtain ⟨u₀, hu₀, hu₀1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hU
  have hD_nontrivial : Nontrivial D :=
    ⟨⟨⟨u₀, hUD hu₀⟩, 1,
      fun h => hu₀1 (by simpa using congrArg Subtype.val h)⟩⟩
  have hB' : Group.IsSolvable (B.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hBD).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBD).injective
  letI := hD_nontrivial
  refine isQuasisimple_of_rankOne (B := B.subgroupOf D) (U := U.subgroupOf D)
      (n := ⟨n, hn⟩) (fun g => ?_) hperf hB'
      (fun b hb u hu => hUB b hb u hu) (fun u hu h => ?_) ?_
  · rcases hbruhat g g.2 with h | ⟨b₁, hb₁, b₂, hb₂, h⟩
    · exact .inl h
    · exact .inr ⟨⟨b₁, hBD hb₁⟩, hb₁, ⟨b₂, hBD hb₂⟩, hb₂, Subtype.ext h⟩
  · exact Subtype.ext (hUn u hu h)
  · intro h
    have hu : (⟨u₀, hUD hu₀⟩ : D) ∈ U.subgroupOf D := hu₀
    rw [h, Subgroup.mem_bot] at hu
    exact hu₀1 (congrArg Subtype.val hu)

theorem isPerfect_commutator_of_le {S : Subgroup Γ}
    (hS : S ≤ derivedSeries Γ 2)
    (hX : commutator Γ ≤ Subgroup.normalClosure (S : Set Γ)) :
    Group.IsPerfect (commutator Γ) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  have hnormal : Subgroup.normalClosure (S : Set Γ) ≤ derivedSeries Γ 2 :=
    Subgroup.normalClosure_le_normal hS
  have hle := hX.trans hnormal
  rwa [derivedSeries_succ, derivedSeries_one] at hle

theorem bruhat_of_le {B S A D : Subgroup Γ} {n n' a₀ : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hSD : S ≤ D) (hSB : S ≤ B) (hAB : A ≤ B)
    (hBSA : ∀ b ∈ B, ∃ s ∈ S, ∃ c ∈ A, b = s * c)
    (hnA : ∀ c ∈ A, n⁻¹ * c * n ∈ A) (hn' : n' ∈ D)
    (ha₀ : a₀ ∈ A) (hn : n = n' * a₀) {g : Γ} (hg : g ∈ D) :
    g ∈ B ⊓ D ∨ ∃ b₁ ∈ B ⊓ D, ∃ b₂ ∈ B ⊓ D, g = b₁ * n' * b₂ := by
  rcases hbruhat g with h | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact .inl ⟨h, hg⟩
  obtain ⟨s, hs, c, hc, rfl⟩ := hBSA b₁ hb₁
  set b := a₀ * (n⁻¹ * c * n) * b₂ with hb
  have he : s * c * n * b₂ = s * n' * b := by
    rw [hb, hn]
    group
  have hbB : b ∈ B := mul_mem (mul_mem (hAB ha₀) (hAB (hnA c hc))) hb₂
  have hbD : b ∈ D := by
    have e : b = n'⁻¹ * s⁻¹ * (s * c * n * b₂) := by
      rw [he]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hn') (inv_mem (hSD hs))) hg
  exact .inr ⟨s, ⟨hSB hs, hSD hs⟩, b, ⟨hbB, hbD⟩, he⟩

end InfoGeometry.Exceptional.CFSGPort.Simplicity

end
