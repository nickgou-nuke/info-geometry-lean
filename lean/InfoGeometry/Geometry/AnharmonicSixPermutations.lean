/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AnharmonicPunctures

/-! The six-element subgroup of the existing puncture permutations. -/
noncomputable section
namespace InfoGeometry.Geometry.AnharmonicPunctures

def anharmonicWord : Fin 6 → Equiv.Perm Punctured
  | 0 => 1
  | 1 => exchangeEquiv
  | 2 => inversionEquiv
  | 3 => exchangeEquiv * inversionEquiv
  | 4 => inversionEquiv * exchangeEquiv
  | 5 => exchangeEquiv * inversionEquiv * exchangeEquiv

private theorem braid_perm : inversionEquiv * exchangeEquiv * inversionEquiv =
    exchangeEquiv * inversionEquiv * exchangeEquiv := by
  ext z
  exact (exchange_inversion_exchange z).symm

private theorem exchange_cancel (g : Equiv.Perm Punctured) :
    exchangeEquiv * (exchangeEquiv * g) = g := by
  rw [← mul_assoc, exchangeEquiv_sq, one_mul]

private theorem inversion_cancel (g : Equiv.Perm Punctured) :
    inversionEquiv * (inversionEquiv * g) = g := by
  rw [← mul_assoc, inversionEquiv_sq, one_mul]

private theorem braid_tail (g : Equiv.Perm Punctured) :
    inversionEquiv * (exchangeEquiv * (inversionEquiv * g)) =
      exchangeEquiv * (inversionEquiv * (exchangeEquiv * g)) := by
  simpa only [mul_assoc] using congrArg (fun x => x * g) braid_perm

private theorem braid_head : inversionEquiv * (exchangeEquiv * inversionEquiv) =
    exchangeEquiv * (inversionEquiv * exchangeEquiv) := by
  simpa only [mul_assoc] using braid_perm

theorem anharmonicWord_mul (a b : Fin 6) :
    ∃ c, anharmonicWord a * anharmonicWord b = anharmonicWord c := by
  fin_cases a <;> fin_cases b
  all_goals first
    | (refine ⟨0, ?_⟩; (solve | simp_all only [anharmonicWord, mul_one, one_mul, mul_assoc, exchange_cancel, inversion_cancel, exchangeEquiv_sq, inversionEquiv_sq, braid_tail, braid_head]))
    | (refine ⟨1, ?_⟩; (solve | simp_all only [anharmonicWord, mul_one, one_mul, mul_assoc, exchange_cancel, inversion_cancel, exchangeEquiv_sq, inversionEquiv_sq, braid_tail, braid_head]))
    | (refine ⟨2, ?_⟩; (solve | simp_all only [anharmonicWord, mul_one, one_mul, mul_assoc, exchange_cancel, exchangeEquiv_sq, braid_tail, braid_head]))
    | (refine ⟨3, ?_⟩; (solve | simp_all only [anharmonicWord, mul_one, one_mul, mul_assoc, exchange_cancel, exchangeEquiv_sq, braid_tail, braid_head]))
    | (refine ⟨4, ?_⟩; (solve | simp_all only [anharmonicWord, mul_one, one_mul, mul_assoc, exchange_cancel, braid_head]))
    | (refine ⟨5, ?_⟩; (solve | simp_all only [anharmonicWord, mul_one, one_mul, mul_assoc, braid_head]))

theorem anharmonicWord_inv (a : Fin 6) :
    ∃ b, (anharmonicWord a)⁻¹ = anharmonicWord b := by
  have he : exchangeEquiv⁻¹ = exchangeEquiv := inv_eq_of_mul_eq_one_right exchangeEquiv_sq
  have hi : inversionEquiv⁻¹ = inversionEquiv := inv_eq_of_mul_eq_one_right inversionEquiv_sq
  fin_cases a
  · exact ⟨0, inv_one⟩
  · exact ⟨1, he⟩
  · exact ⟨2, hi⟩
  · exact ⟨4, by simp [anharmonicWord, he, hi]⟩
  · exact ⟨3, by simp [anharmonicWord, he, hi]⟩
  · exact ⟨5, by simp [anharmonicWord, he, hi, mul_assoc]⟩

def sixPermutationSubgroup : Subgroup (Equiv.Perm Punctured) where
  carrier := Set.range anharmonicWord
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    obtain ⟨c, hc⟩ := anharmonicWord_mul a b
    exact ⟨c, hc.symm⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := anharmonicWord_inv a
    exact ⟨b, hb.symm⟩

def anharmonicGroup : Subgroup (Equiv.Perm Punctured) :=
  Subgroup.closure {exchangeEquiv, inversionEquiv}

theorem anharmonicGroup_eq_sixPermutationSubgroup :
    anharmonicGroup = sixPermutationSubgroup := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact ⟨1, rfl⟩
    · have : g = inversionEquiv := Set.mem_singleton_iff.mp hg
      subst g
      exact ⟨2, rfl⟩
  · have he : exchangeEquiv ∈ anharmonicGroup := Subgroup.subset_closure (by simp)
    have hi : inversionEquiv ∈ anharmonicGroup := Subgroup.subset_closure (by simp)
    rintro g ⟨a, rfl⟩
    fin_cases a
    · exact Subgroup.one_mem _
    · exact he
    · exact hi
    · exact Subgroup.mul_mem _ he hi
    · exact Subgroup.mul_mem _ hi he
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ he hi) he

theorem mem_anharmonicGroup_iff (g : Equiv.Perm Punctured) :
    g ∈ anharmonicGroup ↔ ∃ a : Fin 6, anharmonicWord a = g := by
  rw [anharmonicGroup_eq_sixPermutationSubgroup]
  rfl

def separatingPoint : Punctured := ⟨3, by norm_num⟩

theorem anharmonicWord_separating_values (a : Fin 6) :
    (anharmonicWord a separatingPoint).val =
      (![3, -2, 1 / 3, 2 / 3, -(1 / 2), 3 / 2] : Fin 6 → ℂ) a := by
  fin_cases a
  · change (3 : ℂ) = 3; rfl
  · change (1 - 3 : ℂ) = -2; norm_num
  · change (3 : ℂ)⁻¹ = 1 / 3; norm_num
  · change (1 - (3 : ℂ)⁻¹) = 2 / 3; norm_num
  · change (1 - (3 : ℂ))⁻¹ = -(1 / 2); norm_num
  · change (1 - (1 - (3 : ℂ))⁻¹) = 3 / 2; norm_num

theorem anharmonicWord_injective : Function.Injective anharmonicWord := by
  intro a b h
  have hv := congrArg (fun g : Equiv.Perm Punctured => (g separatingPoint).val) h
  rw [anharmonicWord_separating_values, anharmonicWord_separating_values] at hv
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; norm_num at hv)

theorem anharmonicGroup_natCard : Nat.card anharmonicGroup = 6 := by
  let f : Fin 6 → anharmonicGroup := fun a =>
    ⟨anharmonicWord a, (mem_anharmonicGroup_iff _).mpr ⟨a, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact anharmonicWord_injective (congrArg Subtype.val h)
    · intro g
      obtain ⟨a, ha⟩ := (mem_anharmonicGroup_iff g.val).mp g.property
      exact ⟨a, Subtype.ext ha⟩
  simpa using (Nat.card_congr (Equiv.ofBijective f hf)).symm

end InfoGeometry.Geometry.AnharmonicPunctures
