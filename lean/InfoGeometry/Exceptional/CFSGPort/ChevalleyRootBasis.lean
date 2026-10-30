/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Sparse.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRoots

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

abbrev dim (τ : Tag) : ℕ := τ.rank + τ.rootCertificate.roots.length

/-- Distinct entries in the checked root table denote distinct roots. -/
theorem root_index_injective {p q : ℕ}
    (hp : p < τ.rootCertificate.roots.length)
    (hq : q < τ.rootCertificate.roots.length)
    (h : τ.rootCertificate.root p = τ.rootCertificate.root q) : p = q := by
  have hn := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  exact (List.nodup_map_iff_inj_on List.nodup_range).mp hn p
    (List.mem_range.mpr hp) q (List.mem_range.mpr hq) (congrArg List.ofFn h)

/-- Certificate numbering: Cartan labels first, then the checked root list. -/
@[expose] def posLabel (p : ℕ) (hp : p < dim τ) : Label τ :=
  if h : p < τ.rank then .inl ⟨p, h⟩
  else .inr ⟨τ.rootCertificate.root (p - τ.rank),
    RootCertificate.isRoot_root τ.rootCertificate_check _ (by
      simp only [dim] at hp
      omega)⟩

theorem posLabel_injective {p q : ℕ} (hp : p < dim τ) (hq : q < dim τ)
    (h : posLabel p hp = posLabel q hq) : p = q := by
  simp only [dim] at hp hq
  by_cases h₁ : p < τ.rank <;> by_cases h₂ : q < τ.rank <;>
    simp only [posLabel, h₁, h₂, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
      Fin.mk.injEq, Subtype.mk.injEq, reduceCtorEq] at h
  · exact h
  · have := root_index_injective (by omega) (by omega) h
    omega

theorem posLabel_surjective (b : Label τ) : ∃ p, ∃ hp : p < dim τ, posLabel p hp = b := by
  rcases b with j | ⟨α, hα⟩
  · exact ⟨j, by simp only [dim]; omega, by simp [posLabel]⟩
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
    refine ⟨τ.rank + k, by simp only [dim]; omega, ?_⟩
    simp [posLabel]

variable (τ R) in
/-- The actual root-module basis vector at a valid certificate index;
out-of-range indices evaluate to zero. -/
@[expose] def posVec (p : ℕ) : RootModule τ R :=
  if hp : p < dim τ then Finsupp.single (posLabel p hp) (1 : R) else 0

theorem posVec_eq_single {p : ℕ} (hp : p < dim τ) :
    posVec τ R p = Finsupp.single (posLabel p hp) 1 := by
  simp [posVec, hp]

/-- Equality on all numbered basis vectors establishes operator equality. -/
theorem ext_posVec {f g : Module.End R (RootModule τ R)}
    (h : ∀ p, p < dim τ → f (posVec τ R p) = g (posVec τ R p)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  simpa [posVec_eq_single hp] using h p hp

variable (τ R) in
@[expose] def posCoord (p : ℕ) : RootModule τ R →ₗ[R] R :=
  if hp : p < dim τ then Finsupp.lapply (posLabel p hp) else 0

theorem posCoord_posVec {p q : ℕ} (hq : q < dim τ) :
    posCoord τ R p (posVec τ R q) = if p = q then 1 else 0 := by
  unfold posCoord
  split_ifs with hp hpq hpq
  · subst hpq
    rw [posVec_eq_single hq, Finsupp.lapply_apply, Finsupp.single_eq_same]
  · rw [posVec_eq_single hq, Finsupp.lapply_apply, Finsupp.single_eq_of_ne]
    exact fun h => hpq (posLabel_injective hp hq h)
  · exact absurd (hpq ▸ hq) hp
  · rfl

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
