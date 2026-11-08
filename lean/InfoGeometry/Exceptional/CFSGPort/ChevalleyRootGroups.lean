/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from AxiomMath/CFSG, Apache-2.0. Module and namespace paths are
adapted for this repository's Lean 4.34.1 / mathlib pin.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyPinnedLemmas
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootCheck
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyStringCheck

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

universe u v

variable (τ : Tag) (R : Type u) [CommRing R]

@[expose] def pinnedHom (α : Fin τ.rank → ℤ) :
    Multiplicative R →* (Module.End R (RootModule τ R))ˣ where
  toFun c := pinnedX τ R α c.toAdd
  map_one' := pinnedX_zero τ R α
  map_mul' c d := pinnedX_add τ R α c.toAdd d.toAdd

theorem pinnedHom_apply (α : Fin τ.rank → ℤ) (c : Multiplicative R) :
    pinnedHom τ R α c = pinnedX τ R α c.toAdd :=
  rfl

theorem pinnedHom_injective (α : Fin τ.rank → ℤ) : Function.Injective (pinnedHom τ R α) :=
  fun _ _ h => Multiplicative.toAdd.injective (pinnedX_injective τ R α h)

theorem rootSubgroup_eq_range (α : Fin τ.rank → ℤ) :
    rootSubgroup τ R α = (pinnedHom τ R α).range := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨c.toAdd, rfl⟩

variable {τ R} in
theorem mem_rootSubgroup {α : Fin τ.rank → ℤ} {g : (Module.End R (RootModule τ R))ˣ} :
    g ∈ rootSubgroup τ R α ↔ ∃ c : R, pinnedX τ R α c = g := by
  rw [rootSubgroup_eq_range]
  exact ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

/-- Conjugation transports a pinned root subgroup when it transports its
parameterization surjectively. This is the local pinned-root form of the
external `RootOperatorFamily.map_conj_rootSubgroup` API. -/
theorem map_conj_rootSubgroup {α β : Fin τ.rank → ℤ}
    (g : (Module.End R (RootModule τ R))ˣ) {u : R → R}
    (hu : Function.Surjective u)
    (h : ∀ c, g * pinnedX τ R α c * g⁻¹ = pinnedX τ R β (u c)) :
    (rootSubgroup τ R α).map (MulAut.conj g).toMonoidHom = rootSubgroup τ R β := by
  rw [rootSubgroup_eq_range, MonoidHom.map_range, rootSubgroup_eq_range]
  apply Subgroup.ext
  intro x
  change (∃ c : Multiplicative R,
      (MulAut.conj g).toMonoidHom (pinnedHom τ R α c) = x) ↔
    ∃ d : Multiplicative R, pinnedHom τ R β d = x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd (u c.toAdd), ?_⟩
    change pinnedX τ R β (u c.toAdd) = g * pinnedX τ R α c.toAdd * g⁻¹
    exact (h c.toAdd).symm
  · rintro ⟨d, rfl⟩
    obtain ⟨c, rfl⟩ := hu d.toAdd
    refine ⟨Multiplicative.ofAdd c, ?_⟩
    change g * pinnedX τ R α c * g⁻¹ = pinnedX τ R β (u c)
    exact h c

/-- Every pinned root subgroup over a nontrivial coefficient ring is
nontrivial. Injectivity of the root parameter map distinguishes parameters
`1` and `0` inside the actual endomorphism-unit carrier. -/
theorem rootSubgroup_ne_bot (α : Fin τ.rank → ℤ) [Nontrivial R] :
    rootSubgroup τ R α ≠ ⊥ := by
  apply (Subgroup.ne_bot_iff_exists_ne_one).2
  refine ⟨⟨pinnedX τ R α 1, Subgroup.subset_closure ⟨1, rfl⟩⟩, ?_⟩
  intro h
  have hval := congrArg Subtype.val h
  have hparam : pinnedX τ R α 1 = pinnedX τ R α 0 := by
    rw [pinnedX_zero]
    exact hval
  exact one_ne_zero (pinnedX_injective τ R α hparam)

/-- A pinned root subgroup is abelian because its parameter group is the
additive group of the coefficient ring. -/
theorem rootSubgroup_isMulCommutative (α : Fin τ.rank → ℤ) :
    IsMulCommutative (rootSubgroup τ R α) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 a.2
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 b.2
  change (a.1 : (Module.End R (RootModule τ R))ˣ) * b.1 = b.1 * a.1
  calc
    _ = pinnedX τ R α c * pinnedX τ R α d := by rw [hc, hd]
    _ = pinnedX τ R α (c + d) := (pinnedX_add τ R α c d).symm
    _ = pinnedX τ R α (d + c) := by rw [add_comm]
    _ = pinnedX τ R α d * pinnedX τ R α c := pinnedX_add τ R α d c
    _ = _ := by rw [hc, hd]

/-- The commutator subgroup of a single pinned root subgroup is trivial.
This is the self-commutator clause in the external CFSG root-group interface. -/
theorem commutator_rootSubgroup_self_eq_bot (α : Fin τ.rank → ℤ) :
    ⁅rootSubgroup τ R α, rootSubgroup τ R α⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.le_centralizer_iff_isMulCommutative]
  exact rootSubgroup_isMulCommutative τ R α

@[expose] def rootSubgroupEquiv (α : Fin τ.rank → ℤ) : Multiplicative R ≃* rootSubgroup τ R α :=
  (MonoidHom.ofInjective (pinnedHom_injective τ R α)).trans
    (MulEquiv.subgroupCongr (rootSubgroup_eq_range τ R α).symm)

theorem coe_rootSubgroupEquiv (α : Fin τ.rank → ℤ) (c : R) :
    (rootSubgroupEquiv τ R α (Multiplicative.ofAdd c) : (Module.End R (RootModule τ R))ˣ) =
      pinnedX τ R α c :=
  rfl

variable {τ}

theorem pinnedWeyl_mem_adjointGroup {K : Type v} [Field K] (α : Fin τ.rank → ℤ) :
    pinnedWeyl τ K α ∈ adjointGroup τ K := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hg)
  exact weylElt_mem_adjointGroup _ 1

theorem pinnedX_mem_adjointGroup {K : Type v} [Field K] (α : Fin τ.rank → ℤ) (c : K) :
    pinnedX τ K α c ∈ adjointGroup τ K :=
  mul_mem (mul_mem (pinnedWeyl_mem_adjointGroup α) (xUnit_mem_adjointGroup _ _))
    (inv_mem (pinnedWeyl_mem_adjointGroup α))

theorem rootSubgroup_le_adjointGroup {K : Type v} [Field K] (α : Fin τ.rank → ℤ) :
    rootSubgroup τ K α ≤ adjointGroup τ K :=
  (Subgroup.closure_le _).2 (Set.range_subset_iff.2 (pinnedX_mem_adjointGroup α))

theorem adjointGroup_eq_rootSpan {K : Type v} [Field K] :
    adjointGroup τ K = rootSpan τ K {α | IsRoot τ α} := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_)
    (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  rintro g ⟨i, c, hg | hg⟩
  · have h : g = pinnedX τ K (Pi.single i 1) c := by
      rw [pinnedX_single]
      exact Units.ext hg
    rw [h]
    exact le_biSup (rootSubgroup τ K) (isRoot_single τ i) (Subgroup.subset_closure ⟨c, rfl⟩)
  · have h : g = pinnedX τ K (-Pi.single i 1) c := by
      rw [pinnedX_neg_single]
      exact Units.ext hg
    rw [h]
    exact le_biSup (rootSubgroup τ K) (isRoot_neg_single τ i) (Subgroup.subset_closure ⟨c, rfl⟩)

theorem card_rootSubgroup {K : Type v} [Field K] (α : Fin τ.rank → ℤ) :
    Nat.card (rootSubgroup τ K α) = Nat.card K :=
  (Nat.card_congr (rootSubgroupEquiv τ K α).toEquiv).symm

theorem orderOf_eq_of_mem_rootSubgroup {K : Type v} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {α : Fin τ.rank → ℤ} {g : (Module.End K (RootModule τ K))ˣ} (hg : g ∈ rootSubgroup τ K α)
    (hg1 : g ≠ 1) : orderOf g = p := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  have hc : c ≠ 0 := by
    rintro rfl
    exact hg1 (pinnedX_zero τ K α)
  have hpc : p • c = 0 := by
    rw [nsmul_eq_mul, CharP.cast_eq_zero K p, zero_mul]
  have h := orderOf_injective _ (pinnedHom_injective τ K α) (Multiplicative.ofAdd c)
  rw [pinnedHom_apply, toAdd_ofAdd, orderOf_ofAdd_eq_addOrderOf, addOrderOf_eq_prime hpc hc] at h
  exact h

theorem all_root_subgroup_structure (τ : Tag) :
    (∀ (R : Type u) [CommRing R] (α : Fin τ.rank → ℤ), IsRoot τ α →
      ∃ e : Multiplicative R ≃* rootSubgroup τ R α, ∀ c : R,
        (e (Multiplicative.ofAdd c) : (Module.End R (RootModule τ R))ˣ) = pinnedX τ R α c) ∧
      (∀ (K : Type v) [Field K],
        (∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootSubgroup τ K α ≤ adjointGroup τ K) ∧
          adjointGroup τ K = rootSpan τ K {α | IsRoot τ α}) ∧
      ∀ (K : Type v) [Field K] [Finite K] (p : ℕ) [CharP K p] (α : Fin τ.rank → ℤ),
        IsRoot τ α → Nat.card (rootSubgroup τ K α) = Nat.card K ∧
          ∀ g ∈ rootSubgroup τ K α, g ≠ 1 → orderOf g = p := by
  refine ⟨fun R _ α _ => ⟨rootSubgroupEquiv τ R α, coe_rootSubgroupEquiv τ R α⟩,
    fun K _ => ⟨fun α _ => rootSubgroup_le_adjointGroup α, adjointGroup_eq_rootSpan⟩,
    fun K _ _ p _ α _ => ⟨card_rootSubgroup α, fun g hg hg1 => ?_⟩⟩
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact orderOf_eq_of_mem_rootSubgroup hg hg1

end InfoGeometry.Exceptional.CFSGPort.Chevalley
