/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
The root-parameter commutator identity used by the external CFSG
perfectness arguments, proved for the local pinned root-group API.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroups
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroupsTorus
public import InfoGeometry.Exceptional.CFSGPort.ExceptionalCartanHelpers

public section

set_option maxHeartbeats 0

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

open scoped commutatorElement

variable {τ : Tag} {K : Type*} [Field K]

/-- Commuting a torus element with a pinned root element scales its root
parameter by the torus weight and subtracts the original parameter. -/
theorem torus_commutator_pinnedX (i : Fin τ.rank) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (t : Kˣ) (c : K) :
    ⁅torusElt τ K i t, pinnedX τ K α c⁆ =
      pinnedX τ K α ((((t ^ (∑ j, τ.cartan i j * α j) : Kˣ) : K) - 1) * c) := by
  rw [commutatorElement_def, root_torus_conjugation i hα t c, pinnedX_neg,
    ← pinnedX_add]
  congr 1
  ring

/-- If a torus element acts nontrivially on a root parameter, that root
subgroup lies in the commutator subgroup of the adjoint group. This is the
root-group containment used by the external CFSG perfectness argument. -/
theorem rootSubgroup_le_commutator_of_torus {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (i : Fin τ.rank) (t : Kˣ)
    (ht : (((t ^ (∑ j, τ.cartan i j * α j) : Kˣ) : K) ≠ 1)) :
    rootSubgroup τ K α ≤
      (commutator ↥(adjointGroup τ K)).map (adjointGroup τ K).subtype := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  let w : K := ((t ^ (∑ j, τ.cartan i j * α j) : Kˣ) : K)
  have hw : w - 1 ≠ 0 := sub_ne_zero.mpr ht
  have hcomm :
      ⁅torusElt τ K i t, pinnedX τ K α (c / (w - 1))⁆ ∈
        ⁅adjointGroup τ K, adjointGroup τ K⁆ :=
    Subgroup.commutator_mem_commutator
      (torusElt_mem_adjointGroup i t) (pinnedX_mem_adjointGroup α _)
  have heq : ⁅torusElt τ K i t, pinnedX τ K α (c / (w - 1))⁆ =
      pinnedX τ K α c := by
    rw [torus_commutator_pinnedX i hα t]
    congr 1
    dsimp [w]
    calc
      _ = c / (w - 1) * (w - 1) := mul_comm _ _
      _ = c := div_mul_cancel₀ c hw
  rw [← Subgroup.map_subtype_commutator] at hcomm
  rw [heq] at hcomm
  exact hcomm

/-- A simply-laced neighbor gives a torus weight of `-1`, placing the simple
root subgroup in the derived subgroup whenever the field has a nonidentity
unit. This is the local form of the external F₄/E₈ commutator step. -/
theorem simpleRootSubgroup_le_commutator_of_neighbor (τ : Tag) (K : Type*) [Field K]
    (i l : Fin τ.rank) (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1)
    (t : Kˣ) (ht : (t : K) ≠ 1) :
    rootSubgroup τ K (Pi.single i 1) ≤
      (commutator ↥(adjointGroup τ K)).map (adjointGroup τ K).subtype := by
  have hpair :
      (∑ j, τ.cartan l j * (Pi.single i (1 : ℤ) : Fin τ.rank → ℤ) j) =
        τ.cartan l i := by
    simp [Pi.single_apply]
  have hweight : (((t ^ (-1 : ℤ) : Kˣ) : K) ≠ 1) := by
    simpa [zpow_neg_one, Units.val_inv_eq_inv_val] using (inv_ne_one.mpr ht)
  have hweight' :
      (((t ^ (∑ j, τ.cartan l j *
        (Pi.single i (1 : ℤ) : Fin τ.rank → ℤ) j) : Kˣ) : K) ≠ 1) := by
    simpa [hpair, hli] using hweight
  exact rootSubgroup_le_commutator_of_torus (isRoot_single τ i) l t hweight'

/-- A field with at least three elements has a nonzero element other than one.
This is the parameter needed to choose a nontrivial torus weight. -/
theorem exists_ne_zero_ne_one_of_three_le_card (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  by_contra! h
  have hs : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
    intro t
    by_cases ht : t = 0
    · exact ⟨false, by simp [ht]⟩
    · exact ⟨true, by simp [h t ht]⟩
  have hcard := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
  omega

/-- Every simple-root subgroup of the local finite-field F₄ adjoint group is
contained in its derived subgroup when the field has at least three elements.
This ports the root-level step in the external F₄ perfectness proof. -/
theorem simpleRootSubgroup_le_commutator_F4 (K : Type*) [Field K]
    (i : Fin (Tag.rank .F4)) (hK : 3 ≤ Nat.card K) :
    rootSubgroup .F4 K (Pi.single i 1) ≤
      (commutator ↥(adjointGroup .F4 K)).map (adjointGroup .F4 K).subtype := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_three_le_card K hK
  obtain ⟨l, hil, hli⟩ := exists_symmetric_simple_neighbor_F4 i
  exact simpleRootSubgroup_le_commutator_of_neighbor .F4 K i l hil hli
    (Units.mk0 t ht0) ht1

/-- Every simple-root subgroup of the local finite-field E₈ adjoint group is
contained in its derived subgroup when the field has at least three elements.
This ports the root-level step in the external E₈ perfectness proof. -/
theorem simpleRootSubgroup_le_commutator_E8 (K : Type*) [Field K]
    (i : Fin (Tag.rank .E8)) (hK : 3 ≤ Nat.card K) :
    rootSubgroup .E8 K (Pi.single i 1) ≤
      (commutator ↥(adjointGroup .E8 K)).map (adjointGroup .E8 K).subtype := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_three_le_card K hK
  obtain ⟨l, hil, hli⟩ := exists_symmetric_simple_neighbor_E8 i
  exact simpleRootSubgroup_le_commutator_of_neighbor .E8 K i l hil hli
    (Units.mk0 t ht0) ht1

/-- Every simple-root subgroup of the local finite-field E₆ adjoint group is
contained in its derived subgroup when the field has at least three elements.
This ports the root-level step in the external E₆ perfectness proof. -/
theorem simpleRootSubgroup_le_commutator_E6 (K : Type*) [Field K]
    (i : Fin (Tag.rank .E6)) (hK : 3 ≤ Nat.card K) :
    rootSubgroup .E6 K (Pi.single i 1) ≤
      (commutator ↥(adjointGroup .E6 K)).map (adjointGroup .E6 K).subtype := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_three_le_card K hK
  obtain ⟨l, hil, hli⟩ := exists_symmetric_simple_neighbor_E6 i
  exact simpleRootSubgroup_le_commutator_of_neighbor .E6 K i l hil hli
    (Units.mk0 t ht0) ht1

/-- Every simple-root subgroup of the local finite-field E₇ adjoint group is
contained in its derived subgroup when the field has at least three elements.
This ports the root-level step in the external E₇ perfectness proof. -/
theorem simpleRootSubgroup_le_commutator_E7 (K : Type*) [Field K]
    (i : Fin (Tag.rank .E7)) (hK : 3 ≤ Nat.card K) :
    rootSubgroup .E7 K (Pi.single i 1) ≤
      (commutator ↥(adjointGroup .E7 K)).map (adjointGroup .E7 K).subtype := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_three_le_card K hK
  obtain ⟨l, hil, hli⟩ := exists_symmetric_simple_neighbor_E7 i
  exact simpleRootSubgroup_le_commutator_of_neighbor .E7 K i l hil hli
    (Units.mk0 t ht0) ht1

/-- Every simple-root subgroup of the local finite-field D₄ adjoint group is
contained in its derived subgroup when the field has at least three elements.
-/
theorem simpleRootSubgroup_le_commutator_D4 (K : Type*) [Field K]
    (i : Fin (Tag.rank .D4)) (hK : 3 ≤ Nat.card K) :
    rootSubgroup .D4 K (Pi.single i 1) ≤
      (commutator ↥(adjointGroup .D4 K)).map (adjointGroup .D4 K).subtype := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_three_le_card K hK
  obtain ⟨l, hil, hli⟩ := exists_symmetric_simple_neighbor_D4 i
  exact simpleRootSubgroup_le_commutator_of_neighbor .D4 K i l hil hli
    (Units.mk0 t ht0) ht1

/-- If every simple-root subgroup lies in the derived subgroup, then every
pinned root subgroup does too: each pinned root element is a Weyl conjugate of
a simple-root element, and the derived subgroup is normal. -/
theorem rootSubgroup_le_commutator_of_simpleRoots (τ : Tag) (K : Type*) [Field K]
    (hsimple : ∀ i : Fin τ.rank,
      rootSubgroup τ K (Pi.single i 1) ≤
        (commutator ↥(adjointGroup τ K)).map (adjointGroup τ K).subtype)
    (α : Fin τ.rank → ℤ) :
    rootSubgroup τ K α ≤
      (commutator ↥(adjointGroup τ K)).map (adjointGroup τ K).subtype := by
  let A := adjointGroup τ K
  let D : Subgroup ↥A := commutator ↥A
  have hDnormal : D.Normal := by infer_instance
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  let i := (pinnedData τ α).1
  let ε := (pinnedData τ α).2.2
  let w : ↥A := ⟨pinnedWeyl τ K α, pinnedWeyl_mem_adjointGroup α⟩
  let x : ↥A := ⟨xUnit τ K i (ε • c), xUnit_mem_adjointGroup i _⟩
  have hxroot : xUnit τ K i (ε • c) ∈ rootSubgroup τ K (Pi.single i 1) := by
    rw [← pinnedX_single τ K i (ε • c)]
    exact Subgroup.subset_closure ⟨ε • c, rfl⟩
  have hxmap : (x : (Module.End K (RootModule τ K))ˣ) ∈ D.map A.subtype :=
    hsimple i hxroot
  have hx : x ∈ D := by
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxmap
    have hEq : y = x := A.subtype_injective hxy
    simpa [hEq] using hy
  have hconj : w * x * w⁻¹ ∈ D := hDnormal.conj_mem x hx w
  refine ⟨w * x * w⁻¹, hconj, ?_⟩
  simp [w, x, pinnedX, i, ε]

/-- Every pinned F₄ root subgroup lies in the derived subgroup when the field
has at least three elements. -/
theorem rootSubgroup_le_commutator_F4 (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) (α : Fin (Tag.rank .F4) → ℤ) :
    rootSubgroup .F4 K α ≤
      (commutator ↥(adjointGroup .F4 K)).map (adjointGroup .F4 K).subtype := by
  exact rootSubgroup_le_commutator_of_simpleRoots .F4 K
    (fun i => simpleRootSubgroup_le_commutator_F4 K i hK) α

/-- Every pinned E₈ root subgroup lies in the derived subgroup when the field
has at least three elements. -/
theorem rootSubgroup_le_commutator_E8 (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) (α : Fin (Tag.rank .E8) → ℤ) :
    rootSubgroup .E8 K α ≤
      (commutator ↥(adjointGroup .E8 K)).map (adjointGroup .E8 K).subtype := by
  exact rootSubgroup_le_commutator_of_simpleRoots .E8 K
    (fun i => simpleRootSubgroup_le_commutator_E8 K i hK) α

/-- Every pinned E₆ root subgroup lies in the derived subgroup when the field
has at least three elements. -/
theorem rootSubgroup_le_commutator_E6 (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) (α : Fin (Tag.rank .E6) → ℤ) :
    rootSubgroup .E6 K α ≤
      (commutator ↥(adjointGroup .E6 K)).map (adjointGroup .E6 K).subtype := by
  exact rootSubgroup_le_commutator_of_simpleRoots .E6 K
    (fun i => simpleRootSubgroup_le_commutator_E6 K i hK) α

/-- Every pinned E₇ root subgroup lies in the derived subgroup when the field
has at least three elements. -/
theorem rootSubgroup_le_commutator_E7 (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) (α : Fin (Tag.rank .E7) → ℤ) :
    rootSubgroup .E7 K α ≤
      (commutator ↥(adjointGroup .E7 K)).map (adjointGroup .E7 K).subtype := by
  exact rootSubgroup_le_commutator_of_simpleRoots .E7 K
    (fun i => simpleRootSubgroup_le_commutator_E7 K i hK) α

/-- Every pinned D₄ root subgroup lies in the derived subgroup when the field
has at least three elements. -/
theorem rootSubgroup_le_commutator_D4 (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) (α : Fin (Tag.rank .D4) → ℤ) :
    rootSubgroup .D4 K α ≤
      (commutator ↥(adjointGroup .D4 K)).map (adjointGroup .D4 K).subtype := by
  exact rootSubgroup_le_commutator_of_simpleRoots .D4 K
    (fun i => simpleRootSubgroup_le_commutator_D4 K i hK) α

/-- Every simple root of the G₂ Cartan matrix has an odd Cartan pairing with
some simple coroot. -/
theorem exists_odd_cartan_G2 (i : Fin (Tag.rank .G2)) :
    ∃ l, Odd (Tag.cartan .G2 l i) := by
  fin_cases i
  · exact ⟨⟨1, by decide⟩, ⟨-2, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨-1, by decide⟩⟩

/-- The inverse of the local G₂ Cartan matrix, needed for the external
Steinberg-normalizer argument. -/
def cartanInvG2 : Matrix (Fin (Tag.rank .G2)) (Fin (Tag.rank .G2)) ℤ :=
  !![2, 1; 3, 2]

theorem cartan_mul_cartanInvG2 : Tag.cartan .G2 * cartanInvG2 = 1 := by
  decide +kernel

/-- The local G₂ Cartan matrix is indecomposable, matching the hypothesis in
the external Tits quasisimplicity criterion. -/
theorem isIndecomposable_cartan_G2 : IsIndecomposable (Tag.cartan .G2) := by
  decide +kernel

/-- An involution raised to an odd integer power is itself. -/
theorem zpow_eq_self_of_sq_eq_one {G : Type*} [Group G] {u : G}
    (hu : u ^ 2 = 1) {n : ℤ} (hn : Odd n) : u ^ n = u := by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add, zpow_mul, zpow_one, zpow_ofNat, hu, one_zpow, one_mul]

/-- Each simple-root subgroup of the finite-field G₂ adjoint group lies in its
derived subgroup when the field has at least three elements. -/
theorem simpleRootSubgroup_le_commutator_G2 (K : Type*) [Field K]
    (i : Fin (Tag.rank .G2)) (hK : 3 ≤ Nat.card K) :
    rootSubgroup .G2 K (Pi.single i 1) ≤
      (commutator ↥(adjointGroup .G2 K)).map (adjointGroup .G2 K).subtype := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_three_le_card K hK
  let u : Kˣ := Units.mk0 t ht0
  have hpair (l : Fin (Tag.rank .G2)) :
      (∑ j, Tag.cartan .G2 l j *
        (Pi.single i (1 : ℤ) : Fin (Tag.rank .G2) → ℤ) j) = Tag.cartan .G2 l i := by
    simp [Pi.single_apply]
  by_cases h2 : t ^ 2 = 1
  · have hu : u ^ 2 = 1 := Units.ext (by simp [u, h2])
    obtain ⟨l, hl⟩ := exists_odd_cartan_G2 i
    have hw : (((u ^ Tag.cartan .G2 l i : Kˣ) : K) ≠ 1) := by
      have heq : ((u ^ Tag.cartan .G2 l i : Kˣ) : K) = t := by
        rw [zpow_eq_self_of_sq_eq_one hu hl, Units.val_mk0]
      rw [heq]
      exact ht1
    have hw' :
        (((u ^ (∑ j, Tag.cartan .G2 l j *
          (Pi.single i (1 : ℤ) : Fin (Tag.rank .G2) → ℤ) j) : Kˣ) : K) ≠ 1) := by
      simpa only [hpair] using hw
    exact rootSubgroup_le_commutator_of_torus (isRoot_single .G2 i) l u hw'
  · have hw : (((u ^ Tag.cartan .G2 i i : Kˣ) : K) ≠ 1) := by
      rw [Tag.cartan_self, zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_mk0]
      exact h2
    have hw' :
        (((u ^ (∑ j, Tag.cartan .G2 i j *
          (Pi.single i (1 : ℤ) : Fin (Tag.rank .G2) → ℤ) j) : Kˣ) : K) ≠ 1) := by
      simpa only [hpair] using hw
    exact rootSubgroup_le_commutator_of_torus (isRoot_single .G2 i) i u hw'

/-- Every pinned root subgroup of the G₂ adjoint group lies in its derived
subgroup. The pinned-root definition expresses each generator as a conjugate
of a simple-root generator by an element of the adjoint group. -/
theorem rootSubgroup_le_commutator_G2 (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) (α : Fin (Tag.rank .G2) → ℤ) :
    rootSubgroup .G2 K α ≤
      (commutator ↥(adjointGroup .G2 K)).map (adjointGroup .G2 K).subtype := by
  let A := adjointGroup .G2 K
  let D : Subgroup ↥A := commutator ↥A
  have hDnormal : D.Normal := by infer_instance
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  let i := (pinnedData .G2 α).1
  let ε := (pinnedData .G2 α).2.2
  let w : ↥A := ⟨pinnedWeyl .G2 K α, pinnedWeyl_mem_adjointGroup α⟩
  let x : ↥A := ⟨xUnit .G2 K i (ε • c), xUnit_mem_adjointGroup i _⟩
  have hxroot : xUnit .G2 K i (ε • c) ∈ rootSubgroup .G2 K (Pi.single i 1) := by
    rw [← pinnedX_single .G2 K i (ε • c)]
    exact Subgroup.subset_closure ⟨ε • c, rfl⟩
  have hxmap : (x : (Module.End K (RootModule .G2 K))ˣ) ∈
      D.map A.subtype :=
    simpleRootSubgroup_le_commutator_G2 K i hK hxroot
  have hx : x ∈ D := by
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxmap
    have hEq : y = x := A.subtype_injective hxy
    simpa [hEq] using hy
  have hconj : w * x * w⁻¹ ∈ D := hDnormal.conj_mem x hx w
  refine ⟨w * x * w⁻¹, hconj, ?_⟩
  simp [w, x, pinnedX, i, ε]

/-- The certified G₂ root set is reduced: twice a root is never a root. -/
theorem not_isRoot_double_G2 {α : Fin (Tag.rank .G2) → ℤ}
    (hα : IsRoot .G2 α) : ¬ IsRoot .G2 (2 • α) := by
  intro h2
  obtain ⟨i, hi, rfl⟩ :=
    RootCertificate.exists_root_eq Certificates.certificate113.1 hα
  obtain ⟨j, hj, hjroot⟩ :=
    RootCertificate.exists_root_eq Certificates.certificate113.1 h2
  have hnone : ∀ i < 12, ∀ j < 12,
      g2Certificate.root j ≠ 2 • g2Certificate.root i := by decide +kernel
  exact hnone i (by simpa [g2Certificate] using hi)
    j (by simpa [g2Certificate] using hj) hjroot

/-- The local D₄ root system is reduced: twice a root is never a root. -/
theorem not_isRoot_double_D4 {α : Fin (Tag.rank .D4) → ℤ}
    (hα : IsRoot .D4 α) : ¬ IsRoot .D4 (2 • α) := by
  intro h2
  obtain ⟨i, hi, rfl⟩ :=
    RootCertificate.exists_root_eq Certificates.certificate113.2.2.1 hα
  obtain ⟨j, hj, hjroot⟩ :=
    RootCertificate.exists_root_eq Certificates.certificate113.2.2.1 h2
  have hnone : ∀ i < 24, ∀ j < 24,
      d4Certificate.root j ≠ 2 • d4Certificate.root i := by decide +kernel
  exact hnone i (by simpa [d4Certificate] using hi)
    j (by simpa [d4Certificate] using hj) hjroot

/-- Every root system in the local exceptional Chevalley catalog is reduced.
The proof uses the checked finite root certificates, while the statement is
about the inductively generated root predicate. -/
theorem not_isRoot_double (τ : Tag) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : ¬ IsRoot τ (2 • α) := by
  intro h2
  obtain ⟨i, hi, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  obtain ⟨j, hj, hjroot⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check h2
  have hnone : ∀ i < τ.rootCertificate.roots.length,
      ∀ j < τ.rootCertificate.roots.length,
        τ.rootCertificate.root j ≠ 2 • τ.rootCertificate.root i := by
    cases τ <;> decide +kernel
  exact hnone i hi j hj hjroot

/-- Local operator-carrier version of the `two_smul_le` field in the
external CFSG `SteinbergExtras` interface. The local exceptional root
certificates are reduced, so the field's doubled-root hypothesis is
impossible. -/
theorem rootSubgroup_two_smul_le (τ : Tag) (K : Type*) [Field K]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h2 : IsRoot τ (2 • α)) :
    rootSubgroup τ K (2 • α) ≤ rootSubgroup τ K α := by
  exact (not_isRoot_double τ hα h2).elim

/-- Root-group commutator data in the local Chevalley model, mirroring the
three clauses used by the external CFSG Tits-simplicity criterion. -/
structure RootGroupCommutatorData (τ : Tag) (K : Type*) [CommRing K] : Prop where
  commutator_le : ∀ α, IsRoot τ α → IsRoot τ (2 • α) →
    ⁅rootSubgroup τ K α, rootSubgroup τ K α⁆ ≤ rootSubgroup τ K (2 • α)
  commutator_eq_bot : ∀ α, IsRoot τ α → ¬ IsRoot τ (2 • α) →
    ⁅rootSubgroup τ K α, rootSubgroup τ K α⁆ = ⊥
  commutator_two_smul_eq_bot : ∀ α, IsRoot τ α → IsRoot τ (2 • α) →
    ⁅rootSubgroup τ K α, rootSubgroup τ K (2 • α)⁆ = ⊥

/-- The local pinned root groups satisfy CFSG's root-group commutator
interface in type G₂. The third clause is vacuous by the checked root
certificate, since this root system is reduced. -/
theorem rootGroupCommutatorData_G2 (K : Type*) [Field K] :
    RootGroupCommutatorData .G2 K where
  commutator_le := by
    intro α _ _
    rw [commutator_rootSubgroup_self_eq_bot .G2 K α]
    exact bot_le
  commutator_eq_bot := by
    intro α _ _
    exact commutator_rootSubgroup_self_eq_bot .G2 K α
  commutator_two_smul_eq_bot := by
    intro α hα h2
    exact (not_isRoot_double_G2 hα h2).elim

/-- The local D₄ pinned root groups satisfy the self-commutator interface;
the mixed doubled-root clause is vacuous because the D₄ root system is reduced.
-/
theorem rootGroupCommutatorData_D4 (K : Type*) [Field K] :
    RootGroupCommutatorData .D4 K where
  commutator_le := by
    intro α _ _
    rw [commutator_rootSubgroup_self_eq_bot .D4 K α]
    exact bot_le
  commutator_eq_bot := by
    intro α _ _
    exact commutator_rootSubgroup_self_eq_bot .D4 K α
  commutator_two_smul_eq_bot := by
    intro α hα h2
    exact (not_isRoot_double_D4 hα h2).elim

/-- The local pinned root operators satisfy the root-group commutator
interface uniformly for G₂, F₄, D₄, E₆, E₇, and E₈. Each individual root
subgroup is abelian inside the actual endomorphism-unit group, and the checked
root certificates establish that no doubled root occurs. -/
theorem rootGroupCommutatorData_all (τ : Tag) (K : Type*) [Field K] :
    RootGroupCommutatorData τ K where
  commutator_le := by
    intro α hα h2
    exact (not_isRoot_double τ hα h2).elim
  commutator_eq_bot := by
    intro α _ _
    exact commutator_rootSubgroup_self_eq_bot τ K α
  commutator_two_smul_eq_bot := by
    intro α hα h2
    exact (not_isRoot_double τ hα h2).elim

/-- Every exceptional adjoint Chevalley group is nontrivial: a nonzero
parameter in a simple-root subgroup gives a nonidentity pinned root element. -/
theorem nontrivial_adjointGroup (τ : Tag) (K : Type*) [Field K] :
    Nontrivial ↥(adjointGroup τ K) := by
  let i : Fin τ.rank := ⟨0, τ.rank_pos⟩
  let α : Fin τ.rank → ℤ := Pi.single i 1
  have hx : pinnedX τ K α 1 ≠ 1 := by
    intro h
    have h10 : (1 : K) = 0 :=
      (pinnedX_injective τ K α) (h.trans (pinnedX_zero τ K α).symm)
    exact one_ne_zero h10
  let x : ↥(adjointGroup τ K) :=
    ⟨pinnedX τ K α 1, pinnedX_mem_adjointGroup α 1⟩
  exact nontrivial_of_ne x 1 fun h => hx (congrArg Subtype.val h)

/-- The finite-field G₂ adjoint group is nontrivial. -/
theorem nontrivial_adjointGroup_G2 (K : Type*) [Field K] :
    Nontrivial ↥(adjointGroup .G2 K) :=
  nontrivial_adjointGroup .G2 K

/-- If every pinned root subgroup of an adjoint Chevalley group lies in its
derived subgroup, then the adjoint group is perfect, since those root
subgroups generate it. -/
theorem isPerfect_adjointGroup_of_rootSubgroups_le_commutator (τ : Tag) (K : Type*)
    [Field K]
    (hroot : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      rootSubgroup τ K α ≤
        (commutator ↥(adjointGroup τ K)).map (adjointGroup τ K).subtype) :
    Group.IsPerfect ↥(adjointGroup τ K) := by
  let D : Subgroup ↥(adjointGroup τ K) := commutator ↥(adjointGroup τ K)
  have hspan : rootSpan τ K {α | IsRoot τ α} ≤
      D.map (adjointGroup τ K).subtype := by
    refine iSup₂_le fun α hα => ?_
    exact hroot α hα
  have hderived : adjointGroup τ K ≤
      D.map (adjointGroup τ K).subtype := by
    intro g hg
    rw [adjointGroup_eq_rootSpan] at hg
    exact hspan hg
  have hEq : D.map (adjointGroup τ K).subtype = adjointGroup τ K :=
    le_antisymm (Subgroup.map_subtype_le _) hderived
  apply Subgroup.isPerfect_iff.mpr
  calc
    ⁅adjointGroup τ K, adjointGroup τ K⁆ =
        D.map (adjointGroup τ K).subtype :=
      (Subgroup.map_subtype_commutator (adjointGroup τ K)).symm
    _ = adjointGroup τ K := hEq

/-- The local F₄ adjoint group is perfect for fields of cardinality at least
three. This ports the root-group generation step of the external proof. -/
theorem isPerfect_adjointGroup_F4_of_three_le_card (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) : Group.IsPerfect ↥(adjointGroup .F4 K) := by
  exact isPerfect_adjointGroup_of_rootSubgroups_le_commutator .F4 K
    (fun α _hα => rootSubgroup_le_commutator_F4 K hK α)

/-- The local E₈ adjoint group is perfect for fields of cardinality at least
three. This ports the root-group generation step of the external proof. -/
theorem isPerfect_adjointGroup_E8_of_three_le_card (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) : Group.IsPerfect ↥(adjointGroup .E8 K) := by
  exact isPerfect_adjointGroup_of_rootSubgroups_le_commutator .E8 K
    (fun α _hα => rootSubgroup_le_commutator_E8 K hK α)

/-- The local E₆ adjoint group is perfect for fields of cardinality at least
three. -/
theorem isPerfect_adjointGroup_E6_of_three_le_card (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) : Group.IsPerfect ↥(adjointGroup .E6 K) := by
  exact isPerfect_adjointGroup_of_rootSubgroups_le_commutator .E6 K
    (fun α _hα => rootSubgroup_le_commutator_E6 K hK α)

/-- The local E₇ adjoint group is perfect for fields of cardinality at least
three. -/
theorem isPerfect_adjointGroup_E7_of_three_le_card (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) : Group.IsPerfect ↥(adjointGroup .E7 K) := by
  exact isPerfect_adjointGroup_of_rootSubgroups_le_commutator .E7 K
    (fun α _hα => rootSubgroup_le_commutator_E7 K hK α)

/-- The local D₄ adjoint group is perfect for fields of cardinality at least
three. -/
theorem isPerfect_adjointGroup_D4_of_three_le_card (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) : Group.IsPerfect ↥(adjointGroup .D4 K) := by
  exact isPerfect_adjointGroup_of_rootSubgroups_le_commutator .D4 K
    (fun α _hα => rootSubgroup_le_commutator_D4 K hK α)

/-- The finite-field G₂ adjoint group is perfect for fields of cardinality at
least three. This is the perfectness half of the external quasisimplicity
argument. -/
theorem isPerfect_adjointGroup_G2_of_three_le_card (K : Type*) [Field K]
    (hK : 3 ≤ Nat.card K) : Group.IsPerfect ↥(adjointGroup .G2 K) := by
  exact isPerfect_adjointGroup_of_rootSubgroups_le_commutator .G2 K
    (fun α _hα => rootSubgroup_le_commutator_G2 K hK α)

end InfoGeometry.Exceptional.CFSGPort.Chevalley

end
