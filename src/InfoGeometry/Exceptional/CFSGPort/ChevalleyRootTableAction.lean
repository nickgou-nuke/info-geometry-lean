/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG Chevalley/BraidWalk.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootBasis
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyWeyl

/-! # Checked root-table reflection and Weyl-sign data -/

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag}

theorem rootCertificate_basis_table :
    τ.rank ≤ τ.rootCertificate.roots.length ∧
      (∀ j : Fin τ.rank, τ.rootCertificate.root j = Pi.single j 1) ∧
      ∀ k < τ.rootCertificate.roots.length, ∀ i : Fin τ.rank,
        τ.rootCertificate.image k i < τ.rootCertificate.roots.length ∧
          τ.rootCertificate.root (τ.rootCertificate.image k i) =
            reflect τ i (τ.rootCertificate.root k) := by
  have h := τ.rootCertificate_check
  simp only [RootCertificate.check, RootCertificate.checkBasis, RootCertificate.checkTable,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, List.mem_range,
    true_implies] at h
  exact ⟨h.1.1.1, fun j => RootCertificate.eq_of_ofFn_beq (h.1.1.2 j),
    fun k hk i => ⟨(h.2 k hk i).1, RootCertificate.eq_of_ofFn_beq (h.2 k hk i).2⟩⟩

theorem rootCertificate_image_lt {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : τ.rootCertificate.image k i < τ.rootCertificate.roots.length :=
  (rootCertificate_basis_table.2.2 k hk i).1

theorem rootCertificate_root_image {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    τ.rootCertificate.root (τ.rootCertificate.image k i) =
      reflect τ i (τ.rootCertificate.root k) :=
  (rootCertificate_basis_table.2.2 k hk i).2

/-- The checked root-index action of a simple reflection is involutive. -/
theorem rootCertificate_image_image {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : τ.rootCertificate.image (τ.rootCertificate.image k i) i = k := by
  have hk' := rootCertificate_image_lt hk i
  have hk'' := rootCertificate_image_lt hk' i
  exact root_index_injective hk'' hk (by
    calc
      τ.rootCertificate.root (τ.rootCertificate.image (τ.rootCertificate.image k i) i) =
          reflect τ i (τ.rootCertificate.root (τ.rootCertificate.image k i)) :=
        rootCertificate_root_image hk' i
      _ = reflect τ i (reflect τ i (τ.rootCertificate.root k)) := by
        rw [rootCertificate_root_image hk i]
      _ = τ.rootCertificate.root k := reflect_reflect τ i _)

theorem isRoot_rootCertificate_root {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    IsRoot τ (τ.rootCertificate.root k) :=
  RootCertificate.isRoot_root τ.rootCertificate_check k hk

@[expose] def downAt (τ : Tag) (k : ℕ) (i : Fin τ.rank) : ℕ :=
  if k = i then 2 else if k = τ.rootCertificate.image i i then 0 else τ.stringData.down k i

theorem stringDown_rootCertificate_root {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : stringDown τ i (τ.rootCertificate.root k) = downAt τ k i := by
  obtain ⟨hr, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have hi : (i : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le i.2 hr
  have hneg : τ.rootCertificate.root (τ.rootCertificate.image i i) = -Pi.single i 1 := by
    rw [rootCertificate_root_image hi, hb, reflect_single_self]
  unfold downAt
  split_ifs with h₁ h₂
  · rw [h₁, hb, stringDown_single]
  · rw [h₂, hneg, stringDown_neg_single]
  have hne : τ.rootCertificate.root k ≠ Pi.single i 1 := fun h =>
    h₁ (root_index_injective hk hi (h.trans (hb i).symm))
  have hne' : τ.rootCertificate.root k ≠ -Pi.single i 1 := fun h =>
    h₂ (root_index_injective hk (rootCertificate_image_lt hi i) (h.trans hneg.symm))
  obtain ⟨-, hS⟩ := StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk
    i hne hne'
  obtain ⟨-, hΦ⟩ := isRoot_add_smul_single_iff (isRoot_rootCertificate_root hk) i hne hne'
  have h1 := (hS _).1 ((hΦ (-(stringDown τ i (τ.rootCertificate.root k) : ℤ))).2
    ⟨le_rfl, by omega⟩)
  have h2 := (hΦ _).1 ((hS (-(τ.stringData.down k i : ℤ))).2 ⟨le_rfl, by omega⟩)
  omega

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
