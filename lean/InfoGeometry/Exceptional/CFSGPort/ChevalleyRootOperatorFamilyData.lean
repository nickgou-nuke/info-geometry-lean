/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local port of CFSG/LieType/Chevalley/RootOps/Instance.lean and CertTools.lean.
The coefficient family and its proof fields follow those owners; only the
root carrier and checked sparse-table theorem names are adapted locally.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorFamily
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorValidity

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

theorem exists_rootPos {τ : Tag} (α : RootCarrier τ) :
    ∃ a, a < τ.rootCertificate.roots.length ∧ τ.rootCertificate.root a = α.1 :=
  RootCertificate.exists_root_eq τ.rootCertificate_check α.2

open _root_.Classical in
/-- Canonical certificate index for a root, matching the external `rootPos`. -/
def rootPos {τ : Tag} (α : RootCarrier τ) : ℕ := Nat.find (exists_rootPos α)

theorem rootPos_lt {τ : Tag} (α : RootCarrier τ) :
    rootPos α < τ.rootCertificate.roots.length :=
  (Nat.find_spec (exists_rootPos α)).1

theorem root_rootPos {τ : Tag} (α : RootCarrier τ) :
    τ.rootCertificate.root (rootPos α) = α.1 :=
  (Nat.find_spec (exists_rootPos α)).2

theorem rootPos_eq {τ : Tag} {α : RootCarrier τ} {a : ℕ}
    (ha : a < τ.rootCertificate.roots.length)
    (h : τ.rootCertificate.root a = α.1) : rootPos α = a :=
  root_index_injective (rootPos_lt α) ha ((root_rootPos α).trans h.symm)

theorem rootPos_simpleRoot {τ : Tag} (j : Fin τ.rank) :
    rootPos (⟨Pi.single j 1, IsRoot.basis j⟩ : RootCarrier τ) = j := by
  obtain ⟨hr, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  exact rootPos_eq (lt_of_lt_of_le j.2 hr) (hb j)

theorem rootPos_neg_simpleRoot {τ : Tag} (j : Fin τ.rank) :
    rootPos (⟨-Pi.single j 1, isRoot_neg_single τ j⟩ : RootCarrier τ) =
      τ.rootCertificate.image j j := by
  obtain ⟨hr, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have hj : (j : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le j.2 hr
  refine rootPos_eq (rootCertificate_image_lt hj j) ?_
  rw [rootCertificate_root_image hj, hb j, reflect_single_self]

theorem rootPos_reflect {τ : Tag} (i : Fin τ.rank) (α : RootCarrier τ) :
    rootPos ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩ =
      τ.rootCertificate.image (rootPos α) i := by
  refine rootPos_eq (rootCertificate_image_lt (rootPos_lt α) i) ?_
  rw [rootCertificate_root_image (rootPos_lt α), root_rootPos]

/-- The local data obligations required by the external root-operator family
instance, stated on the local checked root-module operators. -/
structure DataChecks (τ : Tag) : Prop where
  tab : tabCheck τ = true
  valid : allValid τ = true
  conj : ∀ a < τ.rootCertificate.roots.length, ∀ (i : Fin τ.rank), ∀ k ∈ [1, 2, 3],
    conjCheck τ a i k = true
  simple : ∀ (R : Type*) [CommRing R] (j : Fin τ.rank) (k : ℕ), 1 ≤ k → k ≤ 3 →
    entriesOp τ R (entries τ j k) = xCoeff τ R j k
  negSimple : ∀ (R : Type*) [CommRing R] (j : Fin τ.rank) (k : ℕ), 1 ≤ k → k ≤ 3 →
    entriesOp τ R (entries τ (τ.rootCertificate.image j j) k) = yCoeff τ R j k

theorem mem_one_two_three {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3) : k ∈ [1, 2, 3] := by
  interval_cases k <;> simp

theorem dataChecks_of {τ : Tag} (htab : tabCheck τ = true)
    (hvalid : allValid τ = true)
    (hconj : conjRange τ 0 τ.rootCertificate.roots.length = true)
    (hsimple : ∀ j : Fin τ.rank, Mirror.simpleRow τ j = true) : DataChecks τ where
  tab := htab
  valid := hvalid
  conj a ha i k hk := conjRange_spec hconj (Nat.zero_le a) ha i hk
  simple R _ j k h1 h3 :=
    (Mirror.entriesOp_eq_simpleRootCoefficients (τ := τ) (R := R) j
      (mem_one_two_three h1 h3)).1
  negSimple R _ j k h1 h3 :=
    (Mirror.entriesOp_eq_simpleRootCoefficients (τ := τ) (R := R) j
      (mem_one_two_three h1 h3)).2

@[expose] def dataD (τ : Tag) (R : Type*) [CommRing R] (α : RootCarrier τ) (k : ℕ) :
    Module.End R (RootModule τ R) :=
  if k = 0 then 1 else if k ≤ 3 then entriesOp τ R (entries τ (rootPos α) k) else 0

@[expose] noncomputable def DataChecks.family {τ : Tag} (h : DataChecks τ) :
    RootOperatorFamily τ where
  D := dataD τ
  D_zero R _ α := by simp [dataD]
  D_eq_zero R _ α k hk := by
    unfold dataD
    simp only [show k ≠ 0 by omega, show ¬ k ≤ 3 by omega, ↓reduceIte]
  D_simple R _ j k := by
    unfold dataD
    rw [rootPos_simpleRoot]
    split_ifs with h0 h3
    · subst h0
      exact (xCoeff_zero j).symm
    · exact h.simple R j k (by omega) h3
    · exact (xCoeff_eq_zero j (by omega)).symm
  D_neg_simple R _ j k := by
    unfold dataD
    rw [rootPos_neg_simpleRoot]
    split_ifs with h0 h3
    · subst h0
      exact (yCoeff_zero j).symm
    · exact h.negSimple R j k (by omega) h3
    · exact (yCoeff_eq_zero j (by omega)).symm
  sign i α := signOf τ (rootPos α) i
  sign_eq i α := signOf_eq τ (rootPos α) i
  conj R _ i α k := by
    unfold dataD
    split_ifs with h0 h3
    · subst h0
      simp
    · have hk : k ∈ [1, 2, 3] := mem_one_two_three (by omega) h3
      rw [rootPos_reflect]
      exact conj_of_conjCheck (h.conj (rootPos α) (rootPos_lt α) i k hk)
    · simp

theorem conjRange_tag : ∀ τ : Tag,
    conjRange τ 0 τ.rootCertificate.roots.length = true
  | .G2 => by simpa [Tag.rootCertificate, g2Certificate] using conjRange_G2
  | .F4 => by simpa [Tag.rootCertificate, f4Certificate] using conjRange_F4
  | .D4 => by simpa [Tag.rootCertificate, d4Certificate] using conjRange_D4
  | .E6 => by simpa [Tag.rootCertificate, e6Certificate] using conjRange_E6
  | .E7 => by simpa [Tag.rootCertificate, e7Certificate] using conjRange_E7
  | .E8 => by
      simpa only [Tag.rootCertificate_length, Tag.rootCount] using conjRange_E8

@[expose] noncomputable def rootOperatorFamilyData (τ : Tag) : RootOperatorFamily τ :=
  (dataChecks_of (tabCheck_tag τ) (allValid_tag τ) (conjRange_tag τ)
    (fun j => Mirror.simpleRow_eq_true τ j)).family

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
