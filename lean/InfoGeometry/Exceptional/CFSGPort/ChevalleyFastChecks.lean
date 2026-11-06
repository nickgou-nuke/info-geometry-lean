/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Check.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastWeylTables

/-! # Soundness of sparse column checks for Weyl conjugation -/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

@[expose] def colCheck (τ : Tag) (i : Fin τ.rank) (L L' : List Entry)
    (s : ℤ) (c : ℕ) : Bool :=
  normalize (nVecL τ i (colOf L c)) ==
    normalize ((applyL L' (nPos τ i c)).map fun x => (x.1, s * x.2))

theorem colCheck_spec {i : Fin τ.rank} {L L' : List Entry} {s : ℤ} {c : ℕ}
    (hL : ValidEntries τ L) (hc : c < dim τ)
    (h : colCheck τ i L L' s c = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R))
        (entriesOp τ R L (posVec τ R c)) =
      (s : R) • entriesOp τ R L'
        ((weylElt τ R i 1 : Module.End R (RootModule τ R)) (posVec τ R c)) := by
  rw [entriesOp_posVec L hc, weylElt_vecOf i (hL.colOf c), weylElt_posVec i hc,
    entriesOp_vecOf L' (validVec_nPos i hc), ← vecOf_map_mul]
  have hnorm : normalize (nVecL τ i (colOf L c)) =
      normalize ((applyL L' (nPos τ i c)).map fun x => (x.1, s * x.2)) :=
    beq_iff_eq.mp h
  exact vecOf_eq_of_normalize_eq hnorm

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

@[expose] def conjCheckAux (τ : Tag) (i : Fin τ.rank) (L L' : List Entry)
    (s : ℤ) : Bool :=
  validB τ L &&
    ((List.range τ.rank).all fun c => colCheck τ i L L' s c) &&
    (L.all fun e => decide (e.1 < τ.rank) || colCheck τ i L L' s e.1) &&
    (L'.all fun e => decide (e.1 < τ.rank) ||
      L.any fun f => f.1 == τ.rank + τ.rootCertificate.image (e.1 - τ.rank) i)

theorem conj_of_conjCheckAux {i : Fin τ.rank} {L L' : List Entry} {s : ℤ}
    (h : conjCheckAux τ i L L' s = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R L =
      (s : R) • (entriesOp τ R L' *
        (weylElt τ R i 1 : Module.End R (RootModule τ R))) := by
  simp only [conjCheckAux, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hv, hh⟩, hcols⟩, hsupp⟩ := h
  have hL := validEntries_of_validB hv
  refine ext_posVec fun c hc => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply]
  by_cases hcr : c < τ.rank
  · exact colCheck_spec hL hc (hh c hcr)
  by_cases hmem : ∃ e ∈ L, e.1 = c
  · obtain ⟨e, he, rfl⟩ := hmem
    exact colCheck_spec hL hc ((hcols e he).resolve_left hcr)
  push Not at hmem
  have hcolL : colOf L c = [] := by
    simp only [colOf, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
    exact hmem
  have hm : c - τ.rank < τ.rootCertificate.roots.length := by
    rw [dim_eq] at hc
    omega
  have hcolL' : colOf L' (τ.rank + τ.rootCertificate.image (c - τ.rank) i) = [] := by
    simp only [colOf, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
    intro e he hec
    rcases hsupp e he with hlt | ⟨f, hf, hfc⟩
    · omega
    · refine hmem f hf ?_
      rw [hfc, hec, Nat.add_sub_cancel_left, rootCertificate_image_image hm]
      omega
  rw [entriesOp_posVec L hc, hcolL, vecOf_nil, map_zero, weylElt_posVec i hc]
  simp only [nPos, hcr, ↓reduceDIte]
  rw [vecOf_cons, vecOf_nil, add_zero, map_smul, entriesOp_posVec L', hcolL',
    vecOf_nil, smul_zero, smul_zero]
  have him := rootCertificate_image_lt hm i
  rw [dim_eq] at hc
  simp only [dim]
  omega


set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[expose] def conjCheck (τ : Tag) (a : ℕ) (i : Fin τ.rank) (k : ℕ) : Bool :=
  conjCheckAux τ i (entries τ a k)
    (entries τ (τ.rootCertificate.image a i) k) (signOf τ a i ^ k)

theorem conj_of_conjCheck {a : ℕ} {i : Fin τ.rank} {k : ℕ}
    (h : conjCheck τ a i k = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) *
        entriesOp τ R (entries τ a k) =
      ((signOf τ a i ^ k : ℤ) : R) •
        (entriesOp τ R (entries τ (τ.rootCertificate.image a i) k) *
          (weylElt τ R i 1 : Module.End R (RootModule τ R))) :=
  conj_of_conjCheckAux h


@[expose] def conjRange (τ : Tag) (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun a =>
    (List.finRange τ.rank).all fun i => [1, 2, 3].all fun k => conjCheck τ a i k

/-- Transfer two adjacent checked root-table ranges to their union. -/
theorem conjRange_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : conjRange τ a b = true) (h₂ : conjRange τ b c = true) :
    conjRange τ a c = true := by
  simp only [conjRange, List.all_eq_true, List.mem_range'] at h₁ h₂ ⊢
  rintro x ⟨m, hm, rfl⟩
  by_cases hx : a + m < b
  · exact h₁ _ ⟨m, by omega, rfl⟩
  · exact h₂ _ ⟨a + m - b, by omega, by omega⟩

private theorem conjRange_join3 {a b c d : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (h₁ : conjRange τ a b = true)
    (h₂ : conjRange τ b c = true) (h₃ : conjRange τ c d = true) :
    conjRange τ a d = true := by
  exact conjRange_trans (a := a) (b := c) (c := d) (Nat.le_trans hab hbc) hcd
    (conjRange_trans (a := a) (b := b) (c := c) hab hbc h₁ h₂) h₃

private theorem conjRange_join4 {a b c d e : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hde : d ≤ e) (h₁ : conjRange τ a b = true)
    (h₂ : conjRange τ b c = true) (h₃ : conjRange τ c d = true)
    (h₄ : conjRange τ d e = true) : conjRange τ a e = true := by
  exact conjRange_trans (a := a) (b := d) (c := e)
    (Nat.le_trans hab (Nat.le_trans hbc hcd)) hde
    (conjRange_join3 (a := a) (b := b) (c := c) (d := d)
      hab hbc hcd h₁ h₂ h₃) h₄

private theorem conjRange_join7 {a b c d e f g h : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (hef : e ≤ f) (hfg : f ≤ g) (hgh : g ≤ h)
    (h₁ : conjRange τ a b = true) (h₂ : conjRange τ b c = true)
    (h₃ : conjRange τ c d = true) (h₄ : conjRange τ d e = true)
    (h₅ : conjRange τ e f = true) (h₆ : conjRange τ f g = true)
    (h₇ : conjRange τ g h = true) : conjRange τ a h = true := by
  have hAE := conjRange_join4 (a := a) (b := b) (c := c) (d := d) (e := e)
    hab hbc hcd hde h₁ h₂ h₃ h₄
  have hEH := conjRange_join3 (a := e) (b := f) (c := g) (d := h)
    hef hfg hgh h₅ h₆ h₇
  exact conjRange_trans (a := a) (b := e) (c := h) (by omega) (by omega) hAE hEH

theorem conjRange_spec {lo hi : ℕ} (h : conjRange τ lo hi = true)
    {a : ℕ} (ha : lo ≤ a) (ha' : a < hi) (i : Fin τ.rank) {k : ℕ}
    (hk : k ∈ [1, 2, 3]) : conjCheck τ a i k = true := by
  simp only [conjRange, List.all_eq_true, List.mem_range', List.mem_finRange,
    true_implies] at h
  exact h a ⟨a - lo, by omega, by omega⟩ i k hk

theorem conjRange_G2 : conjRange .G2 0 12 = true := by decide +kernel
theorem conjRange_D4 : conjRange .D4 0 24 = true := by decide +kernel

private theorem conjRange_F4_0_24 : conjRange .F4 0 24 = true := by decide +kernel
private theorem conjRange_F4_24_48 : conjRange .F4 24 48 = true := by decide +kernel

theorem conjRange_F4 : conjRange .F4 0 48 = true := by
  exact conjRange_trans (by omega) (by omega)
    conjRange_F4_0_24 conjRange_F4_24_48

private theorem conjRange_E6_0_18 : conjRange .E6 0 18 = true := by decide +kernel
private theorem conjRange_E6_18_36 : conjRange .E6 18 36 = true := by decide +kernel
private theorem conjRange_E6_36_54 : conjRange .E6 36 54 = true := by decide +kernel
private theorem conjRange_E6_54_72 : conjRange .E6 54 72 = true := by decide +kernel

theorem conjRange_E6 : conjRange .E6 0 72 = true := by
  exact conjRange_join4 (by omega) (by omega) (by omega) (by omega)
    conjRange_E6_0_18 conjRange_E6_18_36 conjRange_E6_36_54 conjRange_E6_54_72

private theorem conjRange_E7_0_18 : conjRange .E7 0 18 = true := by decide +kernel
private theorem conjRange_E7_18_36 : conjRange .E7 18 36 = true := by decide +kernel
private theorem conjRange_E7_36_54 : conjRange .E7 36 54 = true := by decide +kernel
private theorem conjRange_E7_54_72 : conjRange .E7 54 72 = true := by decide +kernel
private theorem conjRange_E7_72_90 : conjRange .E7 72 90 = true := by decide +kernel
private theorem conjRange_E7_90_108 : conjRange .E7 90 108 = true := by decide +kernel
private theorem conjRange_E7_108_126 : conjRange .E7 108 126 = true := by decide +kernel

theorem conjRange_E7 : conjRange .E7 0 126 = true := by
  exact conjRange_join7 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    conjRange_E7_0_18 conjRange_E7_18_36 conjRange_E7_36_54
    conjRange_E7_54_72 conjRange_E7_72_90 conjRange_E7_90_108
    conjRange_E7_108_126

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
