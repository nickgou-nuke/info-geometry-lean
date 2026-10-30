/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Check.lean and RootOps/Instance.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseNormalize
public import InfoGeometry.Exceptional.CFSGPort.RootOperatorData.G2
public import InfoGeometry.Exceptional.CFSGPort.RootOperatorData.F4
public import InfoGeometry.Exceptional.CFSGPort.RootOperatorData.D4
public import InfoGeometry.Exceptional.CFSGPort.RootOperatorData.E6
public import InfoGeometry.Exceptional.CFSGPort.RootOperatorData.E7
public import InfoGeometry.Exceptional.CFSGPort.RootOperatorData.E8

/-! # Decoding and index validity of the external exceptional operator tables -/

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

@[expose] def codes : Tag → ℕ → List ℕ
  | .G2, 1 => g2Codes1
  | .G2, 2 => g2Codes2
  | .G2, 3 => g2Codes3
  | .F4, 1 => f4Codes1
  | .F4, 2 => f4Codes2
  | .F4, 3 => f4Codes3
  | .D4, 1 => d4Codes1
  | .D4, 2 => d4Codes2
  | .D4, 3 => d4Codes3
  | .E6, 1 => e6Codes1
  | .E6, 2 => e6Codes2
  | .E6, 3 => e6Codes3
  | .E7, 1 => e7Codes1
  | .E7, 2 => e7Codes2
  | .E7, 3 => e7Codes3
  | .E8, 1 => e8Codes1
  | .E8, 2 => e8Codes2
  | .E8, 3 => e8Codes3
  | _, _ => []

@[expose] def signCodes : Tag → List ℕ
  | .G2 => g2Signs
  | .F4 => f4Signs
  | .D4 => d4Signs
  | .E6 => e6Signs
  | .E7 => e7Signs
  | .E8 => e8Signs

@[expose] def entries (τ : Tag) (a k : ℕ) : List Entry :=
  decodeEntries 128 ((codes τ k).getD a 0)

@[expose] def signOf (τ : Tag) (a : ℕ) (i : Fin τ.rank) : ℤ :=
  if (signCodes τ).getD a 0 / 2 ^ (i : ℕ) % 2 = 1 then -1 else 1

theorem signOf_eq (τ : Tag) (a : ℕ) (i : Fin τ.rank) : signOf τ a i = 1 ∨ signOf τ a i = -1 := by
  unfold signOf
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

@[expose] def validB (τ : Tag) (L : List Entry) : Bool :=
  L.all fun e => decide (e.1 < dim τ) && decide (e.2.1 < dim τ)

theorem validEntries_of_validB {τ : Tag} {L : List Entry} (h : validB τ L = true) :
    ValidEntries τ L := by
  intro e he
  simp only [validB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h e he

@[expose] def allValid (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun a =>
    [1, 2, 3].all fun k => validB τ (entries τ a k)

variable {τ : Tag}

theorem validB_of_allValid (h : allValid τ = true) {a : ℕ}
    (ha : a < τ.rootCertificate.roots.length) {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    validB τ (entries τ a k) = true := by
  simp only [allValid, List.all_eq_true, List.mem_range] at h
  exact h a ha k hk

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
