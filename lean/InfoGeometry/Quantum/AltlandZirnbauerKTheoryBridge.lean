/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge

/-!
# Altland-Zirnbauer symmetry-class index

This module defines the ten symmetry-class labels and gives an exact bijection
between those labels and the valid `(T², C², S)` presence/sign signatures.  The
signature is finite combinatorial data; it does not construct antiunitary
operators or classify Hamiltonians, stable phases, or `KO` groups.

The remaining theorem targets are independent:

* define the class-D Pfaffian bulk invariant and identify it with the signs of
  the Pfaffians at the particle-hole invariant momenta;
* construct stable gapped phases and prove the one-dimensional class-D
  homotopy classification;
* define the half-space boundary index and prove bulk-boundary equality;
* construct real `KO` groups and prove the genuine degree-eight Bott
  equivalence.

No spectral sequence or Fredholm model is part of the bare Bott-equivalence
statement; either may later be used as proof machinery or a realization.
-/

/-- The ten Altland-Zirnbauer symmetry-class labels. -/
inductive AZClass : Type
  | A
  | AIII
  | AI
  | BDI
  | D
  | DIII
  | AII
  | CII
  | C
  | CI
  deriving DecidableEq, Repr

/-- Square sign of an antiunitary symmetry (`T²` or `C²`), or `absent` when the
symmetry is not present. -/
inductive SymSquareSign : Type
  | absent
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Exact algebraic symmetry signature `(T², C², S)` of an Altland–Zirnbauer class. -/
structure AZSignature : Type where
  T_sq : SymSquareSign
  C_sq : SymSquareSign
  hasS : Bool
  deriving DecidableEq, Repr

/-- Compatibility predicate characterizing the ten valid `(T², C², S)` signatures:
1. Both `T` and `C` present forces chiral symmetry `S` (`hasS = true`);
2. Exactly one of `T` or `C` present forces `hasS = false`;
3. Neither present allows both `hasS = false` (`A`) and `hasS = true` (`AIII`). -/
def AZSignature.IsValid (s : AZSignature) : Prop :=
  (s.T_sq ≠ .absent → s.C_sq ≠ .absent → s.hasS = true) ∧
  (s.T_sq ≠ .absent → s.C_sq = .absent → s.hasS = false) ∧
  (s.T_sq = .absent → s.C_sq ≠ .absent → s.hasS = false)

instance : DecidablePred AZSignature.IsValid := fun s =>
  inferInstanceAs (Decidable
    ((s.T_sq ≠ .absent → s.C_sq ≠ .absent → s.hasS = true) ∧
     (s.T_sq ≠ .absent → s.C_sq = .absent → s.hasS = false) ∧
     (s.T_sq = .absent → s.C_sq ≠ .absent → s.hasS = false)))

/-- Canonical map from the ten Altland–Zirnbauer labels to `(T², C², S)` signatures. -/
def azSignature : AZClass → AZSignature
  | .A    => ⟨.absent, .absent, false⟩
  | .AIII => ⟨.absent, .absent, true⟩
  | .AI   => ⟨.plus,   .absent, false⟩
  | .BDI  => ⟨.plus,   .plus,   true⟩
  | .D    => ⟨.absent, .plus,   false⟩
  | .DIII => ⟨.minus,  .plus,   true⟩
  | .AII  => ⟨.minus,  .absent, false⟩
  | .CII  => ⟨.minus,  .minus,  true⟩
  | .C    => ⟨.absent, .minus,  false⟩
  | .CI   => ⟨.plus,   .minus,  true⟩

theorem azSignature_injective : Function.Injective azSignature := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

theorem azSignature_isValid (c : AZClass) : (azSignature c).IsValid := by
  cases c <;> simp [azSignature, AZSignature.IsValid]

/-- Constructive inverse from valid `(T², C², S)` signatures back to `AZClass`. -/
def ofValidSignature (s : { s : AZSignature // s.IsValid }) : AZClass :=
  match hs : s.1 with
  | ⟨.absent, .absent, false⟩ => .A
  | ⟨.absent, .absent, true⟩  => .AIII
  | ⟨.plus,   .absent, false⟩ => .AI
  | ⟨.plus,   .plus,   true⟩  => .BDI
  | ⟨.absent, .plus,   false⟩ => .D
  | ⟨.minus,  .plus,   true⟩  => .DIII
  | ⟨.minus,  .absent, false⟩ => .AII
  | ⟨.minus,  .minus,  true⟩  => .CII
  | ⟨.absent, .minus,  false⟩ => .C
  | ⟨.plus,   .minus,  true⟩  => .CI
  | ⟨.plus,   .absent, true⟩  => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.2.1 (by decide) rfl) (by decide)
  | ⟨.minus,  .absent, true⟩  => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.2.1 (by decide) rfl) (by decide)
  | ⟨.absent, .plus,   true⟩  => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.2.2 rfl (by decide)) (by decide)
  | ⟨.absent, .minus,  true⟩  => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.2.2 rfl (by decide)) (by decide)
  | ⟨.plus,   .plus,   false⟩ => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.1 (by decide) (by decide)) (by decide)
  | ⟨.minus,  .plus,   false⟩ => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.1 (by decide) (by decide)) (by decide)
  | ⟨.minus,  .minus,  false⟩ => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.1 (by decide) (by decide)) (by decide)
  | ⟨.plus,   .minus,  false⟩ => False.elim <| by
      have hv := s.2
      rw [hs] at hv
      exact absurd (hv.1 (by decide) (by decide)) (by decide)

/-- Exact 10-class bijection `AZClass ≃ { s : AZSignature // s.IsValid }`. -/
def azClassEquivValidSignature : AZClass ≃ { s : AZSignature // s.IsValid } where
  toFun c := ⟨azSignature c, azSignature_isValid c⟩
  invFun := ofValidSignature
  left_inv c := by
    cases c <;> rfl
  right_inv := by
    rintro ⟨⟨t, c, b⟩, hv⟩
    apply Subtype.ext
    cases t <;> cases c <;> cases b <;>
      first
      | rfl
      | exfalso; norm_num [AZSignature.IsValid] at hv

theorem azSignature_surjective_on_valid (s : { s : AZSignature // s.IsValid }) :
    ∃ c : AZClass, azSignature c = s.1 :=
  ⟨azClassEquivValidSignature.symm s, congrArg Subtype.val (azClassEquivValidSignature.apply_symm_apply s)⟩

instance instFintypeAZClass : Fintype AZClass where
  elems := {.A, .AIII, .AI, .BDI, .D, .DIII, .AII, .CII, .C, .CI}
  complete c := by cases c <;> simp

theorem azClass_card : Fintype.card AZClass = 10 := by
  decide

noncomputable instance instFintypeValidAZSignature : Fintype { s : AZSignature // s.IsValid } :=
  Fintype.ofEquiv AZClass azClassEquivValidSignature

theorem validAZSignature_card : Fintype.card { s : AZSignature // s.IsValid } = 10 := by
  rw [Fintype.card_congr azClassEquivValidSignature.symm, azClass_card]

end InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
