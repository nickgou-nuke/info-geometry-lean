import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Dadarlat (2009) — finite algebraic K-theory readout

This file keeps only the Lean-owned algebraic surface used downstream:
square-closed additive subgroups of `ℚ` and explicit proof-carrying data for an
abelian group to be additively equivalent to such a subgroup.

It does not prove the analytic C*-algebra classification theorem, UCT input,
Ext-vanishing, or Kirchberg absorption.  Those are external mathematical
hypotheses which must be supplied before this finite algebraic readout applies.
-/

open Classical

noncomputable section

namespace InfoGeometry.KTheory.Dadarlat

/--
A subgroup H ≤ Q is *square-closed* if for all n : ℤ, n ≠ 0,
  1/n ∈ H  →  1/n² ∈ H.
-/
def IsSquareClosed (H : AddSubgroup ℚ) : Prop :=
  ∀ (n : ℤ), n ≠ 0 → ((n : ℚ)⁻¹ ∈ H → ((n : ℚ)⁻¹)^2 ∈ H)

theorem top_squareClosed : IsSquareClosed (⊤ : AddSubgroup ℚ) := by
  intro n hn h
  simp

theorem inv_mem_closure_singleton (p : ℕ) :
    (p : ℚ)⁻¹ ∈ AddSubgroup.closure ({(p : ℚ)⁻¹} : Set ℚ) := by
  exact AddSubgroup.subset_closure (by simp)

/-- Proof-carrying algebraic data for the rational-subgroup branch. -/
structure RationalK0Branch (G : Type*) [AddCommGroup G] where
  H : AddSubgroup ℚ
  equiv : G ≃+ H
  squareClosed : IsSquareClosed H

/--
Conservative Lean-owned replacement for the old theorem-shaped socket.

The deep Dadarlat hypotheses are not reconstructed here.  Instead, this structure
stores the actual finite algebraic consequences needed in this repository:
torsion freeness, a distinguished nonzero element, and an explicit rational
subgroup branch.
-/
structure TorsionFreeWithUnit (G : Type*) [AddCommGroup G] where
  e : G
  he_ne_zero : e ≠ 0
  torsionFree : ∀ (x : G), ∀ (n : ℕ), n ≠ 0 → n • x = 0 → x = 0
  rationalBranch : RationalK0Branch G

lemma torsion_free_of_uct (G : Type*) [AddCommGroup G] (h : TorsionFreeWithUnit G) :
    ∀ (x : G), ∀ (n : ℕ), n ≠ 0 → n • x = 0 → x = 0 :=
  h.torsionFree

def gammaMap {G : Type*} [AddCommGroup G] (data : TorsionFreeWithUnit G) :
    G →+ ℚ :=
  (data.rationalBranch.H.subtype).comp data.rationalBranch.equiv.toAddMonoidHom

theorem gammaMap_apply {G : Type*} [AddCommGroup G] (data : TorsionFreeWithUnit G)
    (x : G) :
    gammaMap data x = data.rationalBranch.equiv x := rfl

theorem gammaMap_injective {G : Type*} [AddCommGroup G] (data : TorsionFreeWithUnit G) :
    Function.Injective (gammaMap data) := by
  intro x y hxy
  apply data.rationalBranch.equiv.injective
  apply Subtype.ext
  exact hxy

theorem rationalBranch_squareClosed {G : Type*} [AddCommGroup G]
    (data : TorsionFreeWithUnit G) :
    IsSquareClosed data.rationalBranch.H :=
  data.rationalBranch.squareClosed

/--
Algebraic classification readout from the explicit rational branch.
-/
theorem classification_of_k0
    {G : Type*} [AddCommGroup G] (data : TorsionFreeWithUnit G) :
    (∃ (f : G ≃+ ℤ), f data.e = 1) ∨
    (∃ (H : AddSubgroup ℚ) (_ : G ≃+ H), IsSquareClosed H) := by
  exact Or.inr
    ⟨data.rationalBranch.H, data.rationalBranch.equiv, data.rationalBranch.squareClosed⟩

/-- Finite symbolic targets for the three standard Kirchberg classification branches. -/
inductive KirchbergModel where
  | O2
  | OInfinity
  | OInfinityTensorUHF

/-- Explicit classification data for a named algebra object. -/
structure AutomaticTrivialityClassification (D : Type*) where
  model : KirchbergModel

theorem automatic_triviality_classification
    (D : Type*) (C : AutomaticTrivialityClassification D) :
    C.model = KirchbergModel.O2 ∨
      C.model = KirchbergModel.OInfinity ∨
      C.model = KirchbergModel.OInfinityTensorUHF := by
  cases C.model <;> simp

end InfoGeometry.KTheory.Dadarlat
