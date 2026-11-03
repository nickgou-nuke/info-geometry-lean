/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The deterministic search grid `S = {0, ..., d}` inside `ZMod p`. -/
def xiHankelDeterministicGrid (p d : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Finset.range (d + 1)).image fun n : ℕ => (n : ZMod p)

lemma xiHankelDeterministicGrid_card {p d : ℕ} [Fact p.Prime] (hpd : d < p) :
    (xiHankelDeterministicGrid p d).card = d + 1 := by
  classical
  unfold xiHankelDeterministicGrid
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb hab
    have hab' : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hab
    have ha_lt : a < p := lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_of_lt hpd)
    have hb_lt : b < p := lt_of_lt_of_le (Finset.mem_range.mp hb) (Nat.succ_le_of_lt hpd)
    rw [Nat.ModEq, Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hab'
    exact hab'

/-- Finite-field data for a nonzero determinant polynomial together with an output function.
The output function is independent data; its graph alone defines `completionEq`. -/
structure XiHankelFinitefieldDeterministicCompletionData
    (p d δ : Nat) [Fact p.Prime] where
  detPolynomial : MvPolynomial (Fin δ) (ZMod p)
  totalDegree_le : detPolynomial.totalDegree ≤ d
  detPolynomial_ne_zero : detPolynomial ≠ 0
  extensionValue : (Fin δ → ZMod p) → ZMod p

namespace XiHankelFinitefieldDeterministicCompletionData

def onGrid {p d δ : Nat} [Fact p.Prime]
    (_D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) : Prop :=
  ∀ i, x i ∈ xiHankelDeterministicGrid p d

def detPoly {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) : ZMod p :=
  MvPolynomial.eval x D.detPolynomial

def completionEq {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ)
    (x : Fin δ → ZMod p) (y : ZMod p) : Prop :=
  y = D.extensionValue x

def uniqueExtension {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) : Prop :=
  ∃! y : ZMod p, D.completionEq x y

lemma uniqueExtension_of_graph {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) :
    D.uniqueExtension x := by
  refine ⟨D.extensionValue x, rfl, ?_⟩
  intro y hy
  simpa [completionEq] using hy

lemma exists_grid_point_detPoly_ne_zero {p d δ : Nat} [Fact p.Prime] (hpd : d < p)
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) :
    ∃ x : Fin δ → ZMod p, D.onGrid x ∧ D.detPoly x ≠ 0 := by
  classical
  by_contra h
  apply D.detPolynomial_ne_zero
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset
    (P := D.detPolynomial) (S := fun _ : Fin δ => xiHankelDeterministicGrid p d)
  · intro i
    have hdeg_le : D.detPolynomial.degreeOf i ≤ d :=
      (MvPolynomial.degreeOf_le_totalDegree D.detPolynomial i).trans D.totalDegree_le
    have hdeg_lt : D.detPolynomial.degreeOf i < d + 1 :=
      lt_of_le_of_lt hdeg_le (Nat.lt_succ_self d)
    simpa [xiHankelDeterministicGrid_card hpd] using hdeg_lt
  · intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩

end XiHankelFinitefieldDeterministicCompletionData

open XiHankelFinitefieldDeterministicCompletionData

/-- Paper label: `prop:xi-hankel-finitefield-deterministic-completion`.

This proves existence of a nonvanishing grid evaluation and uniqueness for the
declared graph relation only. It does not derive an extension from Hankel data;
`xiHankel_completion_graph_does_not_determine_output` exhibits the gap. -/
theorem paper_xi_hankel_finitefield_deterministic_completion {p d δ : Nat} [Fact p.Prime]
    (hpd : d < p) (D : XiHankelFinitefieldDeterministicCompletionData p d δ) :
    ∃ x : Fin δ → ZMod p, D.onGrid x ∧ D.detPoly x ≠ 0 ∧ D.uniqueExtension x := by
  rcases D.exists_grid_point_detPoly_ne_zero hpd with ⟨x, hxGrid, hxDet⟩
  exact ⟨x, hxGrid, hxDet, D.uniqueExtension_of_graph x⟩

/-- The graph-based uniqueness field does not determine an extension from the determinant data:
two data records with the same nonzero polynomial and degree bound can have different unique
outputs because `extensionValue` is unconstrained. -/
theorem xiHankel_completion_graph_does_not_determine_output {p d δ : Nat} [Fact p.Prime]
    (hpd : d < p) (P : MvPolynomial (Fin δ) (ZMod p))
    (hdegree : P.totalDegree ≤ d) (hP : P ≠ 0) :
    ∃ x : Fin δ → ZMod p,
      (let Dzero : XiHankelFinitefieldDeterministicCompletionData p d δ :=
        ⟨P, hdegree, hP, fun _ => 0⟩
       let Done : XiHankelFinitefieldDeterministicCompletionData p d δ :=
        ⟨P, hdegree, hP, fun _ => 1⟩
       Dzero.onGrid x ∧ Dzero.detPoly x ≠ 0 ∧ Dzero.uniqueExtension x ∧
         Done.onGrid x ∧ Done.detPoly x ≠ 0 ∧ Done.uniqueExtension x ∧
         Dzero.extensionValue x ≠ Done.extensionValue x) := by
  let Dzero : XiHankelFinitefieldDeterministicCompletionData p d δ :=
    ⟨P, hdegree, hP, fun _ => 0⟩
  let Done : XiHankelFinitefieldDeterministicCompletionData p d δ :=
    ⟨P, hdegree, hP, fun _ => 1⟩
  obtain ⟨x, hxGrid, hxDet⟩ := Dzero.exists_grid_point_detPoly_ne_zero hpd
  refine ⟨x, hxGrid, hxDet, Dzero.uniqueExtension_of_graph x,
    ?_, ?_, Done.uniqueExtension_of_graph x, ?_⟩
  · exact hxGrid
  · simpa [Done, detPoly] using hxDet
  · norm_num

end Omega.Zeta
