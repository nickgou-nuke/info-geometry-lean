/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PositiveGrassmannianBCFWCells
import InfoGeometry.Canonical.YangianExteriorSupercharge

/-!
# Finite momentum-twistor data and exterior bilocal operators

This module reuses the canonical strict external-data predicate and the
exterior-algebra bilocal operator. It records the transpose convention and
guards maximal-minor positivity against empty index families. Its collinearity
result is a finite operator vanishing theorem; it does not define a
Grassmannian quotient, a Yangian algebra or representation, or a general
amplitude-invariance theorem.
-/

namespace InfoGeometry.Canonical.Amplituhedron

open InfoGeometry.Canonical
open InfoGeometry.Canonical.YangianExteriorSupercharge
open Matrix

variable {k n : ℕ}

/-- Row-oriented external twistor matrices whose transpose has strictly
positive ordered maximal minors, using the canonical BCFW convention. -/
abbrev MomentumTwistorData (k n : ℕ) :=
  {Z : Matrix (Fin n) (Fin (k + 4)) ℝ //
    k + 4 ≤ n ∧
      IsTotallyPositiveData (k := k) (n := n) (m := 4) Z.transpose}

/-- The dimension bound in `MomentumTwistorData` makes the strict-minor
condition substantive: there is an ordered maximal minor, and it is positive. -/
theorem momentumTwistorData_has_positive_maximal_minor
    (Z : MomentumTwistorData k n) :
    ∃ s : Fin (k + 4) → Fin n, StrictMono s ∧
      0 < (Z.1.transpose.submatrix id s).det := by
  let s : Fin (k + 4) → Fin n := fun i =>
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt Z.2.1⟩
  have hs : StrictMono s := by
    intro i j hij
    exact Fin.mk_lt_mk.mpr hij
  exact ⟨s, hs, Z.2.2 s hs⟩

/-! ### Finite exterior-algebra bilocal consequence -/

/-- Every ordered pair of twistor rows is proportional. -/
def PairwiseCollinear (z : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ i j : Fin n, i < j → ∃ c : ℝ, ∀ a : Fin 4, z j a = c * z i a

/-- Proportional rows have zero antisymmetric twistor minor. -/
theorem twistorMinor_eq_zero_of_pairwiseCollinear
    (z : Fin n → Fin 4 → ℝ) (hz : PairwiseCollinear z)
    (a b : Fin 4) (i j : Fin n) (hij : i < j) :
    twistorMinor n z a b i j = 0 := by
  obtain ⟨c, hc⟩ := hz i j hij
  unfold twistorMinor
  rw [hc a, hc b]
  ring

/-- Under pairwise row collinearity, every ordered bilocal term vanishes. -/
theorem bilocalTerm_eq_zero_of_pairwiseCollinear
    (z : Fin n → Fin 4 → ℝ) (hz : PairwiseCollinear z)
    (a b A B : Fin 4) (i j : Fin n) (hij : i < j) :
    bilocalTerm n z a b A B i j = 0 := by
  unfold bilocalTerm
  rw [twistorMinor_eq_zero_of_pairwiseCollinear z hz a b i j hij]
  simp

/-- If every ordered pair of twistor rows is proportional, the finite
bilocal operator in the existing exterior-contraction model is zero. -/
theorem levelOneSupercharge_eq_zero_of_pairwiseCollinear
    (z : Fin n → Fin 4 → ℝ) (hz : PairwiseCollinear z)
    (a b A B : Fin 4) :
    levelOneSupercharge n z a b A B = 0 := by
  unfold levelOneSupercharge
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : i < j
  · simpa [hij] using
      bilocalTerm_eq_zero_of_pairwiseCollinear z hz a b A B i j hij
  · simp [hij]

end InfoGeometry.Canonical.Amplituhedron
