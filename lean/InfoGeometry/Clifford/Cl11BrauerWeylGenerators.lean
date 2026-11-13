/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SplitAtomDoubling.Basic
import Mathlib.Logic.Pairwise

/-!
# Adjoining a split pair to noncommutative generator families

The input family can have any index type and coefficients in any ring. Its
ordered square and anticommutator relations are transported to the existing
`SplitAtomDoubling.Block2` carrier. This is a theorem about generator relations;
it does not identify a presented Clifford algebra with a full matrix algebra.

The owner's `negative = !![0, 1; -1, 0]` is the negative of the intake's
`Ω = !![0, -1; 1, 0]`. This sign change preserves its square and all zero
anticommutators. No characteristic or invertibility-of-two assumption is used.
-/

namespace InfoGeometry.Clifford.Cl11BrauerWeylGenerators

open SplitAtomDoubling

section Extension

variable {A : Type*} [Ring A] {ι : Type*}

/-- The existing positive- and negative-square block generators. -/
def splitPair : Fin 2 → Block2 A := ![positive, negative]

/-- The square values of a split pair, in any coefficient ring. -/
def splitSquares : Fin 2 → A := ![1, -1]

theorem splitPair_square (i : Fin 2) :
    splitPair (A := A) i * splitPair i = splitSquares i := by
  fin_cases i
  · simp [splitPair, splitSquares]
  · simp [splitPair, splitSquares]

theorem splitPair_pairwise :
    Pairwise fun i j : Fin 2 =>
      splitPair (A := A) i * splitPair j + splitPair j * splitPair i = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa [splitPair] using (head_anticommutator (A := A))
  · simpa [splitPair, add_comm] using (head_anticommutator (A := A))
  · exact (hij rfl).elim

/-- Adjoin two outer generators and twist each generator of the old family. -/
def adjoinFamily (g : ι → A) : Fin 2 ⊕ ι → Block2 A :=
  Sum.elim splitPair (fun i => twisted (g i))

/-- Old square values are sent through the genuine repeated-diagonal embedding. -/
def adjoinSquares (s : ι → A) : Fin 2 ⊕ ι → Block2 A :=
  Sum.elim splitSquares (fun i => repeated (s i))

/-- The construction preserves each prescribed square, with two new split signs. -/
theorem adjoinFamily_square (g : ι → A) (s : ι → A)
    (hg : ∀ i, g i * g i = s i) (i : Fin 2 ⊕ ι) :
    adjoinFamily g i * adjoinFamily g i = adjoinSquares s i := by
  cases i with
  | inl i => exact splitPair_square i
  | inr i =>
      change twisted (g i) * twisted (g i) = repeated (s i)
      rw [twisted_mul, hg i]

/-- Every distinct pair anticommutes, including the new/old cross terms. -/
theorem adjoinFamily_pairwise (g : ι → A)
    (hg : Pairwise fun i j => g i * g j + g j * g i = 0) :
    Pairwise fun i j : Fin 2 ⊕ ι =>
      adjoinFamily g i * adjoinFamily g j +
        adjoinFamily g j * adjoinFamily g i = 0 := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          apply splitPair_pairwise
          exact fun h => hij (congrArg Sum.inl h)
      | inr j =>
          fin_cases i
          · simpa [adjoinFamily, splitPair, add_comm] using
              (twisted_positive_anticommutator (g j))
          · simpa [adjoinFamily, splitPair, add_comm] using
              (twisted_negative_anticommutator (g j))
  | inr i =>
      cases j with
      | inl j =>
          fin_cases j
          · simpa [adjoinFamily, splitPair] using
              (twisted_positive_anticommutator (g i))
          · simpa [adjoinFamily, splitPair] using
              (twisted_negative_anticommutator (g i))
      | inr j =>
          have hij' : i ≠ j := fun h => hij (congrArg Sum.inr h)
          change twisted (g i) * twisted (g j) +
            twisted (g j) * twisted (g i) = 0
          rw [twisted_anticommutator, hg hij']
          exact repeatedHom.map_zero

end Extension

section TwoSites

variable {B : Type*} [Ring B]

/-- Four nested generators: two outer operators and two Klein-twisted inner ones. -/
def fourGenerators : Fin 2 ⊕ Fin 2 → Block2 (Block2 B) :=
  adjoinFamily (splitPair (A := B))

/-- Their square values in the order outer positive/negative, inner positive/negative. -/
def fourSquares : Fin 2 ⊕ Fin 2 → Block2 (Block2 B) :=
  Sum.elim splitSquares splitSquares

/-- The two-stage family has square pattern `(+1, -1, +1, -1)`. -/
theorem fourGenerators_square (i : Fin 2 ⊕ Fin 2) :
    fourGenerators (B := B) i * fourGenerators i = fourSquares i := by
  calc
    fourGenerators (B := B) i * fourGenerators i =
        adjoinSquares (splitSquares (A := Block2 B)) i :=
      adjoinFamily_square (splitPair (A := B))
        (splitSquares (A := Block2 B)) (splitPair_square (A := B)) i
    _ = fourSquares i := by
      cases i with
      | inl i => rfl
      | inr i =>
          fin_cases i
          · change repeated (1 : Block2 B) = 1
            exact repeatedHom.map_one
          · change repeated (-1 : Block2 B) = -1
            change repeatedHom (-1 : Block2 B) = -1
            simp

/-- Pairwise anticommutation of all four matrices, over arbitrary ring coefficients. -/
theorem fourGenerators_pairwise :
    Pairwise fun i j : Fin 2 ⊕ Fin 2 =>
      fourGenerators (B := B) i * fourGenerators j +
        fourGenerators j * fourGenerators i = 0 :=
  adjoinFamily_pairwise (splitPair (A := B)) (splitPair_pairwise (A := B))

end TwoSites

end InfoGeometry.Clifford.Cl11BrauerWeylGenerators
