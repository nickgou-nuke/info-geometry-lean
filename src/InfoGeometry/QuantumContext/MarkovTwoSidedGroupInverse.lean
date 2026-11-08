/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift

/-!
# Group inverse of a two-sided matrix action

The left-regular Markov lift and the four-corner matrix action are separately
available in the QuantumContext owners. This module proves the intervening
operator theorem: the sandwich endomorphism `X ↦ A * (X * B)` has group inverse
`X ↦ G * (X * H)` whenever `G` and `H` are group inverses of `A` and `B`.
The Markov specialization acts on the full, generally noncommutative matrix
module. It is a sandwich action, not the Lyapunov sum or a quantum channel.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovTwoSidedGroupInverse

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Independent group inverses on the left and right factors induce a group
inverse for the two-sided sandwich endomorphism of the full matrix module. -/
theorem cornerMap_groupInverse
    (A B G H : MatrixCarrier (ι := ι))
    (hA : IsGroupInverse A G) (hB : IsGroupInverse B H) :
    IsGroupInverse (cornerMap A B) (cornerMap G H) := by
  constructor
  · calc
      cornerMap A B * cornerMap G H * cornerMap A B =
          cornerMap ((A * G) * A) (B * (H * B)) := by
            rw [cornerMap_mul, cornerMap_mul]
      _ = cornerMap A B := by rw [hA.1, ← mul_assoc, hB.1]
  constructor
  · calc
      cornerMap G H * cornerMap A B * cornerMap G H =
          cornerMap ((G * A) * G) (H * (B * H)) := by
            rw [cornerMap_mul, cornerMap_mul]
      _ = cornerMap G H := by rw [hA.2.1, ← mul_assoc, hB.2.1]
  · calc
      cornerMap A B * cornerMap G H = cornerMap (A * G) (H * B) := cornerMap_mul _ _ _ _
      _ = cornerMap (G * A) (B * H) := by rw [hA.2.2, hB.2.2]
      _ = cornerMap G H * cornerMap A B := (cornerMap_mul _ _ _ _).symm

/-- For a Markov Laplacian with matrix group inverse `G`, the full-matrix
sandwich action has group inverse given by sandwiching with `G` on both sides. -/
theorem markovSandwich_groupInverse
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G) :
    IsGroupInverse (cornerMap (1 - P) (1 - P)) (cornerMap G G) :=
  cornerMap_groupInverse ((1 : MatrixCarrier (ι := ι)) - P)
    ((1 : MatrixCarrier (ι := ι)) - P) G G hG hG

/-- The two-sided group inverse recovers every matrix in the image of its
Markov sandwich operator. -/
theorem markovSandwich_recovers_on_range
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G)
    (X : MatrixCarrier (ι := ι))
    (hX : X ∈ (cornerMap ((1 : MatrixCarrier (ι := ι)) - P)
      ((1 : MatrixCarrier (ι := ι)) - P)).range) :
    cornerMap G G
      (cornerMap ((1 : MatrixCarrier (ι := ι)) - P)
        ((1 : MatrixCarrier (ι := ι)) - P) X) = X := by
  obtain ⟨Y, hY⟩ := LinearMap.mem_range.mp hX
  rw [← hY]
  let a : MatrixEnd (ι := ι) := cornerMap (1 - P) (1 - P)
  let g : MatrixEnd (ι := ι) := cornerMap G G
  have hLift : IsGroupInverse a g := by
    simpa [a, g] using markovSandwich_groupInverse P G hG
  calc
    g (a (a Y)) = (g * a) (a Y) := by simp [Module.End.mul_eq_comp]
    _ = (a * g) (a Y) := by rw [hLift.2.2]
    _ = ((a * g) * a) Y := by simp [Module.End.mul_eq_comp]
    _ = a Y := congrArg (fun F : MatrixEnd (ι := ι) => F Y) hLift.1

/-- Every finite row-stochastic matrix admits this two-sided Markov group
inverse lift on the full matrix carrier. -/
theorem exists_stochastic_markovSandwich_groupInverse
    [Nontrivial ι] (P : MatrixCarrier (ι := ι))
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : Matrix ι ι ℝ,
      IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G ∧
        IsGroupInverse (cornerMap ((1 : MatrixCarrier (ι := ι)) - P)
          ((1 : MatrixCarrier (ι := ι)) - P)) (cornerMap G G) := by
  obtain ⟨G, hG, _⟩ := exists_stochastic_markovLeft_groupInverse P hP
  exact ⟨G, hG, markovSandwich_groupInverse P G hG⟩

/-- For every finite row-stochastic matrix, the sandwich Green operator solves
the two-sided Markov Poisson equation on the exact range of the sandwich map. -/
theorem exists_stochastic_markovSandwich_green_recovers_range
    [Nontrivial ι] (P : MatrixCarrier (ι := ι))
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : MatrixCarrier (ι := ι),
      IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G ∧
        ∀ X : MatrixCarrier (ι := ι),
          X ∈ (cornerMap ((1 : MatrixCarrier (ι := ι)) - P)
            ((1 : MatrixCarrier (ι := ι)) - P)).range →
          cornerMap G G
            (cornerMap ((1 : MatrixCarrier (ι := ι)) - P)
              ((1 : MatrixCarrier (ι := ι)) - P) X) = X := by
  obtain ⟨G, hG, _⟩ := exists_stochastic_markovSandwich_groupInverse P hP
  refine ⟨G, hG, ?_⟩
  intro X hX
  exact markovSandwich_recovers_on_range P G hG X hX

end InfoGeometry.QuantumContext.MarkovTwoSidedGroupInverse
