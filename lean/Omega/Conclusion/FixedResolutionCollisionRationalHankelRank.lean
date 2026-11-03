/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.FiniteMomentHankelRank

open scoped BigOperators

namespace Omega.Conclusion

/-- The fixed-resolution collision moment sequence of a finite spectrum. -/
def fixedResolutionCollisionMoment {r : ℕ} (δ μ : Fin r → ℚ) (q : ℕ) : ℚ :=
  ∑ i, μ i * δ i ^ q

/-- The finite generating function prefix of the collision moments. -/
def fixedResolutionCollisionGeneratingPrefix {r : ℕ}
    (δ μ : Fin r → ℚ) (z : ℚ) (N : ℕ) : ℚ :=
  ∑ q ∈ Finset.range N, fixedResolutionCollisionMoment δ μ q * z ^ q

/-- The partial-fraction rewrite of the generating-function prefix. -/
def fixedResolutionCollisionPartialFraction {r : ℕ}
    (δ μ : Fin r → ℚ) (z : ℚ) (N : ℕ) : ℚ :=
  ∑ i, μ i * (((δ i * z) ^ N - 1) / (δ i * z - 1))

/-- The Vandermonde entry associated to the support value `δ_i` and moment index `q`. -/
def fixedResolutionCollisionVandermondeEntry {r : ℕ} (δ : Fin r → ℚ) (q : ℕ) (i : Fin r) : ℚ :=
  δ i ^ q

/-- The Hankel entry built from the collision moments. -/
def fixedResolutionCollisionHankelEntry {r : ℕ} (δ μ : Fin r → ℚ) (i j : ℕ) : ℚ :=
  fixedResolutionCollisionMoment δ μ (i + j)

/-- The Vandermonde-diagonal Gram factorization of the Hankel entry. -/
def fixedResolutionCollisionGramEntry {r : ℕ} (δ μ : Fin r → ℚ) (i j : ℕ) : ℚ :=
  ∑ k, μ k * fixedResolutionCollisionVandermondeEntry δ i k *
    fixedResolutionCollisionVandermondeEntry δ j k

/-- The concrete square moment Hankel matrix at a fixed finite spectrum. -/
def fixedResolutionCollisionHankelMatrix {r : ℕ} (δ μ : Fin r → ℚ) :
    Matrix (Fin r) (Fin r) ℚ := fun i j =>
  fixedResolutionCollisionMoment δ μ (i.1 + j.1)

private theorem fixedResolutionCollisionHankelMatrix_eq_canonical {r : ℕ}
    (δ μ : Fin r → ℚ) :
    fixedResolutionCollisionHankelMatrix δ μ =
      Omega.POM.finiteMomentHankel δ μ := by
  rfl

/-- Distinct finite support and nonzero weights imply the actual moment Hankel matrix
has full rank. -/
theorem fixedResolutionCollisionHankelMatrix_rank {r : ℕ} (δ μ : Fin r → ℚ)
    (hδ : StrictMono δ) (hμ : ∀ i, μ i ≠ 0) :
    (fixedResolutionCollisionHankelMatrix δ μ).rank = r := by
  rw [fixedResolutionCollisionHankelMatrix_eq_canonical]
  exact Omega.POM.finiteMomentHankel_rank δ μ hδ.injective hμ

/-- Distinct support values and nonzero weights provide the determinant-side witness. -/
def fixedResolutionCollisionDeterminantWitness {r : ℕ} (δ μ : Fin r → ℚ) : Prop :=
  (∀ i, μ i ≠ 0) ∧ ∀ i j, i < j → δ i ≠ δ j

/-- Paper label: `thm:conclusion-fixedresolution-collision-rational-hankel-rank`.
The fixed-resolution moment prefix is a finite sum of geometric series, hence a rational
partial-fraction expression; the Hankel entries factor through the Vandermonde Gram expansion;
distinct support values and nonzero weights imply the full rank of the concrete moment Hankel
matrix by its Vandermonde Gram factorization. -/
theorem paper_conclusion_fixedresolution_collision_rational_hankel_rank
    (r N : ℕ) (δ μ : Fin r → ℚ) (z : ℚ) (hδ : StrictMono δ) (hμ : ∀ i, μ i ≠ 0)
    (hz : ∀ i, δ i * z ≠ 1) :
    (fixedResolutionCollisionGeneratingPrefix δ μ z N =
      fixedResolutionCollisionPartialFraction δ μ z N) ∧
    (∀ i j, fixedResolutionCollisionHankelEntry δ μ i j =
      fixedResolutionCollisionGramEntry δ μ i j) ∧
    fixedResolutionCollisionDeterminantWitness δ μ ∧
    (fixedResolutionCollisionHankelMatrix δ μ).rank = r := by
  have hprefix :
      fixedResolutionCollisionGeneratingPrefix δ μ z N =
        fixedResolutionCollisionPartialFraction δ μ z N := by
    unfold fixedResolutionCollisionGeneratingPrefix fixedResolutionCollisionPartialFraction
      fixedResolutionCollisionMoment
    calc
      ∑ q ∈ Finset.range N, (∑ i, μ i * δ i ^ q) * z ^ q
          = ∑ q ∈ Finset.range N, ∑ i, μ i * ((δ i * z) ^ q) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_pow]
              ring
      _ = ∑ i, ∑ q ∈ Finset.range N, μ i * ((δ i * z) ^ q) := by
            rw [Finset.sum_comm]
      _ = ∑ i, μ i * ∑ q ∈ Finset.range N, (δ i * z) ^ q := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [← Finset.mul_sum]
      _ = ∑ i, μ i * (((δ i * z) ^ N - 1) / (δ i * z - 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [geom_sum_eq (hz i)]
  have hhankel :
      ∀ i j, fixedResolutionCollisionHankelEntry δ μ i j =
        fixedResolutionCollisionGramEntry δ μ i j := by
    intro i j
    simp [fixedResolutionCollisionHankelEntry, fixedResolutionCollisionGramEntry,
      fixedResolutionCollisionMoment, fixedResolutionCollisionVandermondeEntry, pow_add, mul_assoc]
  refine ⟨hprefix, hhankel, ?_, ?_⟩
  · exact ⟨hμ, fun i j hij => ne_of_lt (hδ hij)⟩
  · exact fixedResolutionCollisionHankelMatrix_rank δ μ hδ hμ

end Omega.Conclusion
