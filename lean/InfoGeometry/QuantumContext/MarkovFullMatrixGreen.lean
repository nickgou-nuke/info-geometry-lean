/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovAttentionGreenStrictPositivity
import InfoGeometry.QuantumContext.MarkovAttentionGreenReciprocity
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift

/-!
# Green pairing on the full matrix carrier

The reversible Markov Green pairing lifts columnwise to the full matrix
space. Reciprocity holds on the full carrier; strict positivity requires the
source matrix to lie in the range of the Markov Laplacian and to be nonzero.
This range condition excludes stationary columns, on which the group inverse
vanishes. No asymptotic convergence or claim for general directed chains is
made.
-/

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- A column of a matrix product is the matrix action on the corresponding
column vector. -/
theorem matrixColumn_mulVec_left (A X : Matrix ι ι ℝ) (j : ι) :
    matrixColumn (A * X) j = Matrix.mulVec A (matrixColumn X j) := by
  ext i
  simp [matrixColumn, Matrix.mulVec, dotProduct, Matrix.mul_apply]

omit [Nonempty ι] in
/-- The group inverse is self-adjoint for the weighted pairing on the full
matrix carrier. This is the columnwise lift of the finite-dimensional
reversibility theorem. -/
theorem weightedMatrixPairing_groupInverse_symmetric
    (P G : Matrix ι ι ℝ) (π : ι → ℝ) (X Y : Matrix ι ι ℝ)
    (hπ : ∀ i, π i ≠ 0)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hG : IsGroupInverse (1 - P) G) :
    weightedMatrixPairing π X (G * Y) =
      weightedMatrixPairing π (G * X) Y := by
  unfold weightedMatrixPairing
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixColumn_mulVec_left, matrixColumn_mulVec_left]
  exact weightedMarkovPairing_groupInverse_symmetric
    P G π (matrixColumn X j) (matrixColumn Y j) hπ hDB hG

omit [Nonempty ι] in
/-- On the full matrix carrier, the detailed-balance weighted pairing of a
potential with its Markov Laplacian equals the pairing of that Laplacian with
its group-inverse image. This is a finite-matrix Green-form identity; no
diagonal restriction is imposed on `X`. -/
theorem weightedMatrixPairing_laplacian_eq_groupInverse_greenForm
    (P G : Matrix ι ι ℝ) (π : ι → ℝ) (X : Matrix ι ι ℝ)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hG : IsGroupInverse (1 - P) G) :
    weightedMatrixPairing π X (markovLeftOnsager P X) =
      weightedMatrixPairing π (markovLeftOnsager P X)
        (G * markovLeftOnsager P X) := by
  let Y : Matrix ι ι ℝ := X - G * markovLeftOnsager P X
  have hLG : (1 - P) * G * ((1 - P) * X) = (1 - P) * X := by
    calc
      (1 - P) * G * ((1 - P) * X) =
          (1 - P) * (G * ((1 - P) * X)) := by noncomm_ring
      _ = ((1 - P) * G * (1 - P)) * X := by noncomm_ring
      _ = (1 - P) * X := by rw [hG.1]
  have hLG' : (1 - P) * (G * ((1 - P) * X)) = (1 - P) * X := by
    calc
      (1 - P) * (G * ((1 - P) * X)) =
          (1 - P) * G * ((1 - P) * X) := by noncomm_ring
      _ = (1 - P) * X := hLG
  have hLY : markovLeftOnsager P Y = 0 := by
    change (1 - P) * (X - G * ((1 - P) * X)) = 0
    rw [mul_sub, hLG', sub_self]
  have horth :
      weightedMatrixPairing π (markovLeftOnsager P X) Y = 0 := by
    calc
      weightedMatrixPairing π (markovLeftOnsager P X) Y =
          weightedMatrixPairing π Y (markovLeftOnsager P X) :=
            weightedMatrixPairing_comm π _ _
      _ = weightedMatrixPairing π (markovLeftOnsager P Y) X := by
            exact weightedMatrixPairing_laplacian_symmetric P π Y X hDB
      _ = 0 := by
        rw [hLY]
        simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn]
  have hsub :
      weightedMatrixPairing π (markovLeftOnsager P X) Y =
        weightedMatrixPairing π (markovLeftOnsager P X) X -
          weightedMatrixPairing π (markovLeftOnsager P X)
            (G * markovLeftOnsager P X) := by
    dsimp [Y]
    simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn,
      Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  calc
    weightedMatrixPairing π X (markovLeftOnsager P X) =
        weightedMatrixPairing π (markovLeftOnsager P X) X :=
          weightedMatrixPairing_comm π _ _
    _ = weightedMatrixPairing π (markovLeftOnsager P X)
          (G * markovLeftOnsager P X) := by
            rw [horth] at hsub
            exact (sub_eq_zero.mp hsub.symm)

/-- A nonzero full-matrix source in the range of the Markov Laplacian has
strictly positive stationary-weighted Green pairing with its group-inverse
image. The proof decomposes the full matrix pairing by columns and applies
the existing vector theorem to each nonzero column. -/
theorem weightedMatrixPairing_groupInverse_pos_of_ne_on_range
    (P G : Matrix ι ι ℝ) (π : ι → ℝ) (X : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπpos : ∀ i, 0 < π i)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hG : IsGroupInverse (1 - P) G)
    (hXrange : X ∈ (markovLeftOnsager P).range)
    (hXne : X ≠ 0) :
    0 < weightedMatrixPairing π X (G * X) := by
  obtain ⟨Z, hZX⟩ := LinearMap.mem_range.mp hXrange
  change markovLeftOnsager P Z = X at hZX
  rw [markovLeftOnsager_apply] at hZX
  have hcolumn_range (j : ι) :
      matrixColumn X j ∈ LinearMap.range (Matrix.toLin' (1 - P)) := by
    refine LinearMap.mem_range.mpr ⟨matrixColumn Z j, ?_⟩
    change Matrix.mulVec (1 - P) (matrixColumn Z j) = matrixColumn X j
    rw [← hZX]
    exact (matrixColumn_markovLeftOnsager P Z j).symm
  have hcolumn_mean_zero (j : ι) :
      weightedMeanMap π (matrixColumn X j) = 0 := by
    have hRange := range_laplacian_eq_weightedMean_ker P π hP hPpos hπsum hstat
    have hker : matrixColumn X j ∈ (weightedMeanMap π).ker := by
      rw [← hRange]
      exact hcolumn_range j
    exact LinearMap.mem_ker.mp hker
  have hcolumn_green_nonneg (j : ι) :
      0 ≤ weightedMarkovPairing π (matrixColumn X j)
        (Matrix.mulVec G (matrixColumn X j)) := by
    by_cases hzero : matrixColumn X j = 0
    · simp [hzero, weightedMarkovPairing]
    · exact le_of_lt (weightedMarkovPairing_groupInverse_pos_of_ne
        P G π (matrixColumn X j) hP hPpos hπpos hπsum hstat hDB hG
        (hcolumn_mean_zero j) hzero)
  have hnonzero_column : ∃ j, matrixColumn X j ≠ 0 := by
    by_contra hn
    apply hXne
    ext i j
    have hzero : matrixColumn X j = 0 := by
      by_contra hnot
      exact hn ⟨j, hnot⟩
    exact congrFun hzero i
  have hpairing_columns :
      weightedMatrixPairing π X (G * X) =
        ∑ j, weightedMarkovPairing π (matrixColumn X j)
          (Matrix.mulVec G (matrixColumn X j)) := by
    unfold weightedMatrixPairing
    congr 1
  rw [hpairing_columns]
  apply Finset.sum_pos'
  · intro j hj
    exact hcolumn_green_nonneg j
  · obtain ⟨j, hj⟩ := hnonzero_column
    exact ⟨j, Finset.mem_univ _, weightedMarkovPairing_groupInverse_pos_of_ne
      P G π (matrixColumn X j) hP hPpos hπpos hπsum hstat hDB hG
      (hcolumn_mean_zero j) hj⟩

end InfoGeometry.QuantumContext.MarkovDrazin
