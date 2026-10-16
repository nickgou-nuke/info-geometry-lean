/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-!
# Matrix-carrier Kemeny–Snell identity

For a finite strictly positive row-stochastic transition matrix and a
normalized stationary row distribution, the group-inverse principal
idempotent is represented by the constant-row stationary-mean matrix. The
canonical group-inverse shift is therefore the two-sided inverse of the
stationary-mean-regularized Markov Laplacian. These are algebraic identities;
no hitting-time interpretation is asserted here.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant-row matrix associated with a stationary row distribution. -/
def stationaryMeanMatrix (π : ι → ℝ) : Matrix ι ι ℝ := fun _ j => π j

/-- The endomorphism principal idempotent is represented by the stationary
mean matrix on the matrix carrier. -/
theorem principalIdempotent_toLin_eq_stationaryMeanMatrix
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    principalIdempotent (Matrix.toLin' (1 - P)) (Matrix.toLin' G) =
      Matrix.toLin' (stationaryMeanMatrix π) := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  let D : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
  have hD : IsGroupInverse A D := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  have hpoint := principalIdempotent_eq_stationaryMean_projection
    P π hP hPpos hπsum hstat D hD
  apply LinearMap.ext
  intro x
  funext i
  have hx := hpoint x
  have hi := congrFun hx i
  change (principalIdempotent A D) x i =
    (Matrix.toLin' (stationaryMeanMatrix π) x) i
  rw [hi]
  simp [stationaryMeanMatrix, weightedMeanMap, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]

/-- The stationary-mean-regularized group-inverse shift is a right inverse
of the regularized Markov Laplacian. -/
theorem stationaryMean_shift_mul_inverse
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    (G + stationaryMeanMatrix π) * ((1 - P) + stationaryMeanMatrix π) = 1 := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  let D : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
  have hD : IsGroupInverse A D := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  have hE := principalIdempotent_toLin_eq_stationaryMeanMatrix
    P π hP hPpos hπsum hstat G hG
  have hE' : principalIdempotent A D =
      Matrix.toLin' (stationaryMeanMatrix π) := by
    simpa [A, D] using hE
  apply Matrix.toLin'.injective
  have hshift := groupInverseShift_mul_inverse hD
  change (D + principalIdempotent A D) *
      (A + principalIdempotent A D) = 1 at hshift
  rw [hE'] at hshift
  have hshiftEnd :
      (Matrix.toLin' G + Matrix.toLin' (stationaryMeanMatrix π)) *
        (Matrix.toLin' (1 - P) + Matrix.toLin' (stationaryMeanMatrix π)) = 1 := by
    simpa [A, D] using hshift
  have hshift' :
      (Matrix.toLin' (G + stationaryMeanMatrix π)) *
        Matrix.toLin' ((1 - P) + stationaryMeanMatrix π) =
          Matrix.toLin' (1 : Matrix ι ι ℝ) := by
    simpa only [map_add, Matrix.toLin'_one, Module.End.one_eq_id] using hshiftEnd
  simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using hshift'

/-- The reverse regularized matrix product is also the identity. -/
theorem stationaryMean_inverse_mul_shift
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    ((1 - P) + stationaryMeanMatrix π) *
      (G + stationaryMeanMatrix π) = 1 := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  let D : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
  have hD : IsGroupInverse A D := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  have hE := principalIdempotent_toLin_eq_stationaryMeanMatrix
    P π hP hPpos hπsum hstat G hG
  have hE' : principalIdempotent A D =
      Matrix.toLin' (stationaryMeanMatrix π) := by
    simpa [A, D] using hE
  apply Matrix.toLin'.injective
  have hshift := groupInverseShift_inverse_mul hD
  change (A + principalIdempotent A D) *
      (D + principalIdempotent A D) = 1 at hshift
  rw [hE'] at hshift
  have hshiftEnd :
      (Matrix.toLin' (1 - P) + Matrix.toLin' (stationaryMeanMatrix π)) *
        (Matrix.toLin' G + Matrix.toLin' (stationaryMeanMatrix π)) = 1 := by
    simpa [A, D] using hshift
  have hshift' :
      Matrix.toLin' ((1 - P) + stationaryMeanMatrix π) *
        Matrix.toLin' (G + stationaryMeanMatrix π) =
          Matrix.toLin' (1 : Matrix ι ι ℝ) := by
    simpa only [map_add, Matrix.toLin'_one, Module.End.one_eq_id] using hshiftEnd
  simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using hshift'

end InfoGeometry.QuantumContext.MarkovDrazin
