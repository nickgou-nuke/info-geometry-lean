/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.QuantumContext.MarkovMetriplecticEnergyBalance
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift

/-!
# Concrete reversible action paired with the Markov dissipative operator

On the full noncommutative matrix carrier, left multiplication by a real
skew matrix acts columnwise as a skew operator for the uniform weighted
Frobenius pairing. This file supplies a nonzero coordinate generator and
connects it to the existing Markov metriplectic energy balance. The group
inverse remains the range inverse for the dissipative operator; it is not
identified with the reversible generator.
-/

open scoped BigOperators

namespace InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

open InfoGeometry.QuantumContext.MarkovDrazin
open Matrix

variable {ι : Type*} [Fintype ι]

/-- Columns of a left matrix action are acted on by the same matrix-vector
operator. -/
theorem matrixColumn_leftAction (A X : Matrix ι ι ℝ) (j : ι) :
    matrixColumn (A * X) j = A.mulVec (matrixColumn X j) := by
  ext i
  simp [matrixColumn, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- A skew matrix induces a skew operator for the ordinary real dot product. -/
theorem dotProduct_leftAction_skew (A : Matrix ι ι ℝ)
    (hA : Aᵀ = -A) (x y : ι → ℝ) :
    dotProduct (A.mulVec x) y = -dotProduct x (A.mulVec y) := by
  calc
    dotProduct (A.mulVec x) y = dotProduct y (A.mulVec x) := dotProduct_comm _ _
    _ = Matrix.vecMul y A ⬝ᵥ x := Matrix.dotProduct_mulVec y A x
    _ = dotProduct (Aᵀ.mulVec y) x := by rw [Matrix.mulVec_transpose]
    _ = dotProduct x (Aᵀ.mulVec y) := dotProduct_comm _ _
    _ = dotProduct x ((-A).mulVec y) := by rw [hA]
    _ = -dotProduct x (A.mulVec y) := by
      simp [Matrix.mulVec, dotProduct]

/-- Left multiplication by a skew matrix is skew for the exact full-matrix
pairing used by the Markov flow, specialized to uniform stationary weights. -/
theorem weightedMatrixPairing_leftAction_skew
    (A : Matrix ι ι ℝ) (hA : Aᵀ = -A)
    (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing (fun _ : ι => (1 : ℝ)) X
        (mulLeftLinearMap ι ℝ A Y) =
      -weightedMatrixPairing (fun _ : ι => (1 : ℝ))
        (mulLeftLinearMap ι ℝ A X) Y := by
  unfold weightedMatrixPairing
  change (∑ j, weightedMarkovPairing (fun _ : ι => (1 : ℝ))
      (matrixColumn X j) (matrixColumn (A * Y) j)) =
    -∑ j, weightedMarkovPairing (fun _ : ι => (1 : ℝ))
      (matrixColumn (A * X) j) (matrixColumn Y j)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixColumn_leftAction, matrixColumn_leftAction]
  have h := dotProduct_leftAction_skew A hA
    (matrixColumn X j) (matrixColumn Y j)
  have h' := congrArg (fun z : ℝ => -z) h.symm
  simpa [weightedMarkovPairing, dotProduct] using h'

variable [DecidableEq ι]
/-- The elementary skew generator on two distinct indices. -/
def coordinateSkewMatrix (i j : ι) : Matrix ι ι ℝ :=
  Matrix.single i j 1 - Matrix.single j i 1

omit [Fintype ι] in
theorem coordinateSkewMatrix_skew (i j : ι) :
    (coordinateSkewMatrix i j)ᵀ = -coordinateSkewMatrix i j := by
  simp only [coordinateSkewMatrix, Matrix.transpose_sub,
    Matrix.transpose_single]
  abel

omit [Fintype ι] in
theorem coordinateSkewMatrix_ne_zero (i j : ι) (hij : i ≠ j) :
    coordinateSkewMatrix i j ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix ι ι ℝ => M i j) h
  simp [coordinateSkewMatrix, hij] at hentry

/-- A concrete reversible linear action on the full matrix space. -/
def coordinateReversibleAction (i j : ι) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
  mulLeftLinearMap ι ℝ (coordinateSkewMatrix i j)

theorem weightedMatrixPairing_coordinateReversibleAction_skew
    (i j : ι) (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing (fun _ : ι => (1 : ℝ)) X
        (coordinateReversibleAction i j Y) =
      -weightedMatrixPairing (fun _ : ι => (1 : ℝ))
        (coordinateReversibleAction i j X) Y :=
  weightedMatrixPairing_leftAction_skew
    (coordinateSkewMatrix i j) (coordinateSkewMatrix_skew i j) X Y

/-- Distinct coordinate indices give a genuinely nonzero endomorphism on the
full matrix carrier. -/
theorem coordinateReversibleAction_ne_zero (i j : ι) (hij : i ≠ j) :
    coordinateReversibleAction i j ≠ 0 := by
  intro h
  have hA := congrArg
    (fun T : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ => T (1 : Matrix ι ι ℝ)) h
  have hmat : coordinateSkewMatrix i j = 0 := by
    simpa [coordinateReversibleAction, mulLeftLinearMap] using hA
  exact coordinateSkewMatrix_ne_zero i j hij hmat

/-- The constructed generator is nonzero on the noncommutative full matrix
carrier. -/
theorem coordinateReversibleAction_nonzero_on_full_matrix
    [Nontrivial ι] (i j : ι) (hij : i ≠ j) :
    coordinateReversibleAction i j ≠ 0 ∧
      ∃ X Y : Matrix ι ι ℝ, X * Y ≠ Y * X := by
  exact ⟨coordinateReversibleAction_ne_zero i j hij,
    matrix_noncommutative_witness⟩

/-- On the full matrix carrier, the concrete reversible velocity and Markov
dissipation have zero instantaneous pairing with the constant energy force.
Uniform detailed balance is an explicit hypothesis because it is what makes
the Markov Onsager term symmetric for this Frobenius pairing. -/
theorem markovMetriplectic_coordinateReversible_energy_balance
    [Nontrivial ι]
    (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance
      (fun _ : ι => (1 : ℝ)) P)
    (entropyForce : Matrix ι ι ℝ) (i j : ι) :
    weightedMatrixPairing (fun _ : ι => (1 : ℝ))
      (constantOneMatrix (ι := ι))
      (coordinateReversibleAction i j (constantOneMatrix (ι := ι)) +
        markovLeftOnsager P entropyForce) = 0 := by
  apply markovMetriplectic_energyForce_totalVelocity_pairing_eq_zero
    P (fun _ : ι => (1 : ℝ)) hP hDB (fun _ => by norm_num) entropyForce
    (coordinateReversibleAction i j)
  intro X Y
  exact weightedMatrixPairing_coordinateReversibleAction_skew i j X Y

/-- The range inverse remains attached to dissipation while the concrete
skew action supplies the reversible sector, both on the same matrix carrier. -/
theorem groupInverse_projection_and_coordinateReversible_balance
    [Nontrivial ι]
    (P G entropyForce : Matrix ι ι ℝ)
    (hG : InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
      (1 - P) G)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance
      (fun _ : ι => (1 : ℝ)) P)
    (i j : ι) (hij : i ≠ j) :
    G * markovLeftOnsager P entropyForce =
        markovRangeIdempotent P G * entropyForce ∧
      coordinateReversibleAction i j ≠ 0 ∧
      weightedMatrixPairing (fun _ : ι => (1 : ℝ))
        (constantOneMatrix (ι := ι))
        (coordinateReversibleAction i j (constantOneMatrix (ι := ι)) +
          markovLeftOnsager P entropyForce) = 0 := by
  constructor
  · exact markovGroupInverse_recovers_projected_entropyForce P G entropyForce hG
  constructor
  · exact coordinateReversibleAction_ne_zero i j hij
  · exact markovMetriplectic_coordinateReversible_energy_balance
      P hP hDB entropyForce i j

end InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation
