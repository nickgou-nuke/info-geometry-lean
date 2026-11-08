/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticFlowBridge
import InfoGeometry.QuantumContext.MarkovMetriplecticReversibleRotation

/-!
# Full-matrix instantaneous quadratic decay for Markov metriplectic flows

For the existing weighted Frobenius pairing on the full matrix carrier, a
weighted-skew reversible linear action contributes zero to the diagonal
quadratic pairing. The detailed-balance Markov Onsager action contributes a
nonnegative Dirichlet term. Consequently subtracting it with a nonnegative
rate gives a nonpositive instantaneous quadratic change. This is a pointwise
algebraic statement: it does not assert strict decay or convergence of a
trajectory, and it does not use the group inverse.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The full-matrix weighted pairing is additive in its second argument. -/
theorem weightedMatrixPairing_sub_right (π : ι → ℝ)
    (X Y Z : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (Y - Z) =
      weightedMatrixPairing π X Y - weightedMatrixPairing π X Z := by
  simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn,
    Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
/-- The full-matrix weighted pairing is homogeneous in its second argument. -/
theorem weightedMatrixPairing_smul_right (π : ι → ℝ)
    (X Y : Matrix ι ι ℝ) (c : ℝ) :
    weightedMatrixPairing π X (c • Y) =
      c * weightedMatrixPairing π X Y := by
  simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_left_comm, mul_comm]

omit [DecidableEq ι] in
/-- A weighted-skew reversible generator has zero quadratic self-pairing on
every matrix in the full matrix carrier. -/
theorem weightedMatrixPairing_reversible_self_eq_zero
    [Nontrivial ι]
    (π : ι → ℝ) (J : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)
    (hJ : ∀ X Y, weightedMatrixPairing π X (J Y) =
      - weightedMatrixPairing π (J X) Y)
    (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (J X) = 0 := by
  have hskew := hJ X X
  rw [weightedMatrixPairing_comm π (J X) X] at hskew
  exact (add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hskew))

/-- The reversible-plus-dissipative quadratic identity on arbitrary full
matrices. The equality needs only weighted skewness of the reversible map;
no Markov or positivity assumptions are required for it. -/
theorem weightedMatrixPairing_quadratic_decay_eq
    [Nontrivial ι]
    (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (J : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)
    (hJ : ∀ X Y, weightedMatrixPairing π X (J Y) =
      - weightedMatrixPairing π (J X) Y)
    (γ : ℝ) (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X
        (J X - γ • markovLeftOnsager P X) =
      -γ * weightedMatrixPairing π X (markovLeftOnsager P X) := by
  rw [weightedMatrixPairing_sub_right, weightedMatrixPairing_smul_right,
    weightedMatrixPairing_reversible_self_eq_zero π J hJ X]
  simp

/-- Under row-stochasticity, detailed balance, nonnegative stationary weights,
and a nonnegative rate, the full-matrix instantaneous quadratic change is
nonpositive. Semidefinite weights and the Markov Laplacian may give equality
for nonzero matrices. -/
theorem weightedMatrixPairing_quadratic_decay_nonpos
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπpos : ∀ i, 0 < π i)
    (J : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)
    (hJ : ∀ X Y, weightedMatrixPairing π X (J Y) =
      - weightedMatrixPairing π (J X) Y)
    (γ : ℝ) (hγ : 0 ≤ γ) (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X
        (J X - γ • markovLeftOnsager P X) ≤ 0 := by
  rw [weightedMatrixPairing_quadratic_decay_eq π P J hJ γ X]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hγ)
    (weightedMatrixPairing_laplacian_nonneg P π X hP hDB
      (fun i => le_of_lt (hπpos i)))

/-- Concrete realization for the existing weighted-skew action built from a
skew coefficient matrix. Strict positivity is needed by that construction's
rowwise division by `π`; it is not needed by the abstract decay theorem. -/
theorem weightedSkewAction_quadratic_decay_nonpos
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπpos : ∀ i, 0 < π i)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = -S)
    (γ : ℝ) (hγ : 0 ≤ γ) (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X
        (mulLeftLinearMap ι ℝ (weightedSkewActionMatrix π S) X -
          γ • markovLeftOnsager P X) ≤ 0 := by
  apply weightedMatrixPairing_quadratic_decay_nonpos P π hP hDB
    hπpos
    (mulLeftLinearMap ι ℝ (weightedSkewActionMatrix π S))
  · intro X Y
    exact weightedMatrixPairing_weightedSkewActionMatrix_skew
      π S hπpos hS X Y
  · exact hγ

end InfoGeometry.QuantumContext.MarkovDrazin
