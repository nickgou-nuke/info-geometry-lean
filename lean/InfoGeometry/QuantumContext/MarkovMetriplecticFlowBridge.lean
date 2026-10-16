/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MarkovAttentionFiniteDirichlet
import InfoGeometry.SuperMetriplectic.Flow

/-!
# Full-matrix Markov–Onsager bridge

Lift the reversible finite Markov Dirichlet form from columns to the full
noncommutative matrix carrier. The Onsager map is left multiplication by
`1 - P`. Under detailed balance its weighted column pairing is symmetric and
positive semidefinite. Row-stochasticity makes the all-ones matrix an energy
force in the kernel. A separate group-inverse theorem recovers forces in the
left-multiplication range. No quantum-channel, Hamiltonian-conservation, or
iteration-limit statement is made here.
-/

open scoped BigOperators

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Column `j` of a square matrix, viewed as a vector-valued observable. -/
def matrixColumn (X : Matrix ι ι ℝ) (j : ι) : ι → ℝ := fun i => X i j

/-- The weighted Frobenius pairing obtained by summing the Markov pairing over
all matrix columns. Its carrier is the full matrix space, not a diagonal
subspace. -/
def weightedMatrixPairing (π : ι → ℝ) (X Y : Matrix ι ι ℝ) : ℝ :=
  ∑ j, weightedMarkovPairing π (matrixColumn X j) (matrixColumn Y j)

/-- The Markov Laplacian acting on the full matrix carrier by left
multiplication. -/
def markovLeftOnsager (P : Matrix ι ι ℝ) : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
  mulLeftLinearMap ι ℝ (1 - P)

/-- The constant-column matrix used as the degenerate energy force. -/
def constantOneMatrix : Matrix ι ι ℝ := fun _ _ => 1

@[simp]
theorem markovLeftOnsager_apply (P X : Matrix ι ι ℝ) :
    markovLeftOnsager P X = (1 - P) * X := rfl

/-- Each column of `(1-P) * X` is `(1-P)` applied to the corresponding
column of `X`. -/
theorem matrixColumn_markovLeftOnsager (P X : Matrix ι ι ℝ) (j : ι) :
    matrixColumn (markovLeftOnsager P X) j =
      Matrix.mulVec (1 - P) (matrixColumn X j) := by
  ext i
  simp [matrixColumn, markovLeftOnsager, mulLeftLinearMap,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- The full-matrix Dirichlet energy is the sum of the reversible edge
energies of all columns. This transports the finite vector edge formula to
the actual matrix carrier on which the Markov Onsager map acts. -/
theorem weightedMatrixPairing_laplacian_eq_half_column_edge_energy
    (P : Matrix ι ι ℝ) (π : ι → ℝ) (X : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P) :
    weightedMatrixPairing π X (markovLeftOnsager P X) =
      ∑ c, (1 / 2 : ℝ) * ∑ i, ∑ j,
        π i * P i j * (X i c - X j c) ^ 2 := by
  unfold weightedMatrixPairing
  apply Finset.sum_congr rfl
  intro c hc
  rw [matrixColumn_markovLeftOnsager]
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, matrixColumn] using
    (weightedMarkovPairing_laplacian_eq_half_edge_energy P π
      (matrixColumn X c) hP hDB)

/-- Detailed balance lifts the Markov Laplacian symmetry to the full matrix
carrier under the weighted Frobenius pairing. -/
theorem weightedMatrixPairing_laplacian_symmetric
    (P : Matrix ι ι ℝ) (π : ι → ℝ) (X Y : Matrix ι ι ℝ)
    (hDB : InfoGeometry.Probability.DetailedBalance π P) :
    weightedMatrixPairing π X (markovLeftOnsager P Y) =
      weightedMatrixPairing π (markovLeftOnsager P X) Y := by
  unfold weightedMatrixPairing
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixColumn_markovLeftOnsager, matrixColumn_markovLeftOnsager]
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using
    weightedMarkovPairing_laplacian_symmetric P π
      (matrixColumn X j) (matrixColumn Y j) hDB

omit [DecidableEq ι] in
/-- The weighted Frobenius pairing is symmetric as a pairing on matrices. -/
theorem weightedMatrixPairing_comm (π : ι → ℝ) (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π X Y = weightedMatrixPairing π Y X := by
  unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ac_rfl

/-- Nonnegative stationary weights lift the Markov Dirichlet inequality to
the full matrix carrier. This is semidefinite; no nondegeneracy is asserted. -/
theorem weightedMatrixPairing_laplacian_nonneg
    (P : Matrix ι ι ℝ) (π : ι → ℝ) (X : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 ≤ π i) :
    0 ≤ weightedMatrixPairing π X (markovLeftOnsager P X) := by
  unfold weightedMatrixPairing
  apply Finset.sum_nonneg
  intro j _
  rw [matrixColumn_markovLeftOnsager]
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using
    weightedMarkovPairing_laplacian_nonneg P π
      (matrixColumn X j) hP hDB hπ

/-- The all-ones matrix is annihilated by the Markov left Onsager map. -/
theorem markovLeftOnsager_ones_eq_zero
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    markovLeftOnsager P (constantOneMatrix (ι := ι)) = 0 := by
  have hrow (i : ι) : ∑ k, P i k = 1 :=
    Matrix.sum_row_of_mem_rowStochastic hP i
  have hPone : Matrix.mulVec P (fun _ : ι => (1 : ℝ)) = fun _ => 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, hrow i]
  ext i j
  change matrixColumn (markovLeftOnsager P
    (constantOneMatrix (ι := ι))) j i = 0
  rw [matrixColumn_markovLeftOnsager]
  change (Matrix.mulVec (1 - P) (fun _ : ι => (1 : ℝ))) i = 0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  simp [hPone]

/-- Full-matrix metriplectic packet for a reversible finite Markov operator.
The reversible vector is an unconstrained input of the generic packet; this
construction makes no claim that it preserves the energy pairing. -/
def markovMetriplecticFlow
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 ≤ π i)
    (entropyForce reversibleFlow : Matrix ι ι ℝ) :
    InfoGeometry.SuperMetriplectic.MetriplecticFlow (Matrix ι ι ℝ) := by
  let metric : InfoGeometry.SuperMetriplectic.OnsagerMetricData
      (Matrix ι ι ℝ) := {
    onsager := markovLeftOnsager P
    pairing := weightedMatrixPairing π
    metric_symmetric := fun X Y => by
      rw [weightedMatrixPairing_laplacian_symmetric P π X Y hDB,
        weightedMatrixPairing_comm]
    metric_nonnegative := fun X =>
      weightedMatrixPairing_laplacian_nonneg P π X hP hDB hπ
    pairing_zero_right := by
      intro X
      simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn]
  }
  refine {
    metric := metric
    entropyForce := entropyForce
    energyForce := constantOneMatrix (ι := ι)
    reversibleFlow := reversibleFlow
    dissipativeFlow := markovLeftOnsager P entropyForce
    totalFlow := reversibleFlow + markovLeftOnsager P entropyForce
    entropyProduction := weightedMatrixPairing π entropyForce
      (markovLeftOnsager P entropyForce)
    dissipativeFlow_eq_onsager_entropy := rfl
    totalFlow_eq_reversible_add_dissipative := rfl
    energy_degeneracy := ?_
    entropyProduction_eq_quadratic := rfl
  }
  simpa [metric] using markovLeftOnsager_ones_eq_zero P hP

/-- The constructed full-matrix flow has nonnegative entropy production. -/
theorem markovMetriplecticFlow_entropyProduction_nonneg
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 ≤ π i)
    (S R : Matrix ι ι ℝ) :
    0 ≤ (markovMetriplecticFlow P π hP hDB hπ S R).entropyProduction :=
  (markovMetriplecticFlow P π hP hDB hπ S R).entropyProduction_nonnegative

/-- The group inverse recovers every matrix force in the range of left
multiplication by the Markov Laplacian from its dissipative image. This
algebraic statement is independent of detailed balance and of the weighted
pairing. -/
theorem groupInverse_recovers_matrix_force_of_left_range
    (P G X Z : Matrix ι ι ℝ)
    (hG₁ : (1 - P) * G * (1 - P) = 1 - P)
    (hGcomm : (1 - P) * G = G * (1 - P))
    (hX : X = (1 - P) * Z) :
    G * ((1 - P) * X) = X := by
  rw [hX]
  calc
    G * ((1 - P) * ((1 - P) * Z)) =
        (G * (1 - P) * (1 - P)) * Z := by
          simp only [mul_assoc]
    _ = ((1 - P) * G * (1 - P)) * Z := by rw [hGcomm]
    _ = (1 - P) * Z := by rw [hG₁]

end InfoGeometry.QuantumContext.MarkovDrazin
