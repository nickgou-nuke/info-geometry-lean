/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticQuadraticDecay

/-!
# Exact dissipation kernel on the full matrix carrier

For a strictly positive finite reversible Markov transition matrix, the
stationary-weighted full-matrix Dirichlet form vanishes exactly when every
column is constant in the row index. Consequently a positive dissipative rate
gives strict instantaneous quadratic decay away from this columnwise consensus
subspace. The carrier remains the full square-matrix algebra throughout.

The statement depends on detailed balance, positive stationary weights, and
strictly positive transitions. It does not assert convergence of iterates or
of a flow.
-/

open scoped BigOperators

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- On the full square-matrix carrier, the reversible Markov dissipation
vanishes exactly when each column is constant across its row index. -/
theorem weightedMatrixPairing_laplacian_eq_zero_iff_columnwise_const
    (P : Matrix ι ι ℝ) (π : ι → ℝ) (X : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i) (hPpos : ∀ i j, 0 < P i j) :
    weightedMatrixPairing π X (markovLeftOnsager P X) = 0 ↔
      ∃ c : ι → ℝ, ∀ i j, X i j = c j := by
  classical
  constructor
  · intro hzero
    have hsum :
        (∑ j, weightedMarkovPairing π (matrixColumn X j)
          (matrixColumn (markovLeftOnsager P X) j)) = 0 := hzero
    have hterm_nonneg (j : ι) :
        0 ≤ weightedMarkovPairing π (matrixColumn X j)
          (matrixColumn (markovLeftOnsager P X) j) := by
      rw [matrixColumn_markovLeftOnsager]
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using
        weightedMarkovPairing_laplacian_nonneg P π (matrixColumn X j)
          hP hDB (fun i => le_of_lt (hπ i))
    have hterm_zero (j : ι) :
        weightedMarkovPairing π (matrixColumn X j)
          (matrixColumn (markovLeftOnsager P X) j) = 0 := by
      apply le_antisymm
      · have hle := Finset.single_le_sum
          (s := Finset.univ)
          (f := fun k => weightedMarkovPairing π (matrixColumn X k)
            (matrixColumn (markovLeftOnsager P X) k))
          (fun k hk => hterm_nonneg k) (Finset.mem_univ j)
        rw [← hsum]
        exact hle
      · exact hterm_nonneg j
    have hveczero (j : ι) :
        weightedMarkovPairing π (matrixColumn X j)
          (matrixColumn X j - Matrix.mulVec P (matrixColumn X j)) = 0 := by
      have hj := hterm_zero j
      rw [matrixColumn_markovLeftOnsager] at hj
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hj
    let c : ι → ℝ := fun j => Classical.choose
      ((weightedMarkovPairing_laplacian_eq_zero_iff_const P π
        (matrixColumn X j) hP hDB hπ hPpos).mp (hveczero j))
    refine ⟨c, ?_⟩
    intro i j
    have hc := Classical.choose_spec
      ((weightedMarkovPairing_laplacian_eq_zero_iff_const P π
        (matrixColumn X j) hP hDB hπ hPpos).mp (hveczero j))
    exact hc i
  · rintro ⟨c, hc⟩
    unfold weightedMatrixPairing
    apply Finset.sum_eq_zero
    intro j hj
    rw [matrixColumn_markovLeftOnsager]
    have hcol : matrixColumn X j = fun _ => c j := by
      funext i
      exact hc i j
    rw [hcol]
    have hconst :=
      (weightedMarkovPairing_laplacian_eq_zero_iff_const P π
        (fun _ : ι => c j) hP hDB hπ hPpos).mpr
        ⟨c j, fun _ => rfl⟩
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hconst

/-- With a positive dissipative rate, the full-matrix instantaneous
quadratic change is strictly negative exactly off the columnwise-constant
kernel. The reversible action is assumed skew for the existing weighted
matrix pairing. -/
theorem weightedMatrixPairing_quadratic_decay_lt_zero_iff_not_columnwise_const
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i) (hPpos : ∀ i j, 0 < P i j)
    (J : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)
    (hJ : ∀ X Y, weightedMatrixPairing π X (J Y) =
      - weightedMatrixPairing π (J X) Y)
    (γ : ℝ) (hγ : 0 < γ) (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (J X - γ • markovLeftOnsager P X) < 0 ↔
      ¬ ∃ c : ι → ℝ, ∀ i j, X i j = c j := by
  have henergy_nonneg :
      0 ≤ weightedMatrixPairing π X (markovLeftOnsager P X) :=
    weightedMatrixPairing_laplacian_nonneg P π X hP hDB
      (fun i => le_of_lt (hπ i))
  rw [weightedMatrixPairing_quadratic_decay_eq π P J hJ γ X]
  constructor
  · intro hdecay hconstant
    have hzero :=
      (weightedMatrixPairing_laplacian_eq_zero_iff_columnwise_const
        P π X hP hDB hπ hPpos).2 hconstant
    rw [hzero] at hdecay
    simp at hdecay
  · intro hnotconstant
    have henergy_ne :
        weightedMatrixPairing π X (markovLeftOnsager P X) ≠ 0 := by
      intro hzero
      exact hnotconstant
        ((weightedMatrixPairing_laplacian_eq_zero_iff_columnwise_const
          P π X hP hDB hπ hPpos).1 hzero)
    have henergy_pos :
        0 < weightedMatrixPairing π X (markovLeftOnsager P X) :=
      lt_of_le_of_ne henergy_nonneg (Ne.symm henergy_ne)
    have hproduct := mul_pos hγ henergy_pos
    change -γ * weightedMatrixPairing π X (markovLeftOnsager P X) < 0
    linarith

end InfoGeometry.QuantumContext.MarkovDrazin
