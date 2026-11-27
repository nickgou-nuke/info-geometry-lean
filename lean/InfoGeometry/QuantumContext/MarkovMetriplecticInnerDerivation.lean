/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticQuadraticDecay

/-!
# Inner derivations in the full-matrix Markov metriplectic flow

The reversible map is the actual inner commutator `X ↦ H X - X H` on the
full matrix algebra. This module proves its Leibniz rule and weighted
skew-adjointness under explicit left-weight and transpose-skew conditions,
then applies the existing Markov Dirichlet decay theorem. It makes no claim
that a row-rescaled CAR generator preserves CAR relations or that trajectories
converge.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inner commutator action of `H` on the full matrix algebra. -/
def matrixInnerCommutator (H : Matrix ι ι ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := H * X - X * H
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

@[simp]
theorem matrixInnerCommutator_apply (H X : Matrix ι ι ℝ) :
    matrixInnerCommutator H X = H * X - X * H := rfl

/-- Inner commutators satisfy the Leibniz rule on the full, generally
noncommutative matrix algebra. -/
theorem matrixInnerCommutator_mul (H X Y : Matrix ι ι ℝ) :
    matrixInnerCommutator H (X * Y) =
      matrixInnerCommutator H X * Y + X * matrixInnerCommutator H Y := by
  simp only [matrixInnerCommutator_apply, Matrix.mul_sub, Matrix.sub_mul]
  noncomm_ring

/-- Right multiplication by a transpose-skew matrix is skew for the
weighted Frobenius pairing (the row weights are unchanged by right action). -/
theorem weightedMatrixPairing_rightAction_skew
    (π : ι → ℝ) (H : Matrix ι ι ℝ) (hH : Hᵀ = -H)
    (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (Y * H) =
      -weightedMatrixPairing π (X * H) Y := by
  classical
  unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
  simp only [Matrix.mul_apply]
  have hentry : ∀ k j : ι, H k j = -H j k := fun k j => by
    have h := congrArg (fun M : Matrix ι ι ℝ => M j k) hH
    have h' : H k j = -H j k := by simpa using h
    exact h'
  calc
    ∑ j, ∑ i, π i * X i j * ∑ k, Y i k * H k j
        = ∑ j, ∑ i, ∑ k, π i * X i j * (Y i k * H k j) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ k, ∑ i, ∑ j, π i * X i j * (Y i k * (-H j k)) := by
          calc
            ∑ j, ∑ i, ∑ k, π i * X i j * (Y i k * H k j)
                = ∑ i, ∑ j, ∑ k, π i * X i j * (Y i k * H k j) := Finset.sum_comm
            _ = ∑ i, ∑ k, ∑ j, π i * X i j * (Y i k * H k j) := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
            _ = ∑ k, ∑ i, ∑ j, π i * X i j * (Y i k * H k j) := Finset.sum_comm
            _ = ∑ k, ∑ i, ∑ j, π i * X i j * (Y i k * (-H j k)) := by
                refine Finset.sum_congr rfl fun k _ =>
                  Finset.sum_congr rfl fun i _ =>
                    Finset.sum_congr rfl fun j _ => by rw [hentry k j]
    _ = -∑ k, ∑ i, π i * (∑ j, X i j * H j k) * Y i k := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [mul_neg, neg_mul]
          ac_rfl

private lemma weightedMatrixPairing_sub_left
    (π : ι → ℝ) (A B Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π (A - B) Y =
      weightedMatrixPairing π A Y - weightedMatrixPairing π B Y := by
  classical
  unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
  simp only [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- A genuine inner commutator is skew for the weighted Frobenius pairing
when its left action is weighted-skew and its right action is transpose-skew.
These are explicit compatibility conditions, not consequences of a general
stationary distribution. -/
theorem weightedMatrixPairing_innerCommutator_skew
    (π : ι → ℝ) (H : Matrix ι ι ℝ)
    (hLeft : ∀ i k, π i * H i k = -(π k * H k i))
    (hTranspose : Hᵀ = -H)
    (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (matrixInnerCommutator H Y) =
      -weightedMatrixPairing π (matrixInnerCommutator H X) Y := by
  rw [matrixInnerCommutator_apply, matrixInnerCommutator_apply,
    weightedMatrixPairing_sub_right, weightedMatrixPairing_sub_left]
  have hL := weightedMatrixPairing_leftAction_skew_of_weighted_skew
    π H hLeft X Y
  have hR := weightedMatrixPairing_rightAction_skew π H hTranspose X Y
  change weightedMatrixPairing π X (mulLeftLinearMap ι ℝ H Y) -
      weightedMatrixPairing π X (Y * H) =
    -(weightedMatrixPairing π (mulLeftLinearMap ι ℝ H X) Y -
      weightedMatrixPairing π (X * H) Y)
  rw [hL, hR]
  abel

/-- The inner-commutator reversible sector plus the Markov Onsager sector has
nonpositive instantaneous quadratic change on the full matrix carrier. The
Markov term is scaled by a nonnegative rate; no asymptotic flow is asserted. -/
theorem weightedMatrixPairing_innerCommutator_quadratic_decay_nonpos
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i)
    (H : Matrix ι ι ℝ)
    (hLeft : ∀ i k, π i * H i k = -(π k * H k i))
    (hTranspose : Hᵀ = -H)
    (γ : ℝ) (hγ : 0 ≤ γ) (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X
      (matrixInnerCommutator H X - γ • markovLeftOnsager P X) ≤ 0 := by
  exact weightedMatrixPairing_quadratic_decay_nonpos P π hP hDB hπ
    (matrixInnerCommutator H) (by
      intro U V
      exact weightedMatrixPairing_innerCommutator_skew π H hLeft hTranspose U V)
    γ hγ X

end InfoGeometry.QuantumContext.MarkovDrazin
