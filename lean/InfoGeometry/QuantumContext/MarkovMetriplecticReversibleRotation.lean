/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.QuantumContext.MarkovMetriplecticEnergyBalance
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift
import InfoGeometry.QuantumContext.FiniteSoftmaxStationaryGreen

/-!
# Concrete reversible actions paired with the Markov dissipative operator

On the full matrix carrier, left multiplication by a real skew matrix is
skew for the uniform Frobenius pairing. For arbitrary strictly positive
weights, rowwise rescaling of a skew matrix gives a weighted-skew action.
Both actions connect to the existing Markov metriplectic energy balance. The
group inverse remains the range inverse for the dissipative operator; it is
not identified with either reversible generator.
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

/-- A matrix-vector action is skew for the stationary-weighted pairing when
its entries satisfy the corresponding weighted skew-adjointness relation. -/
theorem weightedMarkovPairing_leftAction_skew
    (π : ι → ℝ) (A : Matrix ι ι ℝ)
    (hA : ∀ i k, π i * A i k = -(π k * A k i))
    (x y : ι → ℝ) :
    weightedMarkovPairing π x (A.mulVec y) =
      -weightedMarkovPairing π (A.mulVec x) y := by
  classical
  unfold weightedMarkovPairing
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    π i * x i * (A i k * y k) =
        (π i * A i k) * (x i * y k) := by ac_rfl
    _ = (-(π k * A k i)) * (x i * y k) := by rw [hA i k]
    _ = -(π k * (A k i * x i) * y k) := by
      rw [neg_mul]
      congr 1
      ac_rfl

/-- Weighted-skew left multiplication is skew on the full matrix carrier,
column by column, for the stationary-weighted Frobenius pairing. -/
theorem weightedMatrixPairing_leftAction_skew_of_weighted_skew
    (π : ι → ℝ) (A : Matrix ι ι ℝ)
    (hA : ∀ i k, π i * A i k = -(π k * A k i))
    (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (mulLeftLinearMap ι ℝ A Y) =
      -weightedMatrixPairing π (mulLeftLinearMap ι ℝ A X) Y := by
  unfold weightedMatrixPairing
  change (∑ j, weightedMarkovPairing π (matrixColumn X j)
      (matrixColumn (A * Y) j)) =
    -∑ j, weightedMarkovPairing π (matrixColumn (A * X) j)
      (matrixColumn Y j)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixColumn_leftAction, matrixColumn_leftAction]
  exact weightedMarkovPairing_leftAction_skew π A hA
    (matrixColumn X j) (matrixColumn Y j)

/-- A weighted-skew action matrix obtained by dividing a skew matrix rowwise
by a strictly positive weight. This is not assumed to be a Markov generator
or a probability-transition operator. -/
noncomputable def weightedSkewActionMatrix
    (π : ι → ℝ) (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i k => S i k / π i

omit [Fintype ι] in
theorem weightedSkewActionMatrix_weighted_skew
    (π : ι → ℝ) (S : Matrix ι ι ℝ)
    (hπ : ∀ i, 0 < π i) (hS : Sᵀ = -S) :
    ∀ i k, π i * weightedSkewActionMatrix π S i k =
      -(π k * weightedSkewActionMatrix π S k i) := by
  intro i k
  have hSik : S i k = -S k i := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i k) hS
    have h' : S k i = -S i k := by simpa using h
    simpa using (congrArg (fun z : ℝ => -z) h').symm
  unfold weightedSkewActionMatrix
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hi : π i ≠ 0 := (ne_of_gt (hπ i))
  have hk : π k ≠ 0 := (ne_of_gt (hπ k))
  field_simp [hi, hk]
  rw [hSik]

/-- The weighted-skew action matrix built from a skew matrix acts skewly
on the full matrix space, with no uniformity assumption on the weights. -/
theorem weightedMatrixPairing_weightedSkewActionMatrix_skew
    (π : ι → ℝ) (S : Matrix ι ι ℝ)
    (hπ : ∀ i, 0 < π i) (hS : Sᵀ = -S)
    (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π X
        (mulLeftLinearMap ι ℝ (weightedSkewActionMatrix π S) Y) =
      -weightedMatrixPairing π
        (mulLeftLinearMap ι ℝ (weightedSkewActionMatrix π S) X) Y := by
  exact weightedMatrixPairing_leftAction_skew_of_weighted_skew π
    (weightedSkewActionMatrix π S)
    (weightedSkewActionMatrix_weighted_skew π S hπ hS) X Y

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

/-- A skew coefficient matrix, divided rowwise by a strictly positive
stationary weight, gives a concrete reversible action for the nonuniform
weighted pairing. The resulting total velocity has zero instantaneous
pairing with the constant energy force. -/
theorem markovMetriplectic_weightedSkewAction_energy_balance
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i)
    (entropyForce : Matrix ι ι ℝ)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = -S) :
    weightedMatrixPairing π (constantOneMatrix (ι := ι))
      (mulLeftLinearMap ι ℝ (weightedSkewActionMatrix π S)
          (constantOneMatrix (ι := ι)) +
        markovLeftOnsager P entropyForce) = 0 := by
  apply markovMetriplectic_energyForce_totalVelocity_pairing_eq_zero
    P π hP hDB hπ entropyForce
    (mulLeftLinearMap ι ℝ (weightedSkewActionMatrix π S))
  intro X Y
  exact weightedMatrixPairing_weightedSkewActionMatrix_skew
    π S hπ hS X Y

/-- The same full-matrix packet exposes two independent facts: the Drazin
group inverse recovers the projected dissipative force, while the constructed
weighted-skew reversible action yields the instantaneous energy pairing law. -/
theorem groupInverse_projection_and_weightedSkewAction_balance
    [Nontrivial ι]
    (P G entropyForce : Matrix ι ι ℝ)
    (hG : InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
      (1 - P) G)
    (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = -S) :
    G * markovLeftOnsager P entropyForce =
        markovRangeIdempotent P G * entropyForce ∧
      weightedMatrixPairing π (constantOneMatrix (ι := ι))
        (mulLeftLinearMap ι ℝ (weightedSkewActionMatrix π S)
            (constantOneMatrix (ι := ι)) +
          markovLeftOnsager P entropyForce) = 0 := by
  exact ⟨markovGroupInverse_recovers_projected_entropyForce P G entropyForce hG,
    markovMetriplectic_weightedSkewAction_energy_balance
      P π hP hDB hπ entropyForce S hS⟩

/-- For symmetric finite softmax scores, the explicit partition-function
stationary weight instantiates the nonuniform full-matrix weighted-skew action
and its energy balance. The score symmetry is essential for detailed balance. -/
theorem symmetricSoftmax_weightedSkewAction_energy_balance
    [Nontrivial ι] [Nonempty ι]
    (scores : ι → ι → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (entropyForce : Matrix ι ι ℝ)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = -S) :
    weightedMatrixPairing
        (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
        (constantOneMatrix (ι := ι))
      (mulLeftLinearMap ι ℝ
          (weightedSkewActionMatrix
            (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores) S)
          (constantOneMatrix (ι := ι)) +
        markovLeftOnsager
          (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
          entropyForce) = 0 := by
  apply markovMetriplectic_weightedSkewAction_energy_balance
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix_mem_rowStochastic scores)
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight_detailedBalance scores hsymm)
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight_pos scores)
    entropyForce S hS

/-- The symmetric-softmax specialization displays both operators on one full
matrix carrier: group-inverse projected-force recovery and reversible plus
dissipative instantaneous energy balance. These are separate conclusions. -/
theorem symmetricSoftmax_groupInverse_projection_and_weightedSkewAction_balance
    [Nontrivial ι] [Nonempty ι]
    (scores : ι → ι → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (G entropyForce : Matrix ι ι ℝ)
    (hG : InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
      (1 - InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = -S) :
    G * markovLeftOnsager
        (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
        entropyForce =
      markovRangeIdempotent
        (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G * entropyForce ∧
    weightedMatrixPairing
        (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
        (constantOneMatrix (ι := ι))
      (mulLeftLinearMap ι ℝ
          (weightedSkewActionMatrix
            (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores) S)
          (constantOneMatrix (ι := ι)) +
        markovLeftOnsager
          (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
          entropyForce) = 0 := by
  apply groupInverse_projection_and_weightedSkewAction_balance
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
    G entropyForce hG
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix_mem_rowStochastic scores)
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight_detailedBalance scores hsymm)
    (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight_pos scores)
    S hS

/-- Symmetric softmax supplies an actual group inverse, so the joint
projected-force and weighted-skew energy conclusions need no user-supplied
generalized inverse. -/
theorem exists_symmetricSoftmax_groupInverse_projection_and_weightedSkewAction_balance
    [Nontrivial ι] [Nonempty ι]
    (scores : ι → ι → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (entropyForce : Matrix ι ι ℝ)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = -S) :
    ∃ G : Matrix ι ι ℝ,
      InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
        (1 - InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G ∧
      G * markovLeftOnsager
          (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
          entropyForce =
        markovRangeIdempotent
          (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores) G * entropyForce ∧
      weightedMatrixPairing
          (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores)
          (constantOneMatrix (ι := ι))
        (mulLeftLinearMap ι ℝ
            (weightedSkewActionMatrix
              (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxPartitionStationaryWeight scores) S)
            (constantOneMatrix (ι := ι)) +
          markovLeftOnsager
            (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionMatrix scores)
            entropyForce) = 0 := by
  obtain ⟨G, hG, _hreciprocity⟩ :=
    InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.exists_softmax_groupInverse_green_reciprocity
      scores hsymm
  exact ⟨G, hG,
    (symmetricSoftmax_groupInverse_projection_and_weightedSkewAction_balance
      scores hsymm G entropyForce hG S hS).1,
    (symmetricSoftmax_groupInverse_projection_and_weightedSkewAction_balance
      scores hsymm G entropyForce hG S hS).2⟩

end InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation
