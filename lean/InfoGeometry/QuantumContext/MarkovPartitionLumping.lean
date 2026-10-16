/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import InfoGeometry.Canonical.CoarseGraining
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwining

/-!
# Partition incidence and Markov group-inverse transport

For a finite map `G : X → Y`, its incidence matrix sends macrostate observables
to the corresponding microstate observables. The equation `P * C = C * Q` is
equivalent to the block-sum criterion for strong lumpability. When `Q` is
strictly positive, this intertwining forces `G` to be surjective. The
pushforward of a stationary row through `C` supplies the stationary data
required by the existing rectangular group-inverse transport theorem.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovPartitionLumping

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- The deterministic incidence operator of a finite coarse-graining map.
It pulls a macrostate observable back to the microstate space. -/
def partitionIncidence (G : FiniteCoarseGraining X Y) : Matrix X Y ℝ :=
  fun i j => if G i = j then 1 else 0

omit [Fintype X] in
@[simp]
theorem partitionIncidence_mulVec (G : FiniteCoarseGraining X Y)
    (f : Y → ℝ) (i : X) :
    (partitionIncidence G).mulVec f i = f (G i) := by
  classical
  simp [partitionIncidence, Matrix.mulVec, dotProduct]

omit [Fintype X] in
@[simp]
theorem partitionIncidence_row_sum (G : FiniteCoarseGraining X Y) (i : X) :
    ∑ j : Y, partitionIncidence G i j = 1 := by
  classical
  simp [partitionIncidence]

omit [Fintype X] [Fintype Y] in
theorem partitionIncidence_nonneg (G : FiniteCoarseGraining X Y) (i : X) (j : Y) :
    0 ≤ partitionIncidence G i j := by
  classical
  by_cases h : G i = j <;> simp [partitionIncidence, h]

omit [Fintype Y] in
/-- The left product with the incidence matrix records transition mass into a
partition fiber. -/
@[simp]
theorem mul_partitionIncidence_apply (G : FiniteCoarseGraining X Y)
    (P : Matrix X X ℝ) (i : X) (j : Y) :
    (P * partitionIncidence G) i j =
      ∑ k : X, if G k = j then P i k else 0 := by
  classical
  simp [Matrix.mul_apply, partitionIncidence, mul_ite]

omit [Fintype X] in
/-- The right product with the incidence matrix reads the row of `Q` indexed
by the source macrostate. -/
@[simp]
theorem partitionIncidence_mul_apply (G : FiniteCoarseGraining X Y)
    (Q : Matrix Y Y ℝ) (i : X) (j : Y) :
    (partitionIncidence G * Q) i j = Q (G i) j := by
  classical
  simp [Matrix.mul_apply, partitionIncidence]

/-- Matrix intertwining by the partition incidence operator is exactly the
block-sum lumpability criterion. The finite sum is the transition mass from
microstate `i` into the macrostate fiber over `j`. -/
theorem partitionIntertwining_iff_blockSum
    (G : FiniteCoarseGraining X Y) (P : Matrix X X ℝ) (Q : Matrix Y Y ℝ) :
    P * partitionIncidence G = partitionIncidence G * Q ↔
      ∀ i j, (∑ k : X, if G k = j then P i k else 0) = Q (G i) j := by
  constructor
  · intro h i j
    have hentry := congrArg (fun M : Matrix X Y ℝ => M i j) h
    simpa only [mul_partitionIncidence_apply, partitionIncidence_mul_apply] using hentry
  · intro h
    ext i j
    rw [mul_partitionIncidence_apply, partitionIncidence_mul_apply]
    exact h i j

/-- A strictly positive coarse transition matrix cannot intertwine through an
incidence map with an empty coarse fiber. -/
theorem partitionLumping_surjective
    (G : FiniteCoarseGraining X Y) [DecidableEq X]
    (P : Matrix X X ℝ) (Q : Matrix Y Y ℝ)
    (hQpos : ∀ i j, 0 < Q i j)
    (hintertwines : P * partitionIncidence G = partitionIncidence G * Q)
    [Nonempty X] : Function.Surjective G := by
  classical
  intro y
  by_contra hy
  have hmissing : ∀ x : X, G x ≠ y := by
    intro x hx
    exact hy ⟨x, hx⟩
  let i : X := Classical.choice ‹Nonempty X›
  have hentry := congrArg (fun M : Matrix X Y ℝ => M i y) hintertwines
  have hleft : (P * partitionIncidence G) i y = 0 := by
    rw [mul_partitionIncidence_apply]
    simp [hmissing]
  have hright : (partitionIncidence G * Q) i y = Q (G i) y :=
    partitionIncidence_mul_apply G Q i y
  rw [hleft, hright] at hentry
  exact (ne_of_gt (hQpos (G i) y)) hentry.symm

/-- Pushforward of a stationary row along the finite partition map. -/
def pushforwardStationaryRow (G : FiniteCoarseGraining X Y) (π : X → ℝ) : Y → ℝ :=
  fun j => ∑ i : X, π i * partitionIncidence G i j

theorem pushforwardStationaryRow_sum
    (G : FiniteCoarseGraining X Y) (π : X → ℝ) :
    (∑ j : Y, pushforwardStationaryRow G π j) = ∑ i : X, π i := by
  classical
  unfold pushforwardStationaryRow
  rw [Finset.sum_comm]
  calc
    (∑ i : X, ∑ j : Y, π i * partitionIncidence G i j)
        = ∑ i : X, π i * (∑ j : Y, partitionIncidence G i j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ i : X, π i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [partitionIncidence_row_sum]
          ring

/-- A stationary row remains stationary after a Markov intertwining through the
partition incidence operator. -/
theorem pushforwardStationaryRow_stationary
    (G : FiniteCoarseGraining X Y) (P : Matrix X X ℝ) (Q : Matrix Y Y ℝ)
    (π : X → ℝ)
    (hπstat : ∀ j, ∑ i : X, π i * P i j = π j)
    (hintertwines : P * partitionIncidence G = partitionIncidence G * Q) :
    ∀ j, ∑ i : Y, pushforwardStationaryRow G π i * Q i j =
      pushforwardStationaryRow G π j := by
  classical
  intro j
  unfold pushforwardStationaryRow
  calc
    (∑ y : Y, (∑ x : X, π x * partitionIncidence G x y) * Q y j)
        = ∑ x : X, ∑ y : Y,
            (π x * partitionIncidence G x y) * Q y j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
    _ = ∑ x : X, π x * (∑ y : Y,
          partitionIncidence G x y * Q y j) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ x : X, π x * (∑ z : X, P x z * partitionIncidence G z j) := by
          apply Finset.sum_congr rfl
          intro x _
          have hrow := congrArg (fun M : Matrix X Y ℝ => M x j) hintertwines
          have hentry : (∑ z : X, P x z * partitionIncidence G z j) =
              ∑ y : Y, partitionIncidence G x y * Q y j := by
            simpa only [Matrix.mul_apply] using hrow
          rw [hentry]
    _ = ∑ x : X, ∑ z : X, (π x * P x z) * partitionIncidence G z j := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          ring
    _ = ∑ z : X, ∑ x : X, (π x * P x z) * partitionIncidence G z j := by
          rw [Finset.sum_comm]
    _ = ∑ z : X, (∑ x : X, π x * P x z) * partitionIncidence G z j := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_mul]
    _ = ∑ z : X, π z * partitionIncidence G z j := by
          apply Finset.sum_congr rfl
          intro z _
          rw [hπstat z]
    _ = pushforwardStationaryRow G π j := rfl

/-- Given group inverses for both `I - P` and `I - Q`, strictly positive
row-stochastic transitions, and a stationary row for `P`, incidence
intertwining transports the two group inverses. The coarse stationary row is
the pushforward of the fine row. This is a transport theorem, not an existence
or construction theorem for either group inverse. -/
theorem groupInverse_intertwines_of_partitionLumping
    (G : FiniteCoarseGraining X Y)
    [DecidableEq X]
    (P : Matrix X X ℝ) (Q : Matrix Y Y ℝ) (π : X → ℝ)
    [Nonempty X] [Nonempty Y]
    (hP : P ∈ Matrix.rowStochastic ℝ X)
    (hQ : Q ∈ Matrix.rowStochastic ℝ Y)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπsum : ∑ i : X, π i = 1)
    (hπstat : ∀ j, ∑ i : X, π i * P i j = π j)
    (hintertwines : P * partitionIncidence G = partitionIncidence G * Q)
    (Gsharp : Matrix X X ℝ) (hG : IsGroupInverse (1 - P) Gsharp)
    (Qsharp : Matrix Y Y ℝ) (hQsharp : IsGroupInverse (1 - Q) Qsharp) :
    Gsharp * partitionIncidence G = partitionIncidence G * Qsharp := by
  let μ := pushforwardStationaryRow G π
  have hμsum : ∑ j : Y, μ j = 1 := by
    dsimp [μ]
    rw [pushforwardStationaryRow_sum, hπsum]
  have hμstat : ∀ j, ∑ i : Y, μ i * Q i j = μ j := by
    exact pushforwardStationaryRow_stationary G P Q π hπstat hintertwines
  exact groupInverse_intertwines_of_stationary_compatible
    P Q (partitionIncidence G) π μ hP hQ hPpos hQpos hπsum hμsum hπstat hμstat
    (partitionIncidence_row_sum G)
    (by intro j; rfl)
    hintertwines Gsharp hG Qsharp hQsharp

end InfoGeometry.QuantumContext.MarkovPartitionLumping

end
