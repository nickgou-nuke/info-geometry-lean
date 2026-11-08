/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import InfoGeometry.QuantumContext.GroupInverseIntertwinerAlgebra
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange
import InfoGeometry.QuantumContext.MarkovAttentionKemenySnell

/-!
# Rectangular transport of finite Markov group inverses

Full group-inverse transport follows from rectangular intertwining alone,
by `IntertwinerAlgebra.laplacian_groupInverse_intertwines`. The existing Markov
entry points retain their stochastic data for callers. Separately, positivity
and normalization identify the transported stationary distribution. Matrices
use column-observable multiplication (`mulVec`).
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- The existing stationary-compatible entry point for inverse transport.
Its conclusion follows from the group-inverse laws and `hintertwines` alone;
the stationary data are retained in the signature for existing callers.
`C` has shape `ι × κ`, mapping `κ`-observables to `ι`-observables. -/
theorem groupInverse_intertwines_of_stationary_compatible
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπsum : ∑ i, π i = 1) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ i, μ i * Q i j = μ j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hCmean : ∀ j, ∑ i, π i * C i j = μ j)
    (hintertwines : P * C = C * Q)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H) :
    G * C = C * H := by
  exact InfoGeometry.QuantumContext.IntertwinerAlgebra.laplacian_groupInverse_intertwines
    P Q C G H hG hH hintertwines

/-! The stationary-distribution result below is independent of inverse
transport and supplies the probabilistic interpretation of the intertwiner. -/

omit [DecidableEq ι] [Nonempty ι] in
/-- A nonnegative rectangular row-sum-one intertwiner transports normalized
stationary row distributions. The convention is row action on distributions:
`πᵀ P = πᵀ`, while matrices act on column observables by `mulVec`. -/
theorem stationaryMean_transport_of_stochastic_intertwiner
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hQpos : ∀ i j, 0 < Q i j)
    (hπnonneg : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμnonneg : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hμstat : ∀ j, ∑ j', μ j' * Q j' j = μ j)
    (hCnonneg : ∀ i j, 0 ≤ C i j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hintertwines : P * C = C * Q) :
    ∀ j, ∑ i, π i * C i j = μ j := by
  let ν : κ → ℝ := fun j => ∑ i, π i * C i j
  have hνnonneg (j : κ) : 0 ≤ ν j := by
    dsimp [ν]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hπnonneg i) (hCnonneg i j)
  have hνsum : ∑ j, ν j = 1 := by
    dsimp [ν]
    calc
      (∑ j, ∑ i, π i * C i j) = ∑ i, π i * ∑ j, C i j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ i, π i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hCrows i, mul_one]
      _ = 1 := hπsum
  have hνstat (j : κ) : ∑ k, ν k * Q k j = ν j := by
    calc
      (∑ k, ν k * Q k j) =
          ∑ i, π i * ∑ k, C i k * Q k j := by
        dsimp [ν]
        calc
          (∑ k, (∑ i, π i * C i k) * Q k j) =
              ∑ k, ∑ i, (π i * C i k) * Q k j := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.sum_mul]
          _ = ∑ i, ∑ k, (π i * C i k) * Q k j := by
            rw [Finset.sum_comm]
          _ = ∑ i, π i * ∑ k, C i k * Q k j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = ∑ i, π i * (C * Q) i j := by simp [Matrix.mul_apply]
      _ = ∑ i, π i * (P * C) i j := by rw [hintertwines]
      _ = ∑ i, π i * ∑ k, P i k * C k j := by simp [Matrix.mul_apply]
      _ = ∑ i, ∑ k, (π i * P i k) * C k j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ k, ∑ i, (π i * P i k) * C k j := by
        rw [Finset.sum_comm]
      _ = ∑ k, (∑ i, π i * P i k) * C k j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.sum_mul]
      _ = ∑ k, π k * C k j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hπstat k]
      _ = ν j := rfl
  have hνpos : ∀ j, 0 < ν j :=
    stationaryRowProbability_pos_of_pos_entries Q ν hQpos hνnonneg hνsum hνstat
  have hμpos : ∀ j, 0 < μ j :=
    stationaryRowProbability_pos_of_pos_entries Q μ hQpos hμnonneg hμsum hμstat
  obtain ⟨η, hη, hηunique⟩ :=
    existsUnique_positive_normalized_stationary_row Q hQ hQpos
  have hνη : ν = η := hηunique ν ⟨hνpos, hνsum, hνstat⟩
  have hμη : μ = η := hηunique μ ⟨hμpos, hμsum, hμstat⟩
  have hνμ : ν = μ := hνη.trans hμη.symm
  intro j
  calc
    (∑ i, π i * C i j) = ν j := rfl
    _ = μ j := congrFun hνμ j

/-- The existing stochastic entry point for inverse transport. The algebraic
transport conclusion uses only `P*C=C*Q` and the full group-inverse laws;
the stronger distribution-transport conclusion is proved separately above. -/
theorem groupInverse_intertwines_of_stochastic_compatible
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπnonneg : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hμnonneg : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ j', μ j' * Q j' j = μ j)
    (hCnonneg : ∀ i j, 0 ≤ C i j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hintertwines : P * C = C * Q)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H) :
    G * C = C * H := by
  exact InfoGeometry.QuantumContext.IntertwinerAlgebra.laplacian_groupInverse_intertwines
    P Q C G H hG hH hintertwines

end InfoGeometry.QuantumContext.MarkovDrazin

end
