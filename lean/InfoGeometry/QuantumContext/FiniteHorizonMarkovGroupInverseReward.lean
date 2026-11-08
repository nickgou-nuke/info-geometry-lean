/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift

/-!
# Finite-horizon occupation identity from the Markov group inverse

For a full-matrix force in the range of the Markov Laplacian, the group
inverse gives an exact finite sum of propagated forces, with an endpoint
correction. This is a finite algebraic telescoping theorem: it makes no
asymptotic convergence claim and retains the noncommutative matrix carrier.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite cumulative propagation of a Laplacian-range matrix force is
the group-inverse potential minus its terminally propagated value. The
equation uses full matrix multiplication and assumes the exact Green relation
`(1 - P) * G * (1 - P) = 1 - P` plus actual range membership. The stochastic
corollary below supplies this relation from a full group-inverse witness. -/
theorem finiteHorizon_green_operator_reward
    [Nontrivial ι]
    (P G X : Matrix ι ι ℝ)
    (hGreen : (1 - P) * G * (1 - P) = 1 - P)
    (hX : X ∈ (mulLeftLinearMap ι ℝ (1 - P)).range)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, P ^ k * X =
      G * X - P ^ N * (G * X) := by
  obtain ⟨Z, hZ⟩ := LinearMap.mem_range.mp hX
  change (1 - P) * Z = X at hZ
  have hsolve : (1 - P) * (G * X) = X := by
    calc
      (1 - P) * (G * X) = (1 - P) * (G * ((1 - P) * Z)) := by rw [hZ]
      _ =
          ((1 - P) * G * (1 - P)) * Z := by noncomm_ring
      _ = (1 - P) * Z := by rw [hGreen]
      _ = X := hZ
  have hterm (n : ℕ) :
      P ^ n * X = P ^ n * (G * X) - P ^ (n + 1) * (G * X) := by
    calc
      P ^ n * X = P ^ n * ((1 - P) * (G * X)) := by rw [hsolve]
      _ =
          P ^ n * (G * X) - (P ^ n * P) * (G * X) := by noncomm_ring
      _ = P ^ n * (G * X) - P ^ (n + 1) * (G * X) := by
        rw [pow_succ]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, hterm]
      noncomm_ring

/-- Every finite row-stochastic operator admits a group-inverse potential
which satisfies the finite-horizon occupation identity for every full-matrix
force in the range of its left Laplacian action. -/
theorem exists_stochastic_finiteHorizon_groupInverse_reward
    [Nontrivial ι]
    (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (X : Matrix ι ι ℝ)
    (hX : X ∈ (markovLeftOnsager P).range)
    (N : ℕ) :
    ∃ G : Matrix ι ι ℝ,
      IsGroupInverse (1 - P) G ∧
      ∑ k ∈ Finset.range N, P ^ k * X =
        G * X - P ^ N * (G * X) := by
  obtain ⟨G, hG, _⟩ := exists_stochastic_markovLeft_groupInverse P hP
  refine ⟨G, hG, ?_⟩
  exact finiteHorizon_green_operator_reward P G X hG.1 (by
    simpa [markovLeftOnsager] using hX) N

end InfoGeometry.QuantumContext.MarkovDrazin
