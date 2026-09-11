/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.PoissonSinkhornPrimalDual
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Balanced Poisson Sinkhorn property

This module connects the row-wise Gibbs variational property to the
matrix-level balanced coupling interface. The result is deliberately finite:
it certifies unit marginals and a nonnegative summed primal-dual gap, while
leaving numerical convergence of an iterative Sinkhorn implementation to its
own solver and tests.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

open InfoGeometry.Canonical.MoE

variable {n : Nat} [Nonempty (Fin n)]

/-- A Poisson transport coupling together with its balanced-marginal property. -/
def PoissonSinkhornBalancedCertificate
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) : Type _ :=
  {coupling : Matrix (Fin n) (Fin n) ℝ //
    coupling ∈ doublyStochastic ℝ (Fin n)}

namespace PoissonSinkhornBalancedCertificate

/-- Native subtype projection for the transport coupling. -/
abbrev coupling
    {C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)}
    {ε : ℝ}
    (cert : PoissonSinkhornBalancedCertificate C ε) :
    Matrix (Fin n) (Fin n) ℝ :=
  cert.1

/-- Native subtype proof that the coupling is doubly stochastic. -/
theorem balanced
    {C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)}
    {ε : ℝ}
    (cert : PoissonSinkhornBalancedCertificate C ε) :
    cert.coupling ∈ doublyStochastic ℝ (Fin n) :=
  cert.2

end PoissonSinkhornBalancedCertificate

/- A balanced coupling has unit row and column marginals. -/
theorem PoissonSinkhornBalancedCertificate.has_unit_marginals
    {C : PoissonTransportCost (Observation := Fin n) (Component := Fin n)}
    {ε : ℝ}
    (cert : PoissonSinkhornBalancedCertificate C ε) :
    HasMarginals n cert.coupling (fun _ => 1) (fun _ => 1) := by
  have hbalanced := cert.balanced
  rw [mem_doublyStochastic_iff_sum] at hbalanced
  exact ⟨hbalanced.2.1, hbalanced.2.2⟩

/-- The row-wise entropy-regularized primal-dual gap. -/
noncomputable def poissonSinkhornRowGap
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (i : Fin n) (q : Fin n → ℝ) : ℝ :=
  FiniteGibbs.entropyRegularizedObjective
      (poissonTransportRowModel C i) () ε q -
    FiniteGibbs.freeEnergy (poissonTransportRowModel C i) () ε

theorem poissonSinkhornRowGap_nonneg
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (hε : 0 < ε) (i : Fin n)
    (q : Fin n → ℝ)
    (hq_pos : ∀ j, 0 < q j)
    (hq_sum : ∑ j : Fin n, q j = 1) :
    0 ≤ poissonSinkhornRowGap C ε i q := by
  unfold poissonSinkhornRowGap
  exact sub_nonneg.mpr
    (poissonTransportRow_primalDual_gap_nonneg C ε hε i q hq_pos hq_sum)

/-- Summing the row certificates preserves nonnegativity. -/
theorem poissonSinkhornTotalRowGap_nonneg
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (hε : 0 < ε)
    (q : Fin n → Fin n → ℝ)
    (hq_pos : ∀ i j, 0 < q i j)
    (hq_sum : ∀ i, ∑ j : Fin n, q i j = 1) :
    0 ≤ ∑ i : Fin n, poissonSinkhornRowGap C ε i (q i) := by
  exact Finset.sum_nonneg (fun i _ =>
    poissonSinkhornRowGap_nonneg C ε hε i (q i)
      (hq_pos i) (hq_sum i))

end InfoGeometry.Inference
