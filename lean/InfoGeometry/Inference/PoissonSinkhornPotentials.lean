/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.PoissonSinkhornDualCertificate

/-!
# Finite Poisson Sinkhorn potentials

The row and column scaling factors are represented by additive potentials.
This file defines the corresponding finite dual functional and proves its
constant-shift gauge invariance. The inequality relating this dual to the
entropic primal is intentionally left for the Bregman decomposition step.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {n : Nat}

/-- Finite entropic dual functional for unit row and column marginals. -/
noncomputable def poissonSinkhornDualObjective
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (α β : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, α i) + (∑ j : Fin n, β j) -
    ε * ∑ i : Fin n, ∑ j : Fin n,
      Real.exp ((α i + β j - C.cost i j) / ε)

/-- The dual objective is invariant under the additive Weyl gauge
`α ↦ α + t`, `β ↦ β - t`. -/
theorem poissonSinkhornDualObjective_gauge_invariant
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε t : ℝ) (α β : Fin n → ℝ) :
    poissonSinkhornDualObjective C ε
        (fun i => α i + t) (fun j => β j - t) =
      poissonSinkhornDualObjective C ε α β := by
  unfold poissonSinkhornDualObjective
  have hmass :
      (∑ i : Fin n, (α i + t)) + (∑ j : Fin n, (β j - t)) =
        (∑ i : Fin n, α i) + (∑ j : Fin n, β j) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
  have hkernel :
      (∑ i : Fin n, ∑ j : Fin n,
          Real.exp (((α i + t) + (β j - t) - C.cost i j) / ε)) =
        ∑ i : Fin n, ∑ j : Fin n,
          Real.exp ((α i + β j - C.cost i j) / ε) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring
  rw [hmass, hkernel]

end InfoGeometry.Inference
