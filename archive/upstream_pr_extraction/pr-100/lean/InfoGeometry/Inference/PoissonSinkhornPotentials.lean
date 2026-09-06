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
      Real.exp ((α i + β j - C.cost i j) / ε) + ε * (n : ℝ)

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

/-- Poisson-Bregman gap associated with a coupling and dual potentials. -/
noncomputable def poissonSinkhornBregmanGap
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (α β : Fin n → ℝ)
    (Pi : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ε * ∑ i : Fin n, ∑ j : Fin n,
    poissonBregman (Pi i j)
      (Real.exp ((α i + β j - C.cost i j) / ε))

theorem poissonSinkhornBregmanGap_nonneg
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (α β : Fin n → ℝ)
    (Pi : Matrix (Fin n) (Fin n) ℝ)
    (hPi : ∀ i j, 0 ≤ Pi i j) :
    0 ≤ poissonSinkhornBregmanGap C ε α β Pi := by
  unfold poissonSinkhornBregmanGap
  apply mul_nonneg hε
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact poissonBregman_nonneg (hPi i j) (Real.exp_pos _)

/-- The explicit entropic primal objective for a transport coupling. -/
noncomputable def poissonSinkhornPrimalObjective
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (Pi : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, C.cost i j * Pi i j) +
    ε * ∑ i : Fin n, ∑ j : Fin n, Pi i j * Real.log (Pi i j)

theorem poissonSinkhornPrimalDual_gap_eq_bregmanGap
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (hε : 0 < ε) (α β : Fin n → ℝ)
    (Pi : Matrix (Fin n) (Fin n) ℝ)
    (hPi_pos : ∀ i j, 0 < Pi i j)
    (hrow : ∀ i, ∑ j : Fin n, Pi i j = 1)
    (hcol : ∀ j, ∑ i : Fin n, Pi i j = 1) :
    poissonSinkhornPrimalObjective C ε Pi -
        poissonSinkhornDualObjective C ε α β =
      poissonSinkhornBregmanGap C ε α β Pi := by
  have hrow_weighted :
      (∑ i : Fin n, ∑ j : Fin n, α i * Pi i j) = ∑ i : Fin n, α i := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, α i * Pi i j) =
          ∑ i : Fin n, α i * (∑ j : Fin n, Pi i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ i : Fin n, α i := by simp_rw [hrow]; simp

  have hcol_weighted :
      (∑ i : Fin n, ∑ j : Fin n, β j * Pi i j) = ∑ j : Fin n, β j := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, β j * Pi i j) =
          ∑ j : Fin n, ∑ i : Fin n, β j * Pi i j := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n, β j * (∑ i : Fin n, Pi i j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
      _ = ∑ j : Fin n, β j := by simp_rw [hcol]; simp

  have hmass :
      (∑ i : Fin n, ∑ j : Fin n, Pi i j) = (n : ℝ) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, Pi i j) = ∑ i : Fin n, 1 := by
        simp_rw [hrow]
      _ = (n : ℝ) := by simp

  have hpoint : ∀ i j : Fin n,
      ε * poissonBregman (Pi i j)
          (Real.exp ((α i + β j - C.cost i j) / ε)) =
        ε * (Pi i j * Real.log (Pi i j)) -
          α i * Pi i j - β j * Pi i j - ε * Pi i j +
          C.cost i j * Pi i j +
          ε * Real.exp ((α i + β j - C.cost i j) / ε) := by
    intro i j
    rw [poissonBregman, if_neg (ne_of_gt (hPi_pos i j))]
    rw [Real.log_div (ne_of_gt (hPi_pos i j)) (Real.exp_pos _).ne']
    rw [Real.log_exp]
    field_simp [ne_of_gt hε]
    ring

  unfold poissonSinkhornPrimalObjective poissonSinkhornDualObjective
    poissonSinkhornBregmanGap
  rw [← hrow_weighted, ← hcol_weighted, ← hmass]
  calc
    (∑ i : Fin n, ∑ j : Fin n, C.cost i j * Pi i j) +
          ε * ∑ i : Fin n, ∑ j : Fin n, Pi i j * Real.log (Pi i j) -
        (∑ i : Fin n, ∑ j : Fin n, α i * Pi i j +
          ∑ i : Fin n, ∑ j : Fin n, β j * Pi i j -
          ε * ∑ i : Fin n, ∑ j : Fin n,
            Real.exp ((α i + β j - C.cost i j) / ε) +
          ε * ∑ i : Fin n, ∑ j : Fin n, Pi i j) =
      ∑ i : Fin n, ∑ j : Fin n,
        (ε * (Pi i j * Real.log (Pi i j)) - α i * Pi i j -
          β j * Pi i j - ε * Pi i j + C.cost i j * Pi i j +
          ε * Real.exp ((α i + β j - C.cost i j) / ε)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum]
            ring
    _ = ε * ∑ i : Fin n, ∑ j : Fin n,
        poissonBregman (Pi i j)
          (Real.exp ((α i + β j - C.cost i j) / ε)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [← hpoint i j]

theorem poissonSinkhornPrimalDual_gap_nonneg
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (hε : 0 < ε) (α β : Fin n → ℝ)
    (Pi : Matrix (Fin n) (Fin n) ℝ)
    (hPi_pos : ∀ i j, 0 < Pi i j)
    (hrow : ∀ i, ∑ j : Fin n, Pi i j = 1)
    (hcol : ∀ j, ∑ i : Fin n, Pi i j = 1) :
    0 ≤ poissonSinkhornPrimalObjective C ε Pi -
      poissonSinkhornDualObjective C ε α β := by
  rw [poissonSinkhornPrimalDual_gap_eq_bregmanGap C ε hε α β Pi
    hPi_pos hrow hcol]
  apply poissonSinkhornBregmanGap_nonneg C ε hε.le α β Pi
  intro i j
  exact (hPi_pos i j).le

end InfoGeometry.Inference
