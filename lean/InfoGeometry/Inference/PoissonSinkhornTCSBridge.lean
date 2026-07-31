/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.TCSPoissonModel
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Inference.FisherVariance

/-!
# Poisson transport bridge for TCS mixtures

This module formalizes the finite contract shared by the Python transport
testbench and the TCS inference model.  A nonnegative Poisson-Bregman cost
matrix is converted into a row-normalized Gibbs assignment kernel.  The
kernel is an evidence assignment, not an outlier posterior and not a proof
that a numerical Sinkhorn iteration converges.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

section FinitePoissonTransport

variable {Observation Component : Type*}
  [Fintype Component] [Nonempty Component]

/-- A finite nonnegative cost matrix for observation/component assignments. -/
structure PoissonTransportCost where
  cost : Observation → Component → ℝ
  cost_nonneg : ∀ i j, 0 ≤ cost i j

/-- The row Gibbs assignment induced by a Poisson transport cost. -/
noncomputable def poissonTransportAssignment
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ)
    (i : Observation) (j : Component) : ℝ :=
  Real.exp (-C.cost i j / ε) /
    ∑ k : Component, Real.exp (-C.cost i k / ε)

theorem poissonTransportAssignment_pos
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ)
    (i : Observation) (j : Component) :
    0 < poissonTransportAssignment C ε i j := by
  unfold poissonTransportAssignment
  exact div_pos (Real.exp_pos _)
    (Finset.sum_pos (fun k _ => Real.exp_pos _)
      Finset.univ_nonempty)

theorem poissonTransportAssignment_nonneg
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ)
    (i : Observation) (j : Component) :
    0 ≤ poissonTransportAssignment C ε i j :=
  (poissonTransportAssignment_pos C ε i j).le

/-- Every observation distributes unit mass across the candidate components. -/
theorem poissonTransportAssignment_row_sum_one
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ) (i : Observation) :
    ∑ j : Component, poissonTransportAssignment C ε i j = 1 := by
  classical
  unfold poissonTransportAssignment
  have hZ : (∑ k : Component, Real.exp (-C.cost i k / ε)) ≠ 0 := by
    exact (Finset.sum_pos (fun k _ => Real.exp_pos _)
      Finset.univ_nonempty).ne'
  calc
    ∑ j : Component,
        Real.exp (-C.cost i j / ε) /
          ∑ k : Component, Real.exp (-C.cost i k / ε)
        = (∑ j : Component, Real.exp (-C.cost i j / ε)) /
            ∑ k : Component, Real.exp (-C.cost i k / ε) := by
              simp_rw [div_eq_mul_inv]
              rw [Finset.sum_mul]
    _ = 1 := by
      exact div_self hZ

/-- Poisson-Bregman costs form an admissible transport-cost matrix. -/
noncomputable def tcsPoissonTransportCost
    {x liveTime observed : Observation → ℝ}
    (hobs : ∀ i, 0 ≤ observed i)
    (components : Component → TCSParameter x liveTime) :
    PoissonTransportCost (Observation := Observation)
      (Component := Component) where
  cost := fun i j =>
    poissonBregman (observed i)
      (tcsMean (components j) i)
  cost_nonneg := by
    intro i j
    exact poissonBregman_nonneg (hobs i)
      ((components j).mean_pos i)

theorem tcsPoissonTransportAssignment_row_sum_one
    {x liveTime observed : Observation → ℝ}
    (hobs : ∀ i, 0 ≤ observed i)
    (components : Component → TCSParameter x liveTime)
    (ε : ℝ) (i : Observation) :
    ∑ j : Component,
      poissonTransportAssignment
        (tcsPoissonTransportCost hobs components) ε i j = 1 :=
  poissonTransportAssignment_row_sum_one
    (tcsPoissonTransportCost hobs components) ε i

section BalancedCoupling

variable {n : Nat} [Nonempty (Fin n)]

/-!
The square specialization is the interface to the existing finite Sinkhorn
foundation.  Row normalization is automatic; column normalization is an
additional certificate and must not be inferred from the row calculation.
-/

/-- Square Poisson transport assignment matrix. -/
noncomputable def poissonTransportMatrix
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => poissonTransportAssignment C ε i j

lemma poissonTransportMatrix_nonneg
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (i j : Fin n) :
    0 ≤ poissonTransportMatrix C ε i j := by
  exact poissonTransportAssignment_nonneg C ε i j

lemma poissonTransportMatrix_row_sum_one
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) (i : Fin n) :
    ∑ j : Fin n, poissonTransportMatrix C ε i j = 1 := by
  exact poissonTransportAssignment_row_sum_one C ε i

/-- Column balance required to turn row Gibbs assignments into a balanced plan. -/
def IsColumnBalancedPoissonTransport
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ) : Prop :=
  ∀ j : Fin n, ∑ i : Fin n, poissonTransportMatrix C ε i j = 1

theorem poissonTransportMatrix_mem_doublyStochastic
    (C : PoissonTransportCost (Observation := Fin n) (Component := Fin n))
    (ε : ℝ)
    (hcol : IsColumnBalancedPoissonTransport C ε) :
    poissonTransportMatrix C ε ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact poissonTransportMatrix_nonneg C ε i j
  · intro i
    exact poissonTransportMatrix_row_sum_one C ε i
  · intro j
    exact hcol j

end BalancedCoupling

section WeightedEnergy

variable [Fintype Observation]

/-- Weighted Poisson transport energy used by one component M-step. -/
noncomputable def weightedPoissonTransportEnergy
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (w : Observation → Component → ℝ) : ℝ :=
  ∑ i : Observation, ∑ j : Component, w i j * C.cost i j

omit [Nonempty Component] in
theorem weightedPoissonTransportEnergy_nonneg
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (w : Observation → Component → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) :
    0 ≤ weightedPoissonTransportEnergy C w := by
  unfold weightedPoissonTransportEnergy
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (hw i j) (C.cost_nonneg i j)

end WeightedEnergy

section TransportFisher

variable [Fintype Observation]

/-- Assignment weights received by one candidate TCS component. -/
noncomputable def componentTransportWeights
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (ε : ℝ) (j : Component) : Observation → ℝ :=
  fun i => poissonTransportAssignment C ε i j

/-- Fisher information reweighted by one transport component's assignments. -/
noncomputable def componentTransportFisherInformation
    {x liveTime : Observation → ℝ}
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (ε : ℝ) (j : Component) : Matrix (Fin 2) (Fin 2) ℝ :=
  tcsFisherInformation (componentTransportWeights C ε j) liveTime x

theorem componentTransportFisher_quadratic_nonneg
    {x liveTime : Observation → ℝ}
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (ε : ℝ) (j : Component) (v : Fin 2 → ℝ) :
    0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      v a * componentTransportFisherInformation (x := x) (liveTime := liveTime) C ε j a b * v b := by
  apply fisherInformation_quadratic_nonneg
    (w := componentTransportWeights C ε j)
    (sensitivity := fun i => tcsSensitivity (liveTime i) (x i))
  intro i
  exact (poissonTransportAssignment_nonneg C ε i j)

end TransportFisher

end FinitePoissonTransport

end InfoGeometry.Inference
