/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.PoissonSinkhornTCSBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# End-to-end finite correspondence packet

This file is the small kernel-checked acceptance boundary shared by the
Python testbench and the native Lean model.  It assembles the contracts in
the order used by the implementation, while leaving numerical optimization
and convergence as executable-code obligations.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Observation Component : Type*}
  [Fintype Observation] [Nonempty Observation]
  [Fintype Component] [Nonempty Component]

omit [Nonempty Observation] in
theorem poissonSinkhornTCS_contract
    {x liveTime observed : Observation → ℝ}
    (hobs : ∀ i, 0 ≤ observed i)
    (components : Component → TCSParameter x liveTime)
    (ε : ℝ) (j : Component) (v : Fin 2 → ℝ)
    (hI : FisherInverseContract
      (componentTransportFisherInformation
        (x := x) (liveTime := liveTime)
        (tcsPoissonTransportCost hobs components) ε j)) :
    (∀ i : Observation,
      ∑ k : Component,
        poissonTransportAssignment
          (tcsPoissonTransportCost hobs components) ε i k = 1) ∧
    (0 ≤ weightedPoissonTransportEnergy
      (tcsPoissonTransportCost hobs components)
      (fun i k => poissonTransportAssignment
        (tcsPoissonTransportCost hobs components) ε i k)) ∧
    (0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      v a * componentTransportFisherInformation
        (x := x) (liveTime := liveTime)
        (tcsPoissonTransportCost hobs components) ε j a b * v b) ∧
    (0 ≤ componentTransportLocalVariance
      (x := x) (liveTime := liveTime)
      (tcsPoissonTransportCost hobs components) ε j hI v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact poissonTransportAssignment_row_sum_one
      (tcsPoissonTransportCost hobs components) ε i
  · apply weightedPoissonTransportEnergy_nonneg
    intro i k
    exact poissonTransportAssignment_nonneg
      (tcsPoissonTransportCost hobs components) ε i k
  · exact componentTransportFisher_quadratic_nonneg
      (tcsPoissonTransportCost hobs components) ε j v
  · exact componentTransportLocalVariance_nonneg
      (tcsPoissonTransportCost hobs components) ε j hI v

end InfoGeometry.Inference
