import InfoGeometry.Inference.PoissonSinkhornDualCertificate

open scoped BigOperators

namespace InfoGeometry.Inference

open InfoGeometry.Canonical.MoE

def certificateSmokeCost :
    PoissonTransportCost (Observation := Fin 2) (Component := Fin 2) where
  cost := fun i j => if i = j then 0 else 1
  cost_nonneg := by
    intro i j
    split <;> norm_num

def certificateSmokeCoupling : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then 1 else 0

def certificateSmoke :
    PoissonSinkhornBalancedCertificate certificateSmokeCost 1 :=
  ⟨certificateSmokeCoupling, by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      by_cases h : i = j <;> simp [certificateSmokeCoupling, h]
    · intro i
      fin_cases i <;> norm_num [certificateSmokeCoupling]
    · intro j
      fin_cases j <;> norm_num [certificateSmokeCoupling]
  ⟩

example :
    HasMarginals 2 certificateSmoke.coupling (fun _ => 1) (fun _ => 1) :=
  certificateSmoke.has_unit_marginals

example (ε : ℝ) (hε : 0 < ε)
    (q : Fin 2 → Fin 2 → ℝ)
    (hq_pos : ∀ i j, 0 < q i j)
    (hq_sum : ∀ i, ∑ j : Fin 2, q i j = 1) :
    0 ≤ ∑ i : Fin 2, poissonSinkhornRowGap certificateSmokeCost ε i (q i) :=
  poissonSinkhornTotalRowGap_nonneg certificateSmokeCost ε hε q hq_pos hq_sum

end InfoGeometry.Inference
