import InfoGeometry.Inference.PoissonSinkhornDualCertificate

open scoped BigOperators

namespace InfoGeometry.Inference

open InfoGeometry.Canonical.MoE

def propertySmokeCost :
    PoissonTransportCost (Observation := Fin 2) (Component := Fin 2) where
  cost := fun i j => if i = j then 0 else 1
  cost_nonneg := by
    intro i j
    split <;> norm_num

def propertySmokeCoupling : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then 1 else 0

def propertySmoke :
    PoissonSinkhornBalancedCertificate propertySmokeCost 1 :=
  ⟨propertySmokeCoupling, by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      by_cases h : i = j <;> simp [propertySmokeCoupling, h]
    · intro i
      fin_cases i <;> norm_num [propertySmokeCoupling]
    · intro j
      fin_cases j <;> norm_num [propertySmokeCoupling]
  ⟩

example :
    HasMarginals 2 propertySmoke.coupling (fun _ => 1) (fun _ => 1) :=
  propertySmoke.has_unit_marginals

example (ε : ℝ) (hε : 0 < ε)
    (q : Fin 2 → Fin 2 → ℝ)
    (hq_pos : ∀ i j, 0 < q i j)
    (hq_sum : ∀ i, ∑ j : Fin 2, q i j = 1) :
    0 ≤ ∑ i : Fin 2, poissonSinkhornRowGap propertySmokeCost ε i (q i) :=
  poissonSinkhornTotalRowGap_nonneg propertySmokeCost ε hε q hq_pos hq_sum

end InfoGeometry.Inference
