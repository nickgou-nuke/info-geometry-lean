import InfoGeometry.Inference.PoissonSinkhornPotentials

open scoped BigOperators

namespace InfoGeometry.Inference

def potentialSmokeCost :
    PoissonTransportCost (Observation := Fin 2) (Component := Fin 2) where
  cost := fun i j => if i = j then 0 else 1
  cost_nonneg := by
    intro i j
    split <;> norm_num

noncomputable def potentialSmokeCoupling : Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ _ => (1 : ℝ) / 2

example :
    0 ≤ poissonSinkhornPrimalObjective potentialSmokeCost 1
        potentialSmokeCoupling -
      poissonSinkhornDualObjective potentialSmokeCost 1
        (fun _ => 0) (fun _ => 0) := by
  apply poissonSinkhornPrimalDual_gap_nonneg potentialSmokeCost 1
    (by norm_num) (fun _ => 0) (fun _ => 0) potentialSmokeCoupling
  · intro i j
    simp [potentialSmokeCoupling]
  · intro i
    fin_cases i <;> norm_num [potentialSmokeCoupling]
  · intro j
    fin_cases j <;> norm_num [potentialSmokeCoupling]

example :
    poissonSinkhornPrimalObjective potentialSmokeCost 1
        potentialSmokeCoupling -
      poissonSinkhornDualObjective potentialSmokeCost 1
        (fun _ => 0) (fun _ => 0) =
    poissonSinkhornBregmanGap potentialSmokeCost 1
        (fun _ => 0) (fun _ => 0) potentialSmokeCoupling := by
  apply poissonSinkhornPrimalDual_gap_eq_bregmanGap potentialSmokeCost 1
    (by norm_num) (fun _ => 0) (fun _ => 0) potentialSmokeCoupling
  · intro i j
    simp [potentialSmokeCoupling]
  · intro i
    fin_cases i <;> norm_num [potentialSmokeCoupling]
  · intro j
    fin_cases j <;> norm_num [potentialSmokeCoupling]

end InfoGeometry.Inference
