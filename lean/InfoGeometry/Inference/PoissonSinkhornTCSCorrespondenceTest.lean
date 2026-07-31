import InfoGeometry.Inference.PoissonSinkhornTCSCorrespondence

open scoped BigOperators

namespace InfoGeometry.Inference

/-! A concrete finite smoke test for the Python/Lean contract. -/

def smokeCost : PoissonTransportCost (Observation := Fin 2) (Component := Fin 2) where
  cost := fun i j => if i = j then 0 else 1
  cost_nonneg := by
    intro i j
    split <;> norm_num

def smokeX : Fin 2 → ℝ := fun _ => 1

def smokeLiveTime : Fin 2 → ℝ := fun _ => 1

def smokeObserved : Fin 2 → ℝ := fun i => if i = 0 then 1 else 2

def smokeComponent : Fin 2 → TCSParameter smokeX smokeLiveTime := fun _ =>
  { C := 2
    K := 1
    mean_pos := by
      intro i
      simp [smokeX, smokeLiveTime] }

example (i : Fin 2) :
    ∑ j : Fin 2, poissonTransportAssignment smokeCost ε i j = 1 := by
  exact poissonTransportAssignment_row_sum_one smokeCost ε i

example (ε : ℝ) :
    0 ≤ weightedPoissonTransportEnergy smokeCost
      (fun i j => poissonTransportAssignment smokeCost ε i j) := by
  apply weightedPoissonTransportEnergy_nonneg
  intro i j
  exact poissonTransportAssignment_nonneg smokeCost ε i j

example (ε : ℝ) (i : Fin 2) :
    0 ≤ (tcsPoissonTransportCost (x := smokeX)
      (liveTime := smokeLiveTime) (observed := smokeObserved)
      (by intro k; simp [smokeObserved]; split <;> norm_num)
      smokeComponent).cost i 0 := by
  exact (tcsPoissonTransportCost
    (x := smokeX) (liveTime := smokeLiveTime) (observed := smokeObserved)
    (by intro k; simp [smokeObserved]; split <;> norm_num)
    smokeComponent).cost_nonneg i 0

end InfoGeometry.Inference
