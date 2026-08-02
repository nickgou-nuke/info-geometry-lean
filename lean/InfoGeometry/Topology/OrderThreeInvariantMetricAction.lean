import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.ENNReal.Basic

/-!
# Metric-compatible order-three actions

This owner records the metric prerequisite for a later orbit/quotient metric.
It deliberately stops before asserting that an orbit pseudometric is a metric
or that its topology is the quotient topology.
-/

namespace InfoGeometry.Topology.OrderThreeInvariantMetricAction

structure Data (X : Type*) [PseudoMetricSpace X] where
  action : X ≃ₜ X
  cube : ∀ x, action (action (action x)) = x
  isometry : Isometry action

variable {X : Type*} [PseudoMetricSpace X]
variable (D : Data X)

@[simp] theorem action_cube (x : X) :
    D.action (D.action (D.action x)) = x :=
  D.cube x

theorem action_isometry (x y : X) :
    edist (D.action x) (D.action y) = edist x y :=
  D.isometry x y

theorem inverse_isometry : Isometry D.action.symm := by
  intro x y
  have h := D.isometry (D.action.symm x) (D.action.symm y)
  simpa using h.symm

theorem square_isometry : Isometry (D.action ∘ D.action) :=
  D.isometry.comp D.isometry

def orbitCost (x y : X) : ENNReal :=
  min (edist x y)
    (min (edist x (D.action y))
      (edist x (D.action (D.action y))))

@[simp] theorem orbitCost_self (x : X) :
    orbitCost (D := D) x x = 0 := by
  simp [orbitCost]

theorem orbitCost_right_action (x y : X) :
    orbitCost (D := D) x (D.action y) = orbitCost (D := D) x y := by
  unfold orbitCost
  have h₃ : edist x (D.action (D.action (D.action y))) = edist x y := by
    rw [action_cube D]
  rw [h₃]
  simp [min_comm, min_left_comm]

theorem orbitCost_left_action (x y : X) :
    orbitCost (D := D) (D.action x) (D.action y) =
      orbitCost (D := D) x y := by
  unfold orbitCost
  rw [D.isometry x y]
  rw [D.isometry x (D.action y)]
  rw [D.isometry x (D.action (D.action y))]

theorem orbitCost_action_action (x y : X) :
    orbitCost (D := D) (D.action x) (D.action (D.action y)) =
      orbitCost (D := D) x y := by
  calc
    orbitCost (D := D) (D.action x) (D.action (D.action y)) =
        orbitCost (D := D) (D.action x) (D.action y) := by
          exact orbitCost_right_action D (D.action x) (D.action y)
    _ = orbitCost (D := D) (D.action x) y := by
          exact orbitCost_right_action D (D.action x) y
    _ = orbitCost (D := D) (D.action x) (D.action y) := by
          exact (orbitCost_right_action D (D.action x) y).symm
    _ = orbitCost (D := D) x y := orbitCost_left_action D x y

theorem orbitCost_symm (x y : X) :
    orbitCost (D := D) x y = orbitCost (D := D) y x := by
  have h₁ : edist y (D.action x) =
      edist x (D.action (D.action y)) := by
    calc
      edist y (D.action x) =
          edist (D.action (D.action y))
            (D.action (D.action (D.action x))) := by
        simpa [Function.comp_def] using
          (square_isometry D y (D.action x)).symm
      _ = edist (D.action (D.action y)) x := by
        rw [action_cube D]
      _ = edist x (D.action (D.action y)) := edist_comm _ _
  have h₂ : edist y (D.action (D.action x)) =
      edist x (D.action y) := by
    calc
      edist y (D.action (D.action x)) =
          edist (D.action y)
            (D.action (D.action (D.action x))) := by
        simpa using (D.isometry y (D.action (D.action x))).symm
      _ = edist (D.action y) x := by
        rw [action_cube D]
      _ = edist x (D.action y) := edist_comm _ _
  unfold orbitCost
  rw [edist_comm x y, h₁, h₂]
  simp [min_comm]

end InfoGeometry.Topology.OrderThreeInvariantMetricAction
