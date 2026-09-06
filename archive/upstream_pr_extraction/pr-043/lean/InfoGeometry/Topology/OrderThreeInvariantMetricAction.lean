import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.ENNReal.Basic
import InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient

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

theorem min_three_le_add_min_three
    {a0 a1 a2 b0 b1 b2 c0 c1 c2 : ENNReal}
    (h00 : a0 ≤ b0 + c0) (h01 : a1 ≤ b0 + c1)
    (h02 : a2 ≤ b0 + c2) (h10 : a1 ≤ b1 + c0)
    (h11 : a2 ≤ b1 + c1) (h12 : a0 ≤ b1 + c2)
    (h20 : a2 ≤ b2 + c0) (h21 : a0 ≤ b2 + c1)
    (h22 : a1 ≤ b2 + c2) :
    min a0 (min a1 a2) ≤
      min b0 (min b1 b2) + min c0 (min c1 c2) := by
  have ha0 : min a0 (min a1 a2) ≤ a0 := min_le_left _ _
  have ha1 : min a0 (min a1 a2) ≤ a1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ha2 : min a0 (min a1 a2) ≤ a2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have h0 : min a0 (min a1 a2) ≤ b0 + min c0 (min c1 c2) := by
    rw [add_min, add_min]
    exact le_min (ha0.trans h00) (le_min
      (ha1.trans h01)
      (ha2.trans h02))
  have h1 : min a0 (min a1 a2) ≤ b1 + min c0 (min c1 c2) := by
    rw [add_min, add_min]
    exact le_min (ha1.trans h10) (le_min
      (ha2.trans h11)
      (ha0.trans h12))
  have h2 : min a0 (min a1 a2) ≤ b2 + min c0 (min c1 c2) := by
    rw [add_min, add_min]
    exact le_min (ha2.trans h20) (le_min
      (ha0.trans h21)
      (ha1.trans h22))
  have h12' : min a0 (min a1 a2) ≤
      min b1 b2 + min c0 (min c1 c2) := by
    rw [min_add]
    exact le_min h1 h2
  rw [min_add]
  exact le_min h0 h12'

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

theorem orbitCost_triangle (x y z : X) :
    orbitCost (D := D) x z ≤
      orbitCost (D := D) x y + orbitCost (D := D) y z := by
  have h00 : edist x z ≤ edist x y + edist y z :=
    edist_triangle x y z
  have h01 : edist x (D.action z) ≤
      edist x y + edist y (D.action z) :=
    edist_triangle x y (D.action z)
  have h02 : edist x (D.action (D.action z)) ≤
      edist x y + edist y (D.action (D.action z)) :=
    edist_triangle x y (D.action (D.action z))
  have h10 : edist x (D.action z) ≤
      edist x (D.action y) + edist y z := by
    calc
      edist x (D.action z) ≤
          edist x (D.action y) + edist (D.action y) (D.action z) :=
        edist_triangle x (D.action y) (D.action z)
      _ = edist x (D.action y) + edist y z := by
        rw [D.isometry y z]
  have h11 : edist x (D.action (D.action z)) ≤
      edist x (D.action y) + edist y (D.action z) := by
    calc
      edist x (D.action (D.action z)) ≤
          edist x (D.action y) +
            edist (D.action y) (D.action (D.action z)) :=
        edist_triangle x (D.action y) (D.action (D.action z))
      _ = edist x (D.action y) + edist y (D.action z) := by
        rw [D.isometry y (D.action z)]
  have h12 : edist x z ≤
      edist x (D.action y) + edist y (D.action (D.action z)) := by
    calc
      edist x z ≤ edist x (D.action y) + edist (D.action y) z :=
        edist_triangle x (D.action y) z
      _ = edist x (D.action y) + edist y (D.action (D.action z)) := by
        have h := (square_isometry D (D.action y) z).symm
        simpa [Function.comp_def, action_cube D] using congrArg (fun r => edist x (D.action y) + r) h
  have h20 : edist x (D.action (D.action z)) ≤
      edist x (D.action (D.action y)) + edist y z := by
    calc
      edist x (D.action (D.action z)) ≤
          edist x (D.action (D.action y)) +
            edist (D.action (D.action y)) (D.action (D.action z)) :=
        edist_triangle x (D.action (D.action y)) (D.action (D.action z))
      _ = edist x (D.action (D.action y)) + edist y z := by
        have h := square_isometry D y z
        simpa [Function.comp_def] using congrArg
          (fun r => edist x (D.action (D.action y)) + r) h
  have h21 : edist x z ≤
      edist x (D.action (D.action y)) + edist y (D.action z) := by
    calc
      edist x z ≤ edist x (D.action (D.action y)) +
          edist (D.action (D.action y)) z :=
        edist_triangle x (D.action (D.action y)) z
      _ = edist x (D.action (D.action y)) + edist y (D.action z) := by
        have h := (D.isometry (D.action (D.action y)) z).symm
        simpa [action_cube D] using congrArg
          (fun r => edist x (D.action (D.action y)) + r) h
  have h22 : edist x (D.action z) ≤
      edist x (D.action (D.action y)) + edist y (D.action (D.action z)) := by
    calc
      edist x (D.action z) ≤
          edist x (D.action (D.action y)) +
            edist (D.action (D.action y)) (D.action z) :=
        edist_triangle x (D.action (D.action y)) (D.action z)
      _ = edist x (D.action (D.action y)) +
          edist y (D.action (D.action z)) := by
        have h := (D.isometry (D.action (D.action y)) (D.action z)).symm
        simpa [action_cube D] using congrArg
          (fun r => edist x (D.action (D.action y)) + r) h
  unfold orbitCost
  exact min_three_le_add_min_three h00 h01 h02 h10 h11 h12 h20 h21 h22

@[simp] theorem orbitCost_self (x : X) :
    orbitCost (D := D) x x = 0 := by
  simp [orbitCost]

theorem orbitCost_eq_zero_iff
    {X : Type*} [MetricSpace X]
    (D : Data X) (x y : X) :
    orbitCost D x y = 0 ↔
      x = y ∨ x = D.action y ∨ x = D.action (D.action y) := by
  constructor
  · intro h
    have h' :
        edist x y = 0 ∨
          edist x (D.action y) = 0 ∨
            edist x (D.action (D.action y)) = 0 := by
      simpa [orbitCost] using h
    rcases h' with h' | h' | h'
    · exact Or.inl (edist_eq_zero.mp h')
    · exact Or.inr (Or.inl (edist_eq_zero.mp h'))
    · exact Or.inr (Or.inr (edist_eq_zero.mp h'))
  · intro h
    rcases h with h | h | h
    · simp [orbitCost, h]
    · simp [orbitCost, h]
    · simp [orbitCost, h]

theorem orbitCost_eq_zero_iff_orbitRelation
    {X : Type*} [MetricSpace X]
    (D : Data X) (x y : X) :
    orbitCost D x y = 0 ↔
      OrderThreeHomeomorphOrbitQuotient.orbitRelation D.action y x := by
  rw [orbitCost_eq_zero_iff]
  rfl

theorem orbitCost_right_action (x y : X) :
    orbitCost (D := D) x (D.action y) = orbitCost (D := D) x y := by
  unfold orbitCost
  have h₃ : edist x (D.action (D.action (D.action y))) = edist x y := by
    rw [action_cube D]
  rw [h₃]
  simp [min_comm, min_left_comm]

theorem orbitCost_le_direct (x y : X) :
    orbitCost (D := D) x y ≤ edist x y := by
  unfold orbitCost
  exact min_le_left _ _

theorem orbitCost_le_first_action (x y : X) :
    orbitCost (D := D) x y ≤ edist x (D.action y) := by
  unfold orbitCost
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem orbitCost_le_second_action (x y : X) :
    orbitCost (D := D) x y ≤ edist x (D.action (D.action y)) := by
  unfold orbitCost
  exact (min_le_right _ _).trans (min_le_right _ _)

theorem orbitCost_le_direct_triangle (x y z : X) :
    orbitCost (D := D) x z ≤ edist x y + edist y z := by
  exact (orbitCost_le_direct D x z).trans (edist_triangle x y z)

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

theorem orbitCost_left_action_independent (x y : X) :
    orbitCost (D := D) (D.action x) y = orbitCost (D := D) x y := by
  calc
    orbitCost (D := D) (D.action x) y =
        orbitCost (D := D) (D.action x)
          (D.action (D.action (D.action y))) := by
      rw [action_cube D y]
    _ = orbitCost (D := D) x (D.action (D.action y)) := by
      exact orbitCost_left_action D x (D.action (D.action y))
    _ = orbitCost (D := D) x (D.action y) := by
      exact orbitCost_right_action D x (D.action y)
    _ = orbitCost (D := D) x y := by
      exact orbitCost_right_action D x y

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
