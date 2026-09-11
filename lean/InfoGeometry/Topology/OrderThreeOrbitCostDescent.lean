import InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.OrderThreeInvariantMetricAction

/-!
# Descent of the order-three orbit cost

This owner descends the already verified orbit cost to the coarse orbit
quotient.  It proves representative independence and the descended triangle
inequality, but deliberately does not install a metric instance: separation
and comparison with the quotient topology are separate obligations.
-/

noncomputable section

namespace InfoGeometry.Topology.OrderThreeOrbitCostDescent

open OrderThreeHomeomorphOrbitQuotient
open OrderThreeInvariantMetricAction

variable {X : Type*} [PseudoMetricSpace X]
variable (D : Data X)

theorem orbitCost_respects_right
    {x y z : X}
    (h : orbitRelation D.action y z) :
    orbitCost D x y = orbitCost D x z := by
  rcases h with rfl | rfl | rfl
  · rfl
  · exact (orbitCost_right_action D x y).symm
  · calc
      orbitCost D x y = orbitCost D x (D.action y) :=
        (orbitCost_right_action D x y).symm
      _ = orbitCost D x (D.action (D.action y)) :=
        (orbitCost_right_action D x (D.action y)).symm

theorem orbitCost_respects_left
    {x y z : X}
    (h : orbitRelation D.action x z) :
    orbitCost D x y = orbitCost D z y := by
  rcases h with rfl | rfl | rfl
  · rfl
  · exact (orbitCost_left_action_independent D x y).symm
  · calc
      orbitCost D x y = orbitCost D (D.action x) y :=
        (orbitCost_left_action_independent D x y).symm
      _ = orbitCost D (D.action (D.action x)) y := by
        exact (orbitCost_left_action_independent D (D.action x) y).symm

noncomputable def descendedOrbitCost
    (p q : OrbitSpace D.action D.cube) : ENNReal :=
  Quotient.lift
    (fun x =>
      Quotient.lift
        (fun y => orbitCost D x y)
        (fun y z h => orbitCost_respects_right D h))
    (by
      intro x z h
      funext q
      refine Quotient.inductionOn q ?_
      intro y
      exact orbitCost_respects_left D h)
    p q

/-- The descended extended distance carrier, before adding uniformity data. -/
noncomputable def orbitCostEDist : EDist (OrbitSpace D.action D.cube) where
  edist := descendedOrbitCost D

@[simp] theorem orbitCostEDist_apply
    (p q : OrbitSpace D.action D.cube) :
    @edist (OrbitSpace D.action D.cube) (orbitCostEDist D) p q =
      descendedOrbitCost D p q := rfl

@[simp] theorem descendedOrbitCost_projection
    (x y : X) :
    descendedOrbitCost D
        (orbitProjection D.action D.cube x)
        (orbitProjection D.action D.cube y) =
      orbitCost D x y := by
  rfl

theorem orbitProjection_nonexpansive
    (x y : X) :
    descendedOrbitCost D
        (orbitProjection D.action D.cube x)
        (orbitProjection D.action D.cube y) ≤
      edist x y := by
  rw [descendedOrbitCost_projection]
  exact orbitCost_le_direct D x y

theorem descendedOrbitCost_self
    (p : OrbitSpace D.action D.cube) :
    descendedOrbitCost D p p = 0 := by
  refine Quotient.inductionOn p ?_
  intro x
  simp [descendedOrbitCost]

theorem descendedOrbitCost_eq_zero_iff
    {X : Type*} [MetricSpace X]
    (D : Data X)
    (p q : OrbitSpace D.action D.cube) :
    descendedOrbitCost D p q = 0 ↔ p = q := by
  refine Quotient.inductionOn p ?_
  intro x
  refine Quotient.inductionOn q ?_
  intro y
  constructor
  · intro h
    have h' :
        x = y ∨ x = D.action y ∨
          x = D.action (D.action y) := by
      simpa [descendedOrbitCost] using
        (orbitCost_eq_zero_iff D x y).mp h
    rcases h' with h' | h' | h'
    · simpa [h']
    · subst x
      exact orbitProjection_apply D.action D.cube y
    · subst x
      calc
        orbitProjection D.action D.cube
            (D.action (D.action y)) =
            orbitProjection D.action D.cube (D.action y) := by
              exact orbitProjection_apply D.action D.cube (D.action y)
        _ = orbitProjection D.action D.cube y := by
          exact orbitProjection_apply D.action D.cube y
  · intro h
    rw [h]
    exact descendedOrbitCost_self D (orbitProjection D.action D.cube y)

theorem descendedOrbitCost_symm
    (p q : OrbitSpace D.action D.cube) :
    descendedOrbitCost D p q = descendedOrbitCost D q p := by
  refine Quotient.inductionOn p ?_
  intro x
  refine Quotient.inductionOn q ?_
  intro y
  simp [descendedOrbitCost, orbitCost_symm]

theorem descendedOrbitCost_triangle
    (p q r : OrbitSpace D.action D.cube) :
    descendedOrbitCost D p r ≤
      descendedOrbitCost D p q + descendedOrbitCost D q r := by
  refine Quotient.inductionOn p ?_
  intro x
  refine Quotient.inductionOn q ?_
  intro y
  refine Quotient.inductionOn r ?_
  intro z
  simpa [descendedOrbitCost] using orbitCost_triangle D x y z

end InfoGeometry.Topology.OrderThreeOrbitCostDescent
