import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace InfoGeometry.LatticeGauge

structure PlaquetteLattice (Vertex Edge Face : Type*) where
  source : Edge → Vertex
  target : Edge → Vertex
  bottom : Face → Edge
  right : Face → Edge
  top : Face → Edge
  left : Face → Edge
  bottom_right : ∀ face, target (bottom face) = source (right face)
  right_top : ∀ face, target (right face) = target (top face)
  top_left : ∀ face, source (top face) = target (left face)
  left_bottom : ∀ face, source (left face) = source (bottom face)

variable {Vertex Edge Face Gauge : Type*} [Group Gauge]

abbrev Configuration (Edge Gauge : Type*) := Edge → Gauge

def gaugeTransform (lattice : PlaquetteLattice Vertex Edge Face)
    (gauge : Vertex → Gauge) (links : Configuration Edge Gauge) : Configuration Edge Gauge :=
  fun edge => gauge (lattice.source edge) * links edge * (gauge (lattice.target edge))⁻¹

def plaquetteHolonomy (lattice : PlaquetteLattice Vertex Edge Face)
    (links : Configuration Edge Gauge) (face : Face) : Gauge :=
  links (lattice.bottom face) * links (lattice.right face) *
    (links (lattice.top face))⁻¹ * (links (lattice.left face))⁻¹

theorem gaugeTransform_identity (lattice : PlaquetteLattice Vertex Edge Face)
    (links : Configuration Edge Gauge) :
    gaugeTransform lattice (fun _ => 1) links = links := by
  funext edge
  simp [gaugeTransform]

theorem gaugeTransform_comp (lattice : PlaquetteLattice Vertex Edge Face)
    (outer inner : Vertex → Gauge) (links : Configuration Edge Gauge) :
    gaugeTransform lattice outer (gaugeTransform lattice inner links) =
      gaugeTransform lattice (fun vertex => outer vertex * inner vertex) links := by
  funext edge
  simp [gaugeTransform, mul_assoc]

theorem plaquetteHolonomy_gauge_covariant (lattice : PlaquetteLattice Vertex Edge Face)
    (gauge : Vertex → Gauge) (links : Configuration Edge Gauge) (face : Face) :
    plaquetteHolonomy lattice (gaugeTransform lattice gauge links) face =
      gauge (lattice.source (lattice.bottom face)) * plaquetteHolonomy lattice links face *
        (gauge (lattice.source (lattice.bottom face)))⁻¹ := by
  simp only [plaquetteHolonomy, gaugeTransform]
  rw [lattice.bottom_right, lattice.right_top, lattice.top_left, lattice.left_bottom]
  group

theorem conjugate_eq_one_iff (base value : Gauge) :
    base * value * base⁻¹ = 1 ↔ value = 1 := by
  constructor
  · intro equal
    have recovered := congrArg (fun element => base⁻¹ * element * base) equal
    simpa [mul_assoc] using recovered
  · rintro rfl
    simp

section Action

variable [DecidableEq Gauge]

def plaquetteCost (lattice : PlaquetteLattice Vertex Edge Face)
    (links : Configuration Edge Gauge) (face : Face) : ℝ :=
  if plaquetteHolonomy lattice links face = 1 then 0 else 1

def plaquetteAction [Fintype Face] (lattice : PlaquetteLattice Vertex Edge Face)
    (links : Configuration Edge Gauge) : ℝ :=
  ∑ face, plaquetteCost lattice links face

theorem plaquetteCost_nonneg (lattice : PlaquetteLattice Vertex Edge Face)
    (links : Configuration Edge Gauge) (face : Face) :
    0 ≤ plaquetteCost lattice links face := by
  unfold plaquetteCost
  split_ifs <;> norm_num

theorem plaquetteCost_gauge_invariant (lattice : PlaquetteLattice Vertex Edge Face)
    (gauge : Vertex → Gauge) (links : Configuration Edge Gauge) (face : Face) :
    plaquetteCost lattice (gaugeTransform lattice gauge links) face =
      plaquetteCost lattice links face := by
  simp only [plaquetteCost, plaquetteHolonomy_gauge_covariant, conjugate_eq_one_iff]

theorem plaquetteAction_nonneg [Fintype Face]
    (lattice : PlaquetteLattice Vertex Edge Face) (links : Configuration Edge Gauge) :
    0 ≤ plaquetteAction lattice links :=
  Finset.sum_nonneg fun face _ => plaquetteCost_nonneg lattice links face

theorem plaquetteAction_gauge_invariant [Fintype Face]
    (lattice : PlaquetteLattice Vertex Edge Face) (gauge : Vertex → Gauge)
    (links : Configuration Edge Gauge) :
    plaquetteAction lattice (gaugeTransform lattice gauge links) = plaquetteAction lattice links := by
  unfold plaquetteAction
  apply Finset.sum_congr rfl
  intro face _
  exact plaquetteCost_gauge_invariant lattice gauge links face

theorem trivial_configuration_action [Fintype Face]
    (lattice : PlaquetteLattice Vertex Edge Face) :
    plaquetteAction lattice (fun _ => (1 : Gauge)) = 0 := by
  simp [plaquetteAction, plaquetteCost, plaquetteHolonomy]

end Action

end InfoGeometry.LatticeGauge
