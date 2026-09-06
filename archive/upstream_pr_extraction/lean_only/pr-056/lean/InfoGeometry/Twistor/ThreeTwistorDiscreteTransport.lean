import Mathlib

/-!
# Finite transport on a three-vertex twistor triangle

This file records only finite algebraic transport.  It does not identify the
transport with a manifold connection or claim a curvature theorem.
-/

namespace InfoGeometry.Twistor

universe u

/-- Edge transport on the three vertices of a reconstructed twistor triangle. -/
structure TriangleTransportDatum (G : Type u) [Group G] where
  edge : Fin 3 → Fin 3 → G

namespace TriangleTransportDatum

variable {G : Type u} [Group G]

/-- Oriented transport around `0 → 1 → 2 → 0`. -/
def holonomy (T : TriangleTransportDatum G) : G :=
  T.edge 0 1 * T.edge 1 2 * T.edge 2 0

/-- The algebraic failure of the triangle transport to close. -/
def closureDefect (T : TriangleTransportDatum G) : G :=
  T.holonomy

theorem closureDefect_eq_one_iff (T : TriangleTransportDatum G) :
    T.closureDefect = 1 ↔ T.holonomy = 1 := Iff.rfl

/-- A reverse-edge law for a transport datum. -/
def HasReverseEdges (T : TriangleTransportDatum G) : Prop :=
  ∀ i j, T.edge i j * T.edge j i = 1

theorem reverse_edge_cancel (T : TriangleTransportDatum G)
    (h : T.HasReverseEdges) (i j : Fin 3) :
    T.edge j i = (T.edge i j)⁻¹ := by
  have h' := congrArg (fun z => (T.edge i j)⁻¹ * z) (h i j)
  simpa [mul_assoc] using h'

/-- Gauge transformation by a group element at each triangle vertex. -/
def gaugeTransform (T : TriangleTransportDatum G) (g : Fin 3 → G) :
    TriangleTransportDatum G where
  edge i j := (g i)⁻¹ * T.edge i j * g j

theorem holonomy_gaugeTransform (T : TriangleTransportDatum G)
    (g : Fin 3 → G) :
    (T.gaugeTransform g).holonomy =
      (g 0)⁻¹ * T.holonomy * g 0 := by
  simp only [holonomy, gaugeTransform]
  rw [show (g 0)⁻¹ * T.edge 0 1 * g 1 *
        ((g 1)⁻¹ * T.edge 1 2 * g 2) *
        ((g 2)⁻¹ * T.edge 2 0 * g 0) =
      (g 0)⁻¹ * (T.edge 0 1 * T.edge 1 2 * T.edge 2 0) * g 0 by
      group]

theorem closureDefect_gaugeTransform (T : TriangleTransportDatum G)
    (g : Fin 3 → G) :
    (T.gaugeTransform g).closureDefect =
      (g 0)⁻¹ * T.holonomy * g 0 := by
  rw [closureDefect, holonomy_gaugeTransform]

theorem holonomy_eq_one_of_cocycle (T : TriangleTransportDatum G)
    (h₀₁₂ : T.edge 0 1 * T.edge 1 2 = T.edge 0 2)
    (h₀₂₀ : T.edge 0 2 * T.edge 2 0 = 1) :
    T.holonomy = 1 := by
  calc
    T.holonomy = (T.edge 0 1 * T.edge 1 2) * T.edge 2 0 := rfl
    _ = T.edge 0 2 * T.edge 2 0 := by rw [h₀₁₂]
    _ = 1 := h₀₂₀

end TriangleTransportDatum

end InfoGeometry.Twistor
