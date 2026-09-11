import InfoGeometry.Canonical.ArnoldCohenPluckerBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological readout of the Arnold--Cohen Klein boundary

The algebraic owner supplies the six real Plücker coordinates and the Klein
quadratic polynomial.  This file equips that finite carrier with the induced
product topology, proves continuity of the polynomial readout, and identifies
the on-shell boundary as its closed zero locus.  No analytic `d log` model or
BCFW recursion theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldCohenPluckerBridge

def pluckerCoordinatesEquiv :
    PluckerCoordinates ℝ ≃
      ℝ × ℝ × ℝ × ℝ × ℝ × ℝ where
  toFun p := (p.p12, p.p13, p.p14, p.p23, p.p24, p.p34)
  invFun q :=
    { p12 := q.1
      p13 := q.2.1
      p14 := q.2.2.1
      p23 := q.2.2.2.1
      p24 := q.2.2.2.2.1
      p34 := q.2.2.2.2.2 }
  left_inv := by intro p; rfl
  right_inv := by intro q; rcases q with ⟨p12, p13, p14, p23, p24, p34⟩; rfl

instance pluckerCoordinatesTopologicalSpace :
    TopologicalSpace (PluckerCoordinates ℝ) :=
  TopologicalSpace.induced pluckerCoordinatesEquiv.toFun inferInstance

private theorem continuous_pluckerCoordinatesEquiv :
    Continuous (pluckerCoordinatesEquiv :
      PluckerCoordinates ℝ → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  continuous_induced_dom

theorem continuous_kleinQuadric :
    Continuous (kleinQuadric : PluckerCoordinates ℝ → ℝ) := by
  have hp12 := continuous_pluckerCoordinatesEquiv.fst
  have hp13 := continuous_pluckerCoordinatesEquiv.snd.fst
  have hp14 := continuous_pluckerCoordinatesEquiv.snd.snd.fst
  have hp23 := continuous_pluckerCoordinatesEquiv.snd.snd.snd.fst
  have hp24 := continuous_pluckerCoordinatesEquiv.snd.snd.snd.snd.fst
  have hp34 := continuous_pluckerCoordinatesEquiv.snd.snd.snd.snd.snd
  simpa [kleinQuadric] using
    ((hp12.mul hp34).sub (hp13.mul hp24)).add (hp14.mul hp23)

theorem isClosed_isOnShellBoundary :
    IsClosed {p : PluckerCoordinates ℝ | IsOnShellBoundary p} := by
  change IsClosed (kleinQuadric ⁻¹' ({0} : Set ℝ))
  exact isClosed_singleton.preimage continuous_kleinQuadric

noncomputable def kleinQuadricContinuousMap :
    C(PluckerCoordinates ℝ, ℝ) :=
  ⟨kleinQuadric, continuous_kleinQuadric⟩

noncomputable def kleinQuadricTopCat :
    TopCat.of (PluckerCoordinates ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom kleinQuadricContinuousMap

@[simp] theorem kleinQuadricContinuousMap_apply
    (p : PluckerCoordinates ℝ) :
    kleinQuadricContinuousMap p = kleinQuadric p :=
  rfl

end InfoGeometry.Canonical.ArnoldCohenPluckerBridge
