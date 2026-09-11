import InfoGeometry.Topology.ThreeColorSL3ZornActionTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Three-color `SL₃` Zorn action topological bridge

Canonical re-export of the verified topological `SL₃`-action on the
three-colour Zorn carrier.  This bridge adds no new topology or continuity
claims; it only forwards the already-proved Topology owner.
-/

namespace InfoGeometry.Canonical.ThreeColorSL3ZornActionTopologicalBridge

open InfoGeometry.Topology.ThreeColorSL3ZornActionTopological

abbrev Zorn := InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn

abbrev ZornCoords := InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.ZornCoords

def zornCoordEquiv :
    Zorn ≃ ZornCoords :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.zornCoordEquiv

instance zornTopologicalSpace : TopologicalSpace Zorn :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.zornTopologicalSpace

def zornCoordHomeomorph : Zorn ≃ₜ ZornCoords :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.zornCoordHomeomorph

theorem zornCoordHomeomorph_apply (X : Zorn) :
    zornCoordHomeomorph X = zornCoordEquiv X :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.zornCoordHomeomorph_apply X

theorem continuous_zorn_a :
    Continuous (fun X : Zorn => X.a) :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.continuous_zorn_a

theorem continuous_zorn_u :
    Continuous (fun X : Zorn => X.u) :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.continuous_zorn_u

theorem continuous_zorn_v :
    Continuous (fun X : Zorn => X.v) :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.continuous_zorn_v

theorem continuous_zorn_b :
    Continuous (fun X : Zorn => X.b) :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.continuous_zorn_b

theorem continuous_zornSL3Action
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Continuous (InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action g) :=
  InfoGeometry.Topology.ThreeColorSL3ZornActionTopological.continuous_zornSL3Action g

end InfoGeometry.Canonical.ThreeColorSL3ZornActionTopologicalBridge
