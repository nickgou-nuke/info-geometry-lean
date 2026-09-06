import InfoGeometry.Topology.MappingTorusGluing
import InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation

/-!
# Split-octonion mirror/rail mapping-torus datum

This is the concrete specialization of the quotient-level gluing owner to
the native quaternion-coordinate Zorn carrier.  The source owner proves that
the mirror/rail map is involutive and norm-preserving.  No claim about
nonorientability or anomaly cancellation is made here.
-/

namespace InfoGeometry.Topology.SplitOctonionMirrorRailMappingTorus

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation
open InfoGeometry.Topology.MappingTorusGluing

abbrev Carrier := CartesianCoordinates

noncomputable def mirrorRailGluing : InvolutiveGluing (F := Carrier) where
  map := mirrorRailSwapJK
  involutive := by
    intro x
    exact mirrorRailSwapJK_involutive x

abbrev Torus := InvolutiveGluing.torus mirrorRailGluing

theorem endpoint (x : Carrier) :
    mappingTorusMk mirrorRailGluing.map (0, x) =
      mappingTorusMk mirrorRailGluing.map (1, mirrorRailGluing.map x) :=
  InvolutiveGluing.endpoint mirrorRailGluing x

theorem gluing_is_order_two (x : Carrier) :
    mirrorRailGluing.map (mirrorRailGluing.map x) = x :=
  InvolutiveGluing.map_map mirrorRailGluing x

end InfoGeometry.Topology.SplitOctonionMirrorRailMappingTorus
