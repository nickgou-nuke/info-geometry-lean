import InfoGeometry.Canonical.KleinFourTagRootNormalization
import InfoGeometry.Canonical.SplitOctonionKleinFourTagRepresentation
import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation

/-!
# Canonical Klein-four representations

This is a narrow bridge over the existing additive Klein-four owner, the
split-octonion axis automorphism owner, and the local `Cl(1,1)` adjoint owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinFourRealizations

abbrev V4Add := InfoGeometry.Geometry.KleinFourTag.Tag
abbrev V4 := InfoGeometry.Canonical.KleinFourTagRootNormalization.V4
abbrev AxisCarrier :=
  InfoGeometry.Canonical.SplitOctonionKleinFourTagRepresentation.AxisCarrier
local instance : Mul AxisCarrier :=
  InfoGeometry.Canonical.SplitOctonionKleinFourAutomorphism.instMulSplitOct
abbrev AxisAut := AxisCarrier ≃* AxisCarrier
abbrev LocalCarrier :=
  InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation.Mat2
abbrev LocalAut := LocalCarrier ≃ₐ[ℝ] LocalCarrier

def axisRepresentation : V4 →* AxisAut :=
  InfoGeometry.Canonical.SplitOctonionKleinFourTagRepresentation.axisActionHom

@[simp] theorem axisRepresentation_apply (g : V4) (x : AxisCarrier) :
    axisRepresentation g x =
      InfoGeometry.Canonical.SplitOctonionKleinFourTagRepresentation.axisActionHom g x :=
  rfl

noncomputable def localRepresentation : V4 →* LocalAut :=
  InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation.localCl11Map

@[simp] theorem localRepresentation_apply (g : V4) (x : LocalCarrier) :
    localRepresentation g x =
      InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation.localCl11Map g x :=
  rfl

noncomputable def common_source_equiv :
    V4 ≃* InfoGeometry.Topology.V4RootSystem.V4Group :=
  InfoGeometry.Canonical.KleinFourTagRootNormalization.v4RootEquiv

end InfoGeometry.Canonical.KleinFourRealizations
