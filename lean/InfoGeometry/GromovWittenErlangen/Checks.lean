import InfoGeometry.GromovWittenErlangen.LieOrbitCurve
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.GromovWittenErlangen.Checks

/-- Smoke checks for the Lie-orbit curve synthesis surface. -/
abbrev LieOrbitCurveWitnessType (G T Target : Type*) :=
  @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness (G := G) (T := T) (Target := Target)

abbrev LocalizationGraphWitnessType (G T Target : Type*) :=
  @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness (G := G) (T := T) (Target := Target)

abbrev LanglandsDualOrbitCurveWitnessType
    (G T Target : Type*)
    (C : InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness (G := G) (T := T)
      (Target := Target)) :=
  @InfoGeometry.GromovWittenErlangen.LanglandsDualOrbitCurveWitness (C := C)

abbrev VirtualLocalizationOrbitPacketType (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.VirtualLocalizationOrbitPacket (G := G) (T := T)
    (Target := Target) (Coeff := Coeff)

abbrev KleinGromovPacketType (G T Target : Type*) :=
  @InfoGeometry.GromovWittenErlangen.KleinGromovPacket (G := G) (T := T) (Target := Target)

abbrev constructKleinGromovPacketRef
    (G T Target Coeff : Type*) :=
  @InfoGeometry.GromovWittenErlangen.constructKleinGromovPacket (G := G) (T := T)
    (Target := Target) (Coeff := Coeff)

end InfoGeometry.GromovWittenErlangen.Checks
