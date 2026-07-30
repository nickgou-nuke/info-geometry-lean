import InfoGeometry.Krein.CarrierTransport

/-!
# Carrier With Generator

This module defines the operatorial generators attached to the carrier 
and its transport flow.
-/

namespace InfoGeometry.Krein

/-- A carrier equipped with a static operatorial generator. -/
abbrev CarrierWithGenerator (X : InvolutiveSelfDualCarrier) :=
  X.H →L[ℝ] X.H

namespace CarrierWithGenerator

abbrev generator (G : CarrierWithGenerator X) : X.H →L[ℝ] X.H := G

def mk (generator : X.H →L[ℝ] X.H) : CarrierWithGenerator X :=
  generator

end CarrierWithGenerator

/-- A transport flow equipped with its infinitesimal generator. -/
abbrev CarrierTransportWithGenerator
    (X : InvolutiveSelfDualCarrier)
    (T : CarrierTransport X) :=
  X.H →L[ℝ] X.H

namespace CarrierTransportWithGenerator

abbrev infinitesimalGenerator
    (G : CarrierTransportWithGenerator X T) : X.H →L[ℝ] X.H := G

def mk (infinitesimalGenerator : X.H →L[ℝ] X.H) :
    CarrierTransportWithGenerator X T :=
  infinitesimalGenerator

end CarrierTransportWithGenerator

namespace CarrierWithGenerator

variable {X : InvolutiveSelfDualCarrier} (G : CarrierWithGenerator X)

/-- The generator is 'odd' (Fermionic) relative to the J-grading. -/
def IsOdd : Prop := X.J.comp G.generator = -(G.generator.comp X.J)

/-- The generator is 'even' (Bosonic) relative to the J-grading. -/
def IsEven : Prop := X.J.comp G.generator = G.generator.comp X.J

end CarrierWithGenerator

end InfoGeometry.Krein
