import InfoGeometry.Krein.CarrierTransport

/-!
# Carrier With Generator

This module defines the operatorial generators attached to the carrier 
and its transport flow.
-/

namespace InfoGeometry.Krein

/-- A carrier equipped with a static operatorial generator. -/
structure CarrierWithGenerator (X : InvolutiveSelfDualCarrier) where
  generator : X.H →L[ℝ] X.H

/-- A transport flow equipped with its infinitesimal generator. -/
structure CarrierTransportWithGenerator
    (X : InvolutiveSelfDualCarrier)
    (T : CarrierTransport X) where
  infinitesimalGenerator : X.H →L[ℝ] X.H
  -- Later: hasDerivAt_transport_zero_eq_generator ...

namespace CarrierWithGenerator

variable {X : InvolutiveSelfDualCarrier} (G : CarrierWithGenerator X)

/-- The generator is 'odd' (Fermionic) relative to the J-grading. -/
def IsOdd : Prop := X.J.comp G.generator = -(G.generator.comp X.J)

/-- The generator is 'even' (Bosonic) relative to the J-grading. -/
def IsEven : Prop := X.J.comp G.generator = G.generator.comp X.J

end CarrierWithGenerator

end InfoGeometry.Krein
