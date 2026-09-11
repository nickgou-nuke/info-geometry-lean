import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Carrier Transport

This module defines the minimal flow requirements for the involutive self-dual
carrier.

Scope discipline:
- flow law (`transport_zero`, `transport_add`),
- pairing preservation.

No commutation assumptions with `J`, `ε`, or `K` are included here.
-/

namespace InfoGeometry.Krein

/-- Minimal transport flow on an involutive self-dual carrier. -/
structure CarrierTransport (X : InvolutiveSelfDualCarrier) where
  transport : ℝ → (X.H →L[ℝ] X.H)

  transport_zero :
    transport 0 = ContinuousLinearMap.id ℝ X.H
  transport_add :
    ∀ s t, transport (s + t) = (transport s).comp (transport t)

  transport_preserves_pairing :
    ∀ t u v,
      X.kreinPairing (transport t u) (transport t v) = X.kreinPairing u v

end InfoGeometry.Krein
