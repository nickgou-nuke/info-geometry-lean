import InfoGeometry.Canonical.ChiralConeSpinFrameBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Topology of the real chiral-cone transport

This owner records only the topology available for the scalar real model:
the hyperbolic transport is continuous in its parameter, and the involutive
domain `u^2 = 1` is closed.  No bundle connection or physical spin
connection is inferred from the scalar formula.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

noncomputable section

def realSpinConnectionTransport (u theta : ℝ) : ℝ :=
  spinConnectionTransport u theta 0

theorem continuous_realSpinConnectionTransport (u : ℝ) :
    Continuous (realSpinConnectionTransport u) := by
  unfold realSpinConnectionTransport spinConnectionTransport
  fun_prop

def realHyperbolicTransportDomain : Set ℝ :=
  {u | u * u = 1}

theorem isClosed_realHyperbolicTransportDomain :
    IsClosed realHyperbolicTransportDomain := by
  change IsClosed ((fun u : ℝ => u * u) ⁻¹' ({1} : Set ℝ))
  exact isClosed_singleton.preimage (continuous_id.mul continuous_id)

theorem realSpinConnectionTransport_continuous_on_domain (u : ℝ)
    (hu : u ∈ realHyperbolicTransportDomain) :
    Continuous (realSpinConnectionTransport u) :=
  continuous_realSpinConnectionTransport u

end

end InfoGeometry.Topology
