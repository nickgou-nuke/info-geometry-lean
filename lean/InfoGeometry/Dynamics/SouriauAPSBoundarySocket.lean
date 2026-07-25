import Mathlib.Tactic
import InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions
import InfoGeometry.Dynamics.SouriauDiracHodge

/-!
# Souriau APS Boundary Socket

This file packages the smallest theorem-safe boundary layer matching the
Atiyah-Patodi-Singer style cylindrical-end picture used in the repository:

* the thermal Cayley coordinate reaches the boundary point `1`,
* the twisted Dirac-Hodge index vanishes in the real Krein lane,
* the zero-temperature anomaly norm decays to `0`,
* and an explicit boundary correction `η` is required to vanish.

This is a socket, not a proof of the full APS index theorem.
The boundary correction hypothesis is carried explicitly and then discharged by
the theorem below.
-/

noncomputable section

namespace InfoGeometry.Dynamics.SouriauAPSBoundarySocket

open Filter

open InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions
open InfoGeometry.Dynamics.SouriauDiracHodge

universe u

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [InfoGeometry.Krein.KreinSpace H]

/--
APS-style cylindrical-end socket data.

The only nontrivial new datum is the boundary correction `η`; the rest is the
already-owned real Krein Dirac-Hodge input package.
-/
structure APSBoundarySocket where
  /-- Real Krein Dirac-Hodge carrier. -/
  D : KreinOperatorData H
  /-- Trace functional on endomorphisms. -/
  trace : (H →L[ℝ] H) → ℝ
  /-- Linearity of the trace on scalar multiples. -/
  h_trace_linear : ∀ (c : ℝ) (A : H →L[ℝ] H), trace (c • A) = c * trace A
  /-- `J`-invariance of the trace. -/
  h_trace_J_inv : ∀ A, trace (D.J * A * D.J) = trace A
  /-- Projector commutes with the modular involution. -/
  h_proj_J_comm : D.twistedSectorProjection * D.J = D.J * D.twistedSectorProjection
  /-- The APS boundary correction term. -/
  etaInvariant : ℝ
  /-- Cylindrical-end / APS correction vanishes. -/
  eta_vanishes : etaInvariant = 0
  /-- Boundary correction identifies the index pairing with `η`. -/
  boundary_correction : D.indexPairing trace = etaInvariant

namespace APSBoundarySocket

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [InfoGeometry.Krein.KreinSpace H]
variable (A : APSBoundarySocket H)

/--
The APS boundary correction collapses the index pairing to zero.
-/
theorem boundary_index_vanishes :
    A.D.indexPairing A.trace = 0 := by
  rw [A.boundary_correction, A.eta_vanishes]

/--
The full cylindrical-end package:
thermal Cayley boundary contraction, zero-temperature anomaly decay, and
APS boundary correction vanishing.
-/
theorem cylindrical_end_aps_package :
    Tendsto thermalCayley atTop (nhds (1 : ℝ)) ∧
      Tendsto
        (fun beta : ℝ => ‖A.D.thermalDensityMatrix beta * A.D.chiralChargeOperator‖)
        atTop (nhds 0) ∧
      A.D.indexPairing A.trace = 0 := by
  constructor
  · exact thermalCayley_tendsto_one
  · constructor
    · exact A.D.zero_temperature_anomaly_cancellation
    · exact A.boundary_index_vanishes

end APSBoundarySocket

end InfoGeometry.Dynamics.SouriauAPSBoundarySocket
