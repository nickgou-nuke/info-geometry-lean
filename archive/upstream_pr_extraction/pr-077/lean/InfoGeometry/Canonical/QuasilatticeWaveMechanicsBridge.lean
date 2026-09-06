import Mathlib.Tactic
import InfoGeometry.Canonical.FierzKleinFoundation
import InfoGeometry.Canonical.DrazinModularPersistence
import InfoGeometry.Canonical.InformationalLichnerowicz
import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.QuasilatticeDirac
import InfoGeometry.Canonical.Triality

/-!
# InfoGeometry.Canonical.QuasilatticeWaveMechanicsBridge

Theorem-safe compatibility packet for the corridor

`triality -> Bogoliubov vielbein transport -> quasilattice Dirac evolution ->
informational Lichnerowicz readout`.

This file intentionally stays below any exceptional-classification claim.
It packages the existing triadic geometry and the quasilattice transport
theorems as a single wave-mechanics owner surface.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.QuasilatticeWaveMechanicsBridge

open InfoGeometry.Canonical.InformationalLichnerowicz
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.FierzKleinFoundation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Compatibility packet for the quasilattice wave-mechanics corridor.

The packet stores:

* a metric triadic core on the split binary lattice,
* the Bogoliubov vielbein bundle transporting the Dirac operator,
* and a Dirac seed operator living on the doubled carrier.
-/
@[rep_depth transport]
structure QuasilatticeWaveMechanicsBridge where
  /-- The split triadic geometry carried by the corridor. -/
  triadic :
    InfoGeometry.Canonical.Triality.MetricTriadicCore
      (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)

  /-- The Bogoliubov vielbein bundle transporting the quasilattice Dirac operator. -/
  vielbein :
    InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)

  /-- The Dirac seed transported by the vielbein. -/
  diracSeed : EndH

namespace QuasilatticeWaveMechanicsBridge

variable (B : QuasilatticeWaveMechanicsBridge (E := E))

/-- The triadic route norm compatibility is carried by the packet. -/
@[rep_depth transport]
theorem triadic_route_norm_compat_holds (q k : ℝ × ℝ) :
    B.triadic.quadV (B.triadic.route q k) =
      B.triadic.quadQ q + B.triadic.quadK k + 2 * B.triadic.interact q k :=
  B.triadic.route_norm_compat q k

/-- The quasilattice Dirac operator is fixed at zero flow. -/
@[rep_depth transport]
theorem quasilatticeDirac_zero_holds :
    quasilatticeDirac B.vielbein B.diracSeed 0 = B.diracSeed := by
  simpa using
    (QuasilatticeDirac.quasilatticeDirac_zero B.vielbein B.diracSeed)

/-- The infinitesimal quasilattice Dirac transport is the commutator flow. -/
@[rep_depth transport]
theorem quasilatticeDirac_deriv_holds (t : ℝ) :
    deriv (fun s => quasilatticeDirac B.vielbein B.diracSeed s) t
      =
    B.vielbein.connectionGenerator * (quasilatticeDirac B.vielbein B.diracSeed t)
      - (quasilatticeDirac B.vielbein B.diracSeed t) * B.vielbein.connectionGenerator := by
  simpa using
    (QuasilatticeDirac.deriv_quasilatticeDirac B.vielbein B.diracSeed t)

/-- The reference-point Dirac transport is the Maurer-Cartan curvature readout. -/
@[rep_depth transport]
theorem quasilatticeDirac_at_zero_eq_maurerCartanCurvature :
    deriv (fun s => quasilatticeDirac B.vielbein B.diracSeed s) 0
      = B.vielbein.connectionGenerator * B.diracSeed - B.diracSeed * B.vielbein.connectionGenerator := by
  simpa using
    (QuasilatticeDirac.deriv_quasilatticeDirac B.vielbein B.diracSeed 0)

/-- The second Dirac transport derivative is the operatorial Hessian readout. -/
@[rep_depth transport]
theorem quasilatticeDirac_secondDerivative_eq_operatorInformationHessian :
    let X := B.vielbein.connectionGenerator
    deriv (fun t => deriv (fun s => quasilatticeDirac B.vielbein B.diracSeed s) t) 0
      = operatorInformationHessian X B.diracSeed := by
  simpa using
    (InformationalLichnerowicz.deriv2_quasilatticeDirac_at_zero_eq_operatorInformationHessian
      (V := B.vielbein) (D := B.diracSeed))

/-- The second Dirac transport derivative lands in the metric readout. -/
@[rep_depth transport]
theorem quasilatticeDirac_secondDerivative_eq_operatorInformationMetricPart :
    let X := B.vielbein.connectionGenerator
    deriv (fun t => deriv (fun s => quasilatticeDirac B.vielbein B.diracSeed s) t) 0
      = operatorInformationMetricPart X X B.diracSeed := by
  simpa using
    (InformationalLichnerowicz.deriv2_quasilatticeDirac_at_zero_eq_operatorInformationMetricPart
      (V := B.vielbein) (D := B.diracSeed))

/--
Compatibility packet for the wave-quadric lane.

The packet ties the quasilattice wave-mechanics corridor to an explicit
Fierz readout and Drazin horizon.  The Klein-quadric law itself is inherited
from the existing Fierz--Klein foundation.
-/
structure QuasilatticeFierzKleinPacket (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  wave : QuasilatticeWaveMechanicsBridge (E := E)
  readout : FierzReadoutChannels EndH
  horizon : InfoGeometry.Canonical.DrazinModularPersistence.DrazinSupportData EndH
  horizonAdmissible :
    InfoGeometry.Canonical.FierzKleinFoundation.HorizonFierzAdmissible readout horizon

/-- The quasilattice wave packet lands on the Klein quadric via the Fierz readout. -/
theorem dirac_transport_preserves_klein_quadric
    (readout : FierzReadoutChannels EndH)
    (horizon : InfoGeometry.Canonical.DrazinModularPersistence.DrazinSupportData EndH) :
    IsOnKleinQuadric (chiralPlucker (horizonFierzBilinears readout horizon)) := by
  exact chiralPlucker_on_klein (horizonFierzBilinears readout horizon)

/-- The quasilattice wave packet also yields the full Fierz--Klein variety readout. -/
theorem dirac_transport_preserves_fierz_klein_variety
    (readout : FierzReadoutChannels EndH)
    (horizon : InfoGeometry.Canonical.DrazinModularPersistence.DrazinSupportData EndH)
    (horizonAdmissible : HorizonFierzAdmissible readout horizon) :
    IsOnFierzKleinVariety
      (fierzKleinCoordinates
        (horizonFierzBilinears readout horizon)
        horizonAdmissible.normalization) := by
  exact InfoGeometry.Canonical.FierzKleinFoundation.horizon_fierz_klein_holds
    readout horizon horizonAdmissible

end QuasilatticeWaveMechanicsBridge

end InfoGeometry.Canonical.QuasilatticeWaveMechanicsBridge
