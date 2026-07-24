import InfoGeometry.Convex.Legendre
import InfoGeometry.Potential.LogPotential
import InfoGeometry.Thermo.FromBregman
import InfoGeometry.Thermo.SusceptibilityHessian
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Canonical.AmariSouriauThermodynamicGauge

/-!
# Amari--Souriau Thermodynamic Bridge

Thin Lean-facing facade for the information-geometry / Souriau thermodynamics
dictionary.

This file does not attempt to derive convexity, Fisher positivity, or the
Killing equation from first principles.  It packages the repository-owned
Legendre/Bregman and thermodynamic-gauge data so downstream callers can use a
single interface for:

* log-partition potentials;
* Bregman/KL readouts;
* the thermodynamic force `d_ln_Q`; and
* the equilibrium Killing-field socket already owned by the canonical bridge.
-/

namespace InfoGeometry.Thermo.AmariSouriauBridge

open InfoGeometry.Convex
open InfoGeometry.Convex.LegendrePotential
open InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
open InfoGeometry.Topology.ThermodynamicGauge

/--
Scalar Amari/Souriau bridge packet.

`legendre` carries the dually flat potential, `logPotential` gives the
root-level log-potential shadow, and `gauge` carries the thermodynamic
`d log Q` force together with the equilibrium Killing-field socket.
-/
structure Bridge
    (Op X : Type*) [Ring Op] where
  /-- Scalar Legendre potential used for the information-geometry side. -/
  legendre : LegendrePotential

  /-- Root-level log-potential shadow of the same scalar potential. -/
  logPotential : InfoGeometry.LogPotential ℝ

  /-- The log-potential shadow is the same scalar function as `legendre.f`. -/
  logPotential_eq : logPotential.ψ = legendre.f

  /-- Thermodynamic gauge / Souriau socket. -/
  gauge : SouriauAmariGauge Op ℝ ℝ X

  /-- The gauge-side log-partition potential is the same scalar potential. -/
  infoPotential_eq : gauge.info.Ψ = legendre.f

  /-- The gauge-side dual coordinate is the derivative coordinate of the potential. -/
  infoGradient_eq : gauge.info.gradΨ = eta legendre

namespace Bridge

variable {Op X : Type*} [Ring Op]
variable (B : Bridge Op X)

/-- The thermodynamic force readout is the repository-owned `d_ln_Q`. -/
def thermodynamicForce : Op :=
  B.gauge.flow.d_ln_Q

@[simp] theorem thermodynamicForce_eq_dlogQ :
    B.thermodynamicForce = B.gauge.flow.d_ln_Q := rfl

/-- The root-level and Legendre Bregman readouts coincide. -/
theorem logPotential_bregman_eq_legendre_bregman (θ θ' : ℝ) :
    B.logPotential.bregman θ' θ = B.legendre.bregman θ' θ := by
  simp [InfoGeometry.LogPotential.bregman, B.logPotential_eq]

/-- The gauge-side dual coordinate is the Legendre expectation coordinate. -/
theorem dualCoord_eq_eta (θ : ℝ) :
    B.gauge.info.dualCoord θ = eta B.legendre θ := by
  have h := congrArg (fun f => f θ) B.infoGradient_eq
  simpa [DuallyFlatLogPartition.dualCoord, eta] using h

/-- The thermodynamic force commutator is the de Rham current when supplied. -/
theorem entropy_production_eq_dlogQ
    (hcomm :
      B.gauge.flow.P_forward * B.gauge.flow.P_backward -
        B.gauge.flow.P_backward * B.gauge.flow.P_forward =
        B.gauge.flow.d_ln_Q) :
    entropy_production B.gauge.flow = B.thermodynamicForce := by
  simpa [thermodynamicForce] using
    B.gauge.entropy_production_eq_dlogQ hcomm

/-- At detailed balance, the generated `d log Q` vector is Killing. -/
theorem generated_field_killing_of_equilibrium
    (heq : entropy_production B.gauge.flow = 0) :
    B.gauge.lieMetric B.gauge.generatedVectorField = 0 :=
  B.gauge.generated_field_killing_of_equilibrium heq

/-- The parameter-space KL readout is the Bregman gap of the Legendre potential. -/
theorem KL_param_eq_bregman (θ θ' : ℝ) :
    InfoGeometry.ConvexDuality.KL_param B.legendre.f θ θ' =
      B.legendre.bregman θ' θ :=
  InfoGeometry.Thermo.KL_param_eq_bregman_energy (L := B.legendre) θ θ'

/-- The Legendre Fisher scalar is nonnegative. -/
theorem fisher_nonneg (θ : ℝ) :
    0 ≤ B.legendre.fisher θ :=
  B.legendre.fisher_nonneg θ

end Bridge

end InfoGeometry.Thermo.AmariSouriauBridge
