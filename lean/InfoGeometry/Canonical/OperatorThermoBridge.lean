import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge

/-!
# Retired scalar operator-thermodynamics facade

The former declarations exposed `EndH →L[ℝ] ℝ` scalar readouts for Massieu,
free energy, and entropy production.  They did not define a noncommutative
state, modular flow, or positive functional and had no maintained consumers.

The operator-first thermodynamics owner is
`Canonical.OperatorThermodynamics.OperatorFirstThermodynamicsPacket`; modular
negative-log data and positive-functional Fisher/BKM data remain in the native
owners imported above.  This compatibility module exports no scalar shadow
API.
-/
