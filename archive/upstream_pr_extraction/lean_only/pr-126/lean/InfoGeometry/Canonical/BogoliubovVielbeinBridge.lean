import InfoGeometry.Canonical.BogoliubovVielbein
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Quantum.Fock
import InfoGeometry.Quantum.RealMajorana

/-!
# Bogoliubov Vielbein Bridge

Thin compatibility bridge over the existing Bogoliubov vielbein, Fock, and
real Majorana surfaces.

The repository already has the naive ingredients:
- `BogoliubovVielbeinBundle` for the transport frame,
- `RealMajoranaDatum` and `KPolarization` for the real operator split,
- `Quantum.Fock` for creation/annihilation projectors,
- `BogoliubovFockSuper` for the graded operator vocabulary.

This file only packages those pieces into one bridge surface.
-/

noncomputable section

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.BogoliubovVielbeinBridge

open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Quantum
open InfoGeometry.Krein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Bogoliubov vielbein bridge.

This combines the transport frame with the basic operator split used by the
Fock surface. It does not introduce a new algebraic model.
-/
structure BogoliubovVielbeinBridge where
  frame : BogoliubovVielbeinBundle (E := E)
  superParity : SuperParity

namespace BogoliubovVielbeinBridge

/-- The local frame transported by the bridge. -/
def localFrame
    (B : BogoliubovVielbeinBridge (E := E)) (t : ℝ) : EndH :=
  B.frame.localFrame t

/-- The base Maurer-Cartan curvature readout. -/
def curvature
    (B : BogoliubovVielbeinBridge (E := E)) : EndH :=
  B.frame.maurerCartanCurvature

/-- The phase-linear charge extracted from the vielbein connection. -/
def phaseLinearCharge
    (B : BogoliubovVielbeinBridge (E := E)) : EndH :=
  BogoliubovTransport.phaseLinearPart (E := E) B.frame.connectionGenerator

/-- The phase-antilinear charge extracted from the vielbein connection. -/
def phaseAntilinearCharge
    (B : BogoliubovVielbeinBridge (E := E)) : EndH :=
  BogoliubovTransport.phaseAntilinearPart (E := E) B.frame.connectionGenerator

/-- The phase charge split recomposes the connection generator. -/
theorem phaseCharge_decomposition
    (B : BogoliubovVielbeinBridge (E := E)) :
    B.phaseLinearCharge + B.phaseAntilinearCharge = B.frame.connectionGenerator := by
  simp [phaseLinearCharge, phaseAntilinearCharge]

/-- The bridge creation channel. -/
def creationChannel (_ : BogoliubovVielbeinBridge (E := E)) : EndH :=
  creationOp (E := E)

/-- The bridge annihilation channel. -/
def annihilationChannel (_ : BogoliubovVielbeinBridge (E := E)) : EndH :=
  annihilationOp (E := E)

/-- The bridge vacuum vector. -/
def vacuumVector (_ : BogoliubovVielbeinBridge (E := E)) : H₂ :=
  0

/-- Creation and annihilation recombine to the identity on the doubled carrier. -/
theorem creation_add_annihilation_eq_id
    (B : BogoliubovVielbeinBridge (E := E)) :
    B.creationChannel + B.annihilationChannel
      = ContinuousLinearMap.id ℝ H₂ :=
  creation_add_annihilation (E := E)

/-- The annihilation channel kills the bridge vacuum. -/
theorem annihilation_kills_vacuum
    (B : BogoliubovVielbeinBridge (E := E)) :
    B.annihilationChannel B.vacuumVector = 0 :=
  annihilation_kills_vacuum_vector (E := E)

/--
Canonical bridge package.

This keeps the bridge explicit while reusing the existing transport frame.
-/
def canonical
    (V : BogoliubovVielbeinBundle (E := E)) :
    BogoliubovVielbeinBridge (E := E) where
  frame := V
  superParity := SuperParity.even

end BogoliubovVielbeinBridge

end InfoGeometry.Canonical.BogoliubovVielbeinBridge
