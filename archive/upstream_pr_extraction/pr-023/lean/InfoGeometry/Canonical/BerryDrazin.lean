import Mathlib
import InfoGeometry.Canonical.VarlamovClifford
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.BerryDrazin

Berry connection and curvature on a Drazin horizon.

This module builds on the theorem-safe idempotent differential law from
`VarlamovClifford`:

`p * d p * p = 0`.

It defines the Berry connection `p_A * d p_A`, a curvature readout
`p_A * d p_A * d p_A * p_A`, and a witness-gated thermodynamic entropy packet
for Hodge-Drazin Laplacian geometry.  It does not assert analytic trace, log,
exponential, or Chern integration theorems without supplied witnesses.
-/

noncomputable section

namespace InfoGeometry.Canonical.BerryDrazin

open InfoGeometry.Canonical.VarlamovClifford

/--
Lean-safe Drazin Berry carrier.

`p_A` is the Drazin horizon projector and `H_L` is the harmonic/generalized-zero
projector.  The `J/JD` commutation laws are available for downstream Varlamov
covariance, but the Berry projector law only needs idempotence of `p_A`.
-/
@[rep_depth operator]
structure LeanSafeCarrier
    (Op : Type*) [Ring Op] where
  p_A : Op
  H_L : Op
  J : Op
  JD : Op

  p_A_idempotent : p_A * p_A = p_A
  H_L_idempotent : H_L * H_L = H_L

  J_comm_pA : J * p_A = p_A * J
  JD_comm_pA : JD * p_A = p_A * JD
  J_comm_HL : J * H_L = H_L * J
  JD_comm_HL : JD * H_L = H_L * JD
  J_JD_comm : J * JD = JD * J

/-- Exterior derivative on an operator ring. -/
abbrev ExteriorDerivative
    (Op : Type*) [Ring Op] :=
  InfoGeometry.Canonical.VarlamovClifford.ExteriorDerivative Op

namespace LeanSafeCarrier

variable {Op : Type*} [Ring Op]
variable (C : LeanSafeCarrier Op)
variable (D : ExteriorDerivative Op)

/-- Differential off-diagonality of the Drazin horizon projector. -/
@[rep_depth operator]
theorem d_pA_off_diagonal :
    C.p_A * D.d C.p_A * C.p_A = 0 :=
  D.idempotent_d_off_diagonal C.p_A_idempotent

/-- Differential off-diagonality of the harmonic/generalized-zero projector. -/
@[rep_depth operator]
theorem d_HL_off_diagonal :
    C.H_L * D.d C.H_L * C.H_L = 0 :=
  D.idempotent_d_off_diagonal C.H_L_idempotent

/-- Berry connection one-form on the Drazin horizon: `Ω_B = p_A * d p_A`. -/
@[rep_depth operator]
def berryConnection : Op :=
  C.p_A * D.d C.p_A

/-- Berry curvature readout on the Drazin horizon: `F_B = p_A * d p_A * d p_A * p_A`. -/
@[rep_depth operator]
def berryCurvature : Op :=
  C.p_A * D.d C.p_A * D.d C.p_A * C.p_A

/-- The Berry connection has no right-supported horizon component. -/
@[rep_depth operator]
theorem berryConnection_mul_pA_eq_zero :
    C.berryConnection D * C.p_A = 0 := by
  unfold berryConnection
  simpa [mul_assoc] using C.d_pA_off_diagonal D

/-- The adjoint-side Berry connection `d p_A * p_A` has no left-supported component. -/
@[rep_depth operator]
theorem pA_mul_rightBerryConnection_eq_zero :
    C.p_A * (D.d C.p_A * C.p_A) = 0 := by
  simpa [mul_assoc] using C.d_pA_off_diagonal D

/-- Harmonic Berry connection one-form: `H_L * d H_L`. -/
@[rep_depth operator]
def harmonicBerryConnection : Op :=
  C.H_L * D.d C.H_L

/-- Harmonic Berry curvature readout: `H_L * d H_L * d H_L * H_L`. -/
@[rep_depth operator]
def harmonicBerryCurvature : Op :=
  C.H_L * D.d C.H_L * D.d C.H_L * C.H_L

/-- The harmonic Berry connection has no right-supported harmonic component. -/
@[rep_depth operator]
theorem harmonicBerryConnection_mul_HL_eq_zero :
    C.harmonicBerryConnection D * C.H_L = 0 := by
  unfold harmonicBerryConnection
  simpa [mul_assoc] using C.d_HL_off_diagonal D

end LeanSafeCarrier

/--
Witness-gated Chern readout for a Drazin Berry curvature.

Integration, trace, normalization constants, and cohomology classes are analytic
or geometric model data, so they are explicit fields.
-/
@[rep_depth operator]
structure DrazinBerryChernPacket
    (Op : Type*) [Ring Op] where
  carrier : LeanSafeCarrier Op
  derivative : ExteriorDerivative Op
  chernReadout : Op → ℝ
  chernValue : ℝ
  chern_law : chernReadout (carrier.berryCurvature derivative) = chernValue

namespace DrazinBerryChernPacket

variable {Op : Type*} [Ring Op]
variable (P : DrazinBerryChernPacket Op)

/-- Re-export of the supplied Chern readout law. -/
@[rep_depth operator]
theorem chern_readout_eq_value :
    P.chernReadout (P.carrier.berryCurvature P.derivative) = P.chernValue :=
  P.chern_law

end DrazinBerryChernPacket

/--
Witness-gated Hodge-Drazin thermodynamic entropy packet.

This records the intended regular-sector density and entropy readouts without
claiming the existence of trace, exponential, logarithm, or positivity theory in
an arbitrary operator ring.
-/
@[rep_depth operator]
structure HodgeDrazinThermodynamicEntropyPacket
    (Op : Type*) [Ring Op] where
  carrier : LeanSafeCarrier Op
  beta : ℝ
  density : Op
  partitionFunction : ℝ
  entropy : ℝ
  horizonEntropy : ℝ
  harmonicEntropy : ℝ

  density_regularSector_law : Prop
  entropy_vonNeumann_law : Prop
  entropy_split_law : entropy = horizonEntropy + harmonicEntropy

namespace HodgeDrazinThermodynamicEntropyPacket

variable {Op : Type*} [Ring Op]
variable (P : HodgeDrazinThermodynamicEntropyPacket Op)

/-- Re-export of the supplied entropy split law. -/
@[rep_depth operator]
theorem entropy_eq_horizon_add_harmonic :
    P.entropy = P.horizonEntropy + P.harmonicEntropy :=
  P.entropy_split_law

/-- The regular-sector density law is available as a model-supplied proposition. -/
@[rep_depth operator]
def density_regularSector_statement : Prop :=
  P.density_regularSector_law

/-- The von Neumann entropy law is available as a model-supplied proposition. -/
@[rep_depth operator]
def entropy_vonNeumann_statement : Prop :=
  P.entropy_vonNeumann_law

end HodgeDrazinThermodynamicEntropyPacket

end InfoGeometry.Canonical.BerryDrazin
