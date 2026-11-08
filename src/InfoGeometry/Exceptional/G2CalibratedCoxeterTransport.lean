import InfoGeometry.Exceptional.G2CyclotomicCoxeterLift
import InfoGeometry.Exceptional.G2CyclotomicCoordinateActionBridge

/-!
# Equivariant transport of the calibrated Coxeter action

Contract: transport the sector-dependent cyclotomic Coxeter lift through the
existing signed-root equivalence. The resulting group action has the actual
coordinate simple reflections and is equivariant on every group element.
The old single-axis dihedral action is not identified with this action.
-/
namespace InfoGeometry.Exceptional.G2CalibratedCoxeterTransport

open InfoGeometry.Exceptional.G2CyclotomicCoxeterLift
open InfoGeometry.Exceptional.G2CyclotomicCoordinateActionBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

noncomputable def calibratedCoordinateAction :
    g2CoxeterMatrix.Group →* Equiv.Perm G2CoordinateRoot :=
  transportRootPermHom.comp cyclotomicCoxeterLift

theorem calibratedCoordinateAction_equivariant
    (g : g2CoxeterMatrix.Group) (x : G2CoordinateRoot) :
    signedRootCyclotomicEquiv (calibratedCoordinateAction g x) =
      cyclotomicCoxeterLift g (signedRootCyclotomicEquiv x) := by
  simp [calibratedCoordinateAction, transportRootPermHom,
    transportRootPerm, Equiv.trans_apply]

theorem calibratedCoordinateAction_simple_zero :
    calibratedCoordinateAction (g2CoxeterMatrix.simple 0) = s1Root := by
  change transportRootPerm (cyclotomicCoxeterLift (g2CoxeterMatrix.simple 0)) = _
  rw [cyclotomicCoxeterLift_apply_simple]
  exact transportRootPerm_cyclotomicS1

theorem calibratedCoordinateAction_simple_one :
    calibratedCoordinateAction (g2CoxeterMatrix.simple 1) = s2Root := by
  change transportRootPerm (cyclotomicCoxeterLift (g2CoxeterMatrix.simple 1)) = _
  rw [cyclotomicCoxeterLift_apply_simple]
  exact transportRootPerm_cyclotomicS2

end InfoGeometry.Exceptional.G2CalibratedCoxeterTransport
