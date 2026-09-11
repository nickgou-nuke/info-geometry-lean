import InfoGeometry.Canonical.ChiralCuntzFockSpaceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Clifford.Cl11TensorTower

/-!
# A finite chiral/Fock/twistor algebraic readout

This owner composes existing finite theorems.  It does not construct a
super-Kähler manifold, a twistor space, an infinite CAR representation, or a
Fock-space completion.  The Cuntz statement and the exterior-algebra vacuum
statement live in their respective carriers and are not identified here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperKahlerTwistorFockBridge

open ChiralCuntzSuperchargeBridge
open ChiralCuntzFockSpaceBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge

variable {R : Type*} [Ring R] [StarRing R]

/-- The finite Cuntz chiral number expression `Q₊ Q₋`. -/
def particleNumberOp
    (sys : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R) : R :=
  Q_plus sys * Q_minus sys

@[simp] theorem particleNumberOp_eq_chiralProjection
    (sys : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R) :
    particleNumberOp sys = P_plus sys := rfl

theorem particleNumberOp_isProjection
    (sys : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R) :
    IsSelfAdjoint (particleNumberOp sys) ∧
      particleNumberOp sys * particleNumberOp sys = particleNumberOp sys := by
  simpa [particleNumberOp] using P_plus_isProjection sys

/-- The exterior-algebra vacuum is annihilated by contraction. -/
theorem exteriorVacuum_annihilated
    {S U : Type*} [CommRing S] [AddCommGroup U] [Module S U]
    (u : U) :
    (contractionOp (evaluationLinear u))
        (FockVacuumAnnihilationBridge.vacuumState S U) = 0 := by
  exact FockVacuumAnnihilationBridge.annihilation_vacuum_zero u

/-- The rational determinant polynomial used for the finite twistor readout. -/
def twistorNorm (alpha beta xi eta : ℚ) : ℚ :=
  alpha * beta - xi * eta

@[simp] theorem twistorNorm_upper_nilpotent (xi : ℚ) :
    twistorNorm 0 0 xi 0 = 0 := by
  simp [twistorNorm]

@[simp] theorem twistorNorm_lower_nilpotent (eta : ℚ) :
    twistorNorm 0 0 0 eta = 0 := by
  simp [twistorNorm]

theorem cl11_single_site_witt_packet :
    InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase *
        InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase = 0 ∧
      InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase *
        InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase = 0 ∧
      (InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase *
          InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase +
        InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase *
          InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase) =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact ⟨InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase_sq,
    InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase_sq,
    InfoGeometry.Clifford.Cl11TensorTower.realEncodedWitt_anticomm⟩

end SuperKahlerTwistorFockBridge

end Canonical
