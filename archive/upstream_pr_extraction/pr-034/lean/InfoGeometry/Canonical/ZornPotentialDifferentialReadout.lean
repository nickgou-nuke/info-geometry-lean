import InfoGeometry.Canonical.ZornPotentialGradientAlgebraicBridge
import Mathlib.Tactic

/-!
# Differential readout for the Zorn potential product

The algebraic Zorn product and the differential calculus are separate layers.
This owner supplies independent differential readouts for `φ` and `A`, then
proves the resulting component identities.  In particular, it records the
sign forced by the symmetric Zorn layout: the lower vector block is the
negative of the upper block.  No Maxwell equation is postulated here.
-/

namespace InfoGeometry.Canonical.ZornPotentialDifferentialReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

local notation "Vec3" => ZornVec3 R
local notation "ZM" => ZornVectorMatrix R

/-- Differential data needed to read a potential product componentwise. -/
structure PotentialDifferentialData where
  timePotential : R
  scalarPotential : R
  spatialPotential : Vec3
  timePotentialDerivative : R
  spatialPotentialDerivative : Vec3
  scalarGradient : Vec3
  potentialDivergence : R
  potentialCurl : Vec3

def lorenzResidual (P : PotentialDifferentialData (R := R)) : R :=
  P.timePotentialDerivative - P.potentialDivergence

def electricReadout (P : PotentialDifferentialData (R := R)) : Vec3 :=
  fun i => -(P.scalarGradient i + P.spatialPotentialDerivative i)

def magneticReadout (P : PotentialDifferentialData (R := R)) : Vec3 :=
  P.potentialCurl

def upperFieldReadout (P : PotentialDifferentialData (R := R)) : Vec3 :=
  fun i => P.spatialPotentialDerivative i + P.scalarGradient i -
    P.potentialCurl i

def differentialFieldReadout (P : PotentialDifferentialData (R := R)) : ZM :=
  ⟨lorenzResidual P, upperFieldReadout P,
    fun i => -(upperFieldReadout P i), lorenzResidual P⟩

@[simp] theorem upperFieldReadout_eq_neg_electric_add_magnetic
    (P : PotentialDifferentialData (R := R)) :
    upperFieldReadout P =
      fun i => -(electricReadout P i + magneticReadout P i) := by
  funext i
  simp [upperFieldReadout, electricReadout, magneticReadout]
  ring

@[simp] theorem lowerFieldReadout_eq_electric_add_magnetic
    (P : PotentialDifferentialData (R := R)) :
    (fun i => -(upperFieldReadout P i)) =
      fun i => electricReadout P i + magneticReadout P i := by
  funext i
  rw [upperFieldReadout_eq_neg_electric_add_magnetic P]
  simp

theorem differentialFieldReadout_eq_symmetric_components
    (P : PotentialDifferentialData (R := R)) :
    differentialFieldReadout P =
      ⟨P.timePotentialDerivative - P.potentialDivergence,
        fun i => P.spatialPotentialDerivative i + P.scalarGradient i -
          P.potentialCurl i,
        fun i => -(P.spatialPotentialDerivative i + P.scalarGradient i -
          P.potentialCurl i),
        P.timePotentialDerivative - P.potentialDivergence⟩ := by
  rfl

theorem lorenzGauge_zero_diagonal
    (P : PotentialDifferentialData (R := R))
    (hGauge : P.timePotentialDerivative = P.potentialDivergence) :
    differentialFieldReadout P =
      ⟨0, upperFieldReadout P,
        fun i => -(upperFieldReadout P i), 0⟩ := by
  ext i <;> simp [differentialFieldReadout, lorenzResidual, hGauge]

end InfoGeometry.Canonical.ZornPotentialDifferentialReadout
