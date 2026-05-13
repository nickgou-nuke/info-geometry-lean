import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LightConeAffineCurrentBridge

open InfoGeometry.OperatorAlgebra

/--
Affine-current socket for lightcone-arrow modes.

This bridge does not identify the nilpotent lightcone arrows with Virasoro
generators.  It records that selected finite symmetry elements represent the
`u₊` and `u₋` lightcone directions, then routes their loop/current modes through
the already-owned affine/Virasoro bridge.
-/
@[rep_depth operator]
structure LightConeAffineCurrentBridge
    (Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where

  affine :
    AffineVirasoroBridge.AffineCurrentDatum Finite Alg

  virasoro :
    AffineVirasoroBridge.VirasoroDatum Alg

  bridge :
    AffineVirasoroBridge.AffineVirasoroBridgeDatum Finite Alg

  /-- Finite-algebra element representing the `u₊` lightcone direction. -/
  uPlusRoot : Finite

  /-- Finite-algebra element representing the `u₋` lightcone direction. -/
  uMinusRoot : Finite

  /--
  Compatibility between the separately supplied bridge and the current/Virasoro
  data stored in this lightcone socket.
  -/
  bridge_affine_eq : bridge.affine = affine

  /--
  Compatibility between the separately supplied bridge and the current/Virasoro
  data stored in this lightcone socket.
  -/
  bridge_virasoro_eq : bridge.virasoro = virasoro

  /--
  Model-specific certification that the chosen roots really are the lightcone
  current directions.  This is a witness field by design: the algebra remains
  owned by the modules that construct the lightcone arrows.
  -/
  lightconeCurrentLaw : Prop
  lightconeCurrentWitness : lightconeCurrentLaw

namespace LightConeAffineCurrentBridge

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : LightConeAffineCurrentBridge Finite Alg)

/-- The positive lightcone current mode `J⁺_n`. -/
@[rep_depth operator]
def uPlusCurrent (n : ℤ) : Alg :=
  B.affine.Current n B.uPlusRoot

/-- The negative lightcone current mode `J⁻_n`. -/
@[rep_depth operator]
def uMinusCurrent (n : ℤ) : Alg :=
  B.affine.Current n B.uMinusRoot

/-- Re-export of the supplied lightcone-current certification law. -/
@[rep_depth operator]
theorem lightconeCurrentLaw_holds :
    B.lightconeCurrentLaw :=
  B.lightconeCurrentWitness

/-- Bracket of two positive lightcone current modes, inherited from the affine owner. -/
@[rep_depth operator]
theorem uPlusCurrent_bracket
    (m n : ℤ) :
    ⁅B.uPlusCurrent m, B.uPlusCurrent n⁆ =
      B.affine.Current (m + n) ⁅B.uPlusRoot, B.uPlusRoot⁆ +
        ((m : ℝ) * B.affine.killingForm B.uPlusRoot B.uPlusRoot) •
          (if m + n = 0 then B.affine.kCentral else 0) := by
  unfold uPlusCurrent
  exact B.affine.current_mode_bracket m n B.uPlusRoot B.uPlusRoot

/-- Bracket of two negative lightcone current modes, inherited from the affine owner. -/
@[rep_depth operator]
theorem uMinusCurrent_bracket
    (m n : ℤ) :
    ⁅B.uMinusCurrent m, B.uMinusCurrent n⁆ =
      B.affine.Current (m + n) ⁅B.uMinusRoot, B.uMinusRoot⁆ +
        ((m : ℝ) * B.affine.killingForm B.uMinusRoot B.uMinusRoot) •
          (if m + n = 0 then B.affine.kCentral else 0) := by
  unfold uMinusCurrent
  exact B.affine.current_mode_bracket m n B.uMinusRoot B.uMinusRoot

/-- Mixed lightcone current bracket, inherited from the affine owner. -/
@[rep_depth operator]
theorem uPlus_uMinusCurrent_bracket
    (m n : ℤ) :
    ⁅B.uPlusCurrent m, B.uMinusCurrent n⁆ =
      B.affine.Current (m + n) ⁅B.uPlusRoot, B.uMinusRoot⁆ +
        ((m : ℝ) * B.affine.killingForm B.uPlusRoot B.uMinusRoot) •
          (if m + n = 0 then B.affine.kCentral else 0) := by
  unfold uPlusCurrent uMinusCurrent
  exact B.affine.current_mode_bracket m n B.uPlusRoot B.uMinusRoot

/-- Virasoro reparametrization of positive lightcone current modes. -/
@[rep_depth operator]
theorem virasoro_acts_on_uPlusCurrent
    (m n : ℤ) :
    ⁅B.virasoro.Lmode m, B.uPlusCurrent n⁆ =
      (-(n : ℝ)) • B.uPlusCurrent (m + n) := by
  unfold uPlusCurrent
  have h :=
    B.bridge.virasoro_acts_on_currents_at m n B.uPlusRoot
  rw [B.bridge_virasoro_eq, B.bridge_affine_eq] at h
  exact h

/-- Virasoro reparametrization of negative lightcone current modes. -/
@[rep_depth operator]
theorem virasoro_acts_on_uMinusCurrent
    (m n : ℤ) :
    ⁅B.virasoro.Lmode m, B.uMinusCurrent n⁆ =
      (-(n : ℝ)) • B.uMinusCurrent (m + n) := by
  unfold uMinusCurrent
  have h :=
    B.bridge.virasoro_acts_on_currents_at m n B.uMinusRoot
  rw [B.bridge_virasoro_eq, B.bridge_affine_eq] at h
  exact h

/-- The bridge central charge remains the Sugawara-calibrated central charge. -/
@[rep_depth operator]
theorem centralCharge_calibrated :
    B.bridge.centralCharge =
      B.bridge.level * B.bridge.finiteDimension /
        (B.bridge.level + B.bridge.dualCoxeterNumber) :=
  B.bridge.centralCharge_calibrated

end LightConeAffineCurrentBridge

end InfoGeometry.OperatorAlgebra.LightConeAffineCurrentBridge
