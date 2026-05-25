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

  /-- Compatibility between the bridge record and the local affine datum. -/
  bridge_affine_eq : bridge.affine = affine

  /-- Compatibility between the bridge record and the local Virasoro datum. -/
  bridge_virasoro_eq : bridge.virasoro = virasoro

  /-- Finite-algebra element representing the `u₊` lightcone direction. -/
  uPlusRoot : Finite

  /-- Finite-algebra element representing the `u₋` lightcone direction. -/
  uMinusRoot : Finite

  /-- Model-specific law that the chosen roots are lightcone directions. -/
  lightconeCurrentLaw : Prop
  lightconeCurrentLaw_holds : lightconeCurrentLaw

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

/-- Compatibility between the bridge record and the local affine datum. -/
theorem bridge_affine_eq_theorem : B.bridge.affine = B.affine :=
  B.bridge_affine_eq

/-- Compatibility between the bridge record and the local Virasoro datum. -/
theorem bridge_virasoro_eq_theorem : B.bridge.virasoro = B.virasoro :=
  B.bridge_virasoro_eq

/-- Evidence for the installed lightcone-current law. -/
theorem lightconeCurrentLaw_holds_theorem : B.lightconeCurrentLaw :=
  B.lightconeCurrentLaw_holds

/-- Bracket of two positive lightcone current modes, inherited from the affine owner. -/
@[rep_depth operator]
theorem uPlusCurrent_bracket
    (m n : ℤ)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅B.affine.Current m X, B.affine.Current n Y⁆ =
          B.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * B.affine.killingForm X Y) •
              (if m + n = 0 then B.affine.kCentral else 0)) :
    ⁅B.uPlusCurrent m, B.uPlusCurrent n⁆ =
      B.affine.Current (m + n) ⁅B.uPlusRoot, B.uPlusRoot⁆ +
        ((m : ℝ) * B.affine.killingForm B.uPlusRoot B.uPlusRoot) •
          (if m + n = 0 then B.affine.kCentral else 0) := by
  unfold uPlusCurrent
  exact B.affine.current_mode_bracket hbr m n B.uPlusRoot B.uPlusRoot

/-- Bracket of two negative lightcone current modes, inherited from the affine owner. -/
@[rep_depth operator]
theorem uMinusCurrent_bracket
    (m n : ℤ)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅B.affine.Current m X, B.affine.Current n Y⁆ =
          B.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * B.affine.killingForm X Y) •
              (if m + n = 0 then B.affine.kCentral else 0)) :
    ⁅B.uMinusCurrent m, B.uMinusCurrent n⁆ =
      B.affine.Current (m + n) ⁅B.uMinusRoot, B.uMinusRoot⁆ +
        ((m : ℝ) * B.affine.killingForm B.uMinusRoot B.uMinusRoot) •
          (if m + n = 0 then B.affine.kCentral else 0) := by
  unfold uMinusCurrent
  exact B.affine.current_mode_bracket hbr m n B.uMinusRoot B.uMinusRoot

/-- Mixed lightcone current bracket, inherited from the affine owner. -/
@[rep_depth operator]
theorem uPlus_uMinusCurrent_bracket
    (m n : ℤ)
    (hbr :
      ∀ (m n : ℤ) (X Y : Finite),
        ⁅B.affine.Current m X, B.affine.Current n Y⁆ =
          B.affine.Current (m + n) ⁅X, Y⁆ +
            ((m : ℝ) * B.affine.killingForm X Y) •
              (if m + n = 0 then B.affine.kCentral else 0)) :
    ⁅B.uPlusCurrent m, B.uMinusCurrent n⁆ =
      B.affine.Current (m + n) ⁅B.uPlusRoot, B.uMinusRoot⁆ +
        ((m : ℝ) * B.affine.killingForm B.uPlusRoot B.uMinusRoot) •
          (if m + n = 0 then B.affine.kCentral else 0) := by
  unfold uPlusCurrent uMinusCurrent
  exact B.affine.current_mode_bracket hbr m n B.uPlusRoot B.uMinusRoot

/-- Virasoro reparametrization of positive lightcone current modes. -/
@[rep_depth operator]
theorem virasoro_acts_on_uPlusCurrent
    (m n : ℤ)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅B.bridge.virasoro.Lmode m, B.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • B.bridge.affine.Current (m + n) X) :
    ⁅B.virasoro.Lmode m, B.uPlusCurrent n⁆ =
      (-(n : ℝ)) • B.uPlusCurrent (m + n) := by
  have h :=
    B.bridge.virasoro_acts_on_currents m n B.uPlusRoot hact
  simpa [uPlusCurrent, B.bridge_virasoro_eq_theorem, B.bridge_affine_eq_theorem] using h

/-- Virasoro reparametrization of negative lightcone current modes. -/
@[rep_depth operator]
theorem virasoro_acts_on_uMinusCurrent
    (m n : ℤ)
    (hact :
      ∀ (m n : ℤ) (X : Finite),
        ⁅B.bridge.virasoro.Lmode m, B.bridge.affine.Current n X⁆ =
          (-(n : ℝ)) • B.bridge.affine.Current (m + n) X) :
    ⁅B.virasoro.Lmode m, B.uMinusCurrent n⁆ =
      (-(n : ℝ)) • B.uMinusCurrent (m + n) := by
  have h :=
    B.bridge.virasoro_acts_on_currents m n B.uMinusRoot hact
  simpa [uMinusCurrent, B.bridge_virasoro_eq_theorem, B.bridge_affine_eq_theorem] using h

/-- The bridge central charge remains the Sugawara-calibrated central charge. -/
@[rep_depth operator]
theorem centralCharge_calibrated :
    (hcc : B.bridge.centralCharge =
      B.bridge.level * B.bridge.finiteDimension /
        (B.bridge.level + B.bridge.dualCoxeterNumber)) →
    B.bridge.centralCharge =
      B.bridge.level * B.bridge.finiteDimension /
        (B.bridge.level + B.bridge.dualCoxeterNumber) :=
  B.bridge.centralCharge_calibrated

end LightConeAffineCurrentBridge

end InfoGeometry.OperatorAlgebra.LightConeAffineCurrentBridge
