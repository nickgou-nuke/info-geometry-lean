/-
InfoGeometry/Application/BlackHoleEntropyReadout.lean

Witness-gated application wrapper over the existing canonical surfaces.

This file is a compatibility adapter only. It does not introduce a new owner
theory for entropy, area, or gravity.

Consumed surfaces:
- SplitSuperGeometry
- ChiralOperatorAlgebra
- OperatorThermodynamics
- RealModularBerryBridge
- NarainSupervolumeBridgeData
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebraic.ChiralOperatorAlgebra
import InfoGeometry.Algebraic.NarainSupervolumeBridgeData
import InfoGeometry.Algebraic.SplitSuperGeometry
import InfoGeometry.Bridge.RealModularBerryBridge
import InfoGeometry.Canonical.OperatorThermodynamics

noncomputable section

namespace InfoGeometry.Application

open InfoGeometry.Algebraic
open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Algebraic.SplitSuperGeometry
open InfoGeometry.Bridge
open InfoGeometry.Canonical.OperatorThermodynamics

/--
Witness-gated black-hole entropy readout.

This is a compatibility adapter, not a new owner:
- the split Clifford parity lives in `split`;
- the chiral operator algebra lives in `chiral`;
- the modular thermodynamic readout lives in `thermodynamics`;
- the modular Berry limit data lives in `modularBerry`;
- the Narain lattice/supervolume readout lives in `narain`.
-/
structure BlackHoleEntropyReadout
    (n : ℕ)
    (G X Rotor Bivector : Type*)
    [Group G] [MulAction G X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector]
    [NormedAddCommGroup (Cl_nn n)] [NormedSpace ℝ (Cl_nn n)] where
  split : SplitSuperGeometry n
  chiral : ChiralOperatorAlgebra n
  splitChiralCompat : split.parity = chiral.chiralParity
  thermodynamics : OperatorThermodynamicsPacket (Cl_nn n)
  thermoChiralCompat :
    ∀ v : Cl_nn n,
      thermodynamics.modular.modularHamiltonian v =
        chiral.modularHamiltonian v
  modularBerry : RealModularBerryBridgeData G X Rotor Bivector
  narain : NarainSupervolumeBridgeData n
  thermoNarainCompat :
    thermodynamics.supervolumeReadout = narain.supervolumeReadout

namespace BlackHoleEntropyReadout

variable
    {n : ℕ}
    {G X Rotor Bivector : Type*}
    [Group G] [MulAction G X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector]
    [NormedAddCommGroup (Cl_nn n)] [NormedSpace ℝ (Cl_nn n)]

/-- The canonical modular Hamiltonian readout. -/
def modularHamiltonian
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    Cl_nn n →L[ℝ] Cl_nn n :=
  B.thermodynamics.modularHamiltonian

/-- The canonical supervolume readout. -/
def supervolumeReadout
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) : ℝ :=
  B.thermodynamics.supervolumeReadout

/-- The entropy shadow, packaged as a witness-gated scalar readout. -/
def entropyReadout
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) : ℝ :=
  B.thermodynamics.supervolumeReadout

/-- The Narain negative-log potential shadow. -/
def negativeLogPotential
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) : ℝ :=
  B.narain.negativeLogPotential

@[simp]
theorem entropyReadout_eq_supervolumeReadout
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    B.entropyReadout = B.supervolumeReadout :=
  rfl

@[simp]
theorem modularHamiltonian_eq_negativeLogModularOperator
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    B.modularHamiltonian = B.thermodynamics.negativeLogModularOperator := by
  simp [modularHamiltonian, OperatorThermodynamicsPacket.modularHamiltonian_eq_negativeLogModularOperator]

@[simp]
theorem negativeLogPotential_eq_narain
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    B.negativeLogPotential = - Real.log B.narain.supervolume := by
  rw [negativeLogPotential, B.narain.effectiveAction_eq_negLog]

@[simp]
theorem splitParity_eq_chiralParity
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    B.split.parity = B.chiral.chiralParity :=
  B.splitChiralCompat

theorem thermo_modularHamiltonian_eq_chiral
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    (fun v : Cl_nn n => B.thermodynamics.modular.modularHamiltonian v) =
      fun v : Cl_nn n => B.chiral.modularHamiltonian v := by
  funext v
  exact B.thermoChiralCompat v

@[simp]
theorem thermo_modularHamiltonian_apply_eq_chiral
    (B : BlackHoleEntropyReadout n G X Rotor Bivector)
    (v : Cl_nn n) :
    B.thermodynamics.modular.modularHamiltonian v =
      B.chiral.modularHamiltonian v :=
  B.thermoChiralCompat v

@[simp]
theorem thermo_supervolumeReadout_eq_narainSupervolume
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    B.supervolumeReadout = B.narain.supervolumeReadout :=
  B.thermoNarainCompat

@[simp]
theorem entropyReadout_eq_narainSupervolume
    (B : BlackHoleEntropyReadout n G X Rotor Bivector) :
    B.entropyReadout = B.narain.supervolumeReadout := by
  simpa [entropyReadout] using B.thermoNarainCompat

end BlackHoleEntropyReadout

end InfoGeometry.Application
