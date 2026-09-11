/-
InfoGeometry/Specialization/ModularBerrySpecialization.lean

Operator-first modular Berry specialization.

No complex imports.
No Mathlib.NumberTheory.Modular import.
No coordinate upper-half-plane substrate.

This file uses raw `SL(2, ℤ)` matrices as generators and pushes a split
Clifford rotor cocycle through the generic bulk-boundary bridge.
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

import InfoGeometry.Algebraic.RealModularReadout
import InfoGeometry.Algebraic.SplitCliffordCarrier
import InfoGeometry.Bridge.RealModularBerryBridge

noncomputable section

open scoped MatrixGroups
open Filter

namespace InfoGeometry.Specialization.ModularBerry

open InfoGeometry.Algebraic
open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Bridge

/-- The arithmetic modular group, used only as a matrix group in the real core. -/
abbrev SL2Z : Type :=
  SL(2, ℤ)

/-- The usual `S` generator, represented as a raw `SL(2, ℤ)` matrix. -/
def matrixS : SL2Z :=
  ⟨!![(0 : ℤ), -1; 1, 0], by
    norm_num [Matrix.det_fin_two_of]⟩

/-- The usual translation generator `T`, represented as a raw `SL(2, ℤ)` matrix. -/
def matrixT : SL2Z :=
  InfoGeometry.Algebraic.matrixT

/-- The elliptic generator candidate `ST`. -/
def matrixST : SL2Z :=
  matrixS * matrixT

/--
Push a rotor cocycle through a group homomorphism of rotor targets.
-/
def mapRotorCocycle
    {G X R R' : Type*}
    [Group G] [MulAction G X]
    [Group R] [Group R']
    (C : MulActionCocycle G X R)
    (φ : R →* R') :
    MulActionCocycle G X R' where
  toFun g x := φ (C g x)
  map_one := by
    intro x
    rw [C.map_one x]
    exact φ.map_one
  map_mul := by
    intro g h x
    rw [C.map_mul g h x]
    exact φ.map_mul (C g (h • x)) (C h x)

/--
Optional sign-twisted Weyl realization.

This is where D4/triality, exceptional lattices, or other Weyl data may enter.
The core theorem does not assume that `SL(2, ℤ)` is itself a Weyl group.
It only requires a chosen realization into the split Clifford rotor target.
-/
structure SignTwistedWeylRotorRealization
    (n : ℕ)
    (Weyl : Type*)
    [Group Weyl] where
  weylMap : SL2Z →* Weyl
  weylRotor : Weyl →* SplitSpinGroup n
  signRotor : SL2Z →* SplitSpinGroup n
  readout : SL2Z →* SplitSpinGroup n
  readout_eq :
    ∀ γ : SL2Z,
      readout γ = signRotor γ * weylRotor (weylMap γ)

/--
An ordered stabilizer sample contributing to the boundary anomaly.
-/
structure StabilizerSample
    (G X Rotor : Type*)
    [Group G] [MulAction G X]
    [Group Rotor] where
  point : X
  stabilizer : Subgroup G
  stabilizes : ∀ γ ∈ stabilizer, γ • point = point
  anomaly : MulActionCocycle G X Rotor → Rotor

/--
A modular Clifford Berry datum.

`spinCocycle` is the primitive Clifford rotor cocycle.
`rotorReadout` pushes the Clifford rotor into the chosen topological rotor
group.

The topological/analytic content is isolated in `cusp_tendsto` and
`finite_stokes`.
-/
structure ModularCliffordBerryData
    (n : ℕ)
    (Weyl X Rotor Bivector : Type*)
    [Group Weyl]
    [MulAction SL2Z X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector] where
  /-- Explicit sign-twisted Weyl realization, kept as data. -/
  signTwistedWeyl : SignTwistedWeylRotorRealization n Weyl

  /-- Split Clifford rotor cocycle. -/
  spinCocycle : MulActionCocycle SL2Z X (SplitSpinGroup n)

  /-- Concrete rotor readout. -/
  rotorReadout : SplitSpinGroup n →* Rotor

  /-- Bulk bivector integral, indexed by truncation/flow parameter. -/
  bulkIntegral : ℝ → Bivector

  /-- Exponentiation/readout from the bivector line into the rotor group. -/
  exponentiate : Bivector → Rotor

  /-- Ordered stabilizer anomaly samples. -/
  stabilizerSamples : List (StabilizerSample SL2Z X Rotor)

  /-- Boundary/cusp approach. -/
  cuspRay : ℝ → X

  /-- Limiting cusp anomaly. -/
  cuspAnomaly : Rotor

  /--
  Cusp convergence gate for the `T` generator.

  This is the topological input.
  -/
  cusp_tendsto :
    Tendsto
      (fun Y : ℝ =>
        rotorReadout (spinCocycle matrixT (cuspRay Y)))
      atTop
      (nhds cuspAnomaly)

  /--
  Finite-height Stokes law.

  This is the geometric/analytic input.
  The order of `List.prod` is meaningful and is not commuted.
  -/
  finite_stokes :
    ∀ Y : ℝ,
      exponentiate (bulkIntegral Y) =
        (stabilizerSamples.map
          (fun A =>
            A.anomaly
              (mapRotorCocycle spinCocycle rotorReadout))).prod *
        rotorReadout (spinCocycle matrixT (cuspRay Y))

namespace ModularCliffordBerryData

variable
    {n : ℕ}
    {Weyl X Rotor Bivector : Type*}
    [Group Weyl]
    [MulAction SL2Z X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector]

/-- Rotor-valued cocycle obtained from the split Clifford cocycle. -/
def rotorCocycle
    (D : ModularCliffordBerryData n Weyl X Rotor Bivector) :
    MulActionCocycle SL2Z X Rotor :=
  mapRotorCocycle D.spinCocycle D.rotorReadout

/--
Convert modular Clifford data into the generic real modular Berry bridge data.
-/
def toBridgeData
    (D : ModularCliffordBerryData n Weyl X Rotor Bivector) :
    RealModularBerryBridgeData SL2Z X Rotor Bivector where
  cocycle := D.rotorCocycle
  bulkIntegral := D.bulkIntegral
  exponentiate := D.exponentiate
  stabilizerProduct :=
    (D.stabilizerSamples.map
      (fun A => A.anomaly (D.rotorCocycle))).prod
  cuspGenerator := matrixT
  cuspRay := D.cuspRay
  cuspAnomaly := D.cuspAnomaly
  cusp_tendsto := by
    simpa [rotorCocycle, mapRotorCocycle] using D.cusp_tendsto
  finite_stokes := by
    intro Y
    simpa [rotorCocycle, mapRotorCocycle] using D.finite_stokes Y

/--
The modular Clifford Berry bridge.

The exponentiated bulk bivector is determined by the ordered boundary
anomalies once the finite Stokes law and cusp limit are supplied.
-/
theorem bulkRotor_limit
    (D : ModularCliffordBerryData n Weyl X Rotor Bivector) :
    Tendsto
      (RealModularBerryBridgeData.bulkRotor D.toBridgeData)
      atTop
      (nhds (RealModularBerryBridgeData.boundaryRotor D.toBridgeData)) :=
  InfoGeometry.Bridge.ModularBerryTranslation.bulk_bivector_limit_eq_boundary_rotors
    D.toBridgeData

end ModularCliffordBerryData

end InfoGeometry.Specialization.ModularBerry
