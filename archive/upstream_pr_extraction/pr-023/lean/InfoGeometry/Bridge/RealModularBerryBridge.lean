import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Basic
import InfoGeometry.Algebraic.RealModularReadout

/-!
InfoGeometry/Bridge/RealModularBerryBridge.lean

Operator-first modular Berry carrier and Stokes bridge.
No complex coordinates.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Bridge

open Filter
open InfoGeometry.Algebraic

/--
Real modular Berry bridge data.

This is the operator-first carrier:
the cocycle supplies the boundary readout,
the real bulk integral supplies the additive bivector phase,
and the ordered rotor product is the boundary anomaly.
-/
structure RealModularBerryBridgeData
    (G X Rotor Bivector : Type*)
    [Group G] [MulAction G X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector] where
  /-- The rotor-valued modular cocycle. -/
  cocycle : MulActionCocycle G X Rotor

  /-- The real bulk bivector integral at cutoff height `Y`. -/
  bulkIntegral : ℝ → Bivector

  /-- Exponentiation from the bivector line into the rotor group. -/
  exponentiate : Bivector → Rotor

  /-- Ordered boundary anomaly factor. -/
  stabilizerProduct : Rotor

  /-- Cusp generator in the discrete symmetry group. -/
  cuspGenerator : G

  /-- Cusp ray in the real substrate. -/
  cuspRay : ℝ → X

  /-- Limiting cusp anomaly rotor. -/
  cuspAnomaly : Rotor

  /-- Cusp-limit convergence of the modular cocycle on the ray. -/
  cusp_tendsto :
    Tendsto
      (fun Y : ℝ => cocycle cuspGenerator (cuspRay Y))
      atTop
      (nhds cuspAnomaly)

  /--
  Finite-height Stokes law.

  The exponentiated bulk integral is resolved by the ordered boundary anomaly.
  -/
  finite_stokes_law :
    ∀ Y : ℝ,
      exponentiate (bulkIntegral Y) =
        stabilizerProduct * cocycle cuspGenerator (cuspRay Y)

namespace RealModularBerryBridgeData

variable
    {G X Rotor Bivector : Type*}
    [Group G] [MulAction G X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector]

/-- The limiting boundary rotor. -/
def boundaryRotor (D : RealModularBerryBridgeData G X Rotor Bivector) : Rotor :=
  D.stabilizerProduct * D.cuspAnomaly

/-- The exponentiated bulk rotor at cutoff height `Y`. -/
def bulkRotor
    (D : RealModularBerryBridgeData G X Rotor Bivector)
    (Y : ℝ) : Rotor :=
  D.exponentiate (D.bulkIntegral Y)

/--
The exponentiated bulk rotor tends to the ordered boundary anomaly product.
-/
theorem bulkBoundary_tendsto
    (D : RealModularBerryBridgeData G X Rotor Bivector) :
    Tendsto D.bulkRotor atTop (nhds D.boundaryRotor) := by
  have hmul :
      Tendsto
        (fun Y : ℝ =>
          D.stabilizerProduct * D.cocycle D.cuspGenerator (D.cuspRay Y))
        atTop
        (nhds (D.stabilizerProduct * D.cuspAnomaly)) :=
    tendsto_const_nhds.mul D.cusp_tendsto
  have hfun :
      D.bulkRotor =
        fun Y : ℝ =>
          D.stabilizerProduct *
            D.cocycle D.cuspGenerator (D.cuspRay Y) := by
    funext Y
    rw [RealModularBerryBridgeData.bulkRotor, D.finite_stokes_law Y]
  rw [hfun]
  simpa [RealModularBerryBridgeData.boundaryRotor] using hmul

end RealModularBerryBridgeData

namespace ModularBerryTranslation

/--
Modular Berry carrier.

Klein/Hestenes reading:
the modular symmetry action plus the real bulk curvature data form the carrier;
the rotor-valued boundary anomalies are the invariant readout.
-/
structure ModularBerryCarrier
    (G X Rotor Bivector : Type*)
    [Group G] [MulAction G X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector] where
  bridgeData : RealModularBerryBridgeData G X Rotor Bivector

namespace ModularBerryCarrier

variable
    {G X Rotor Bivector : Type*}
    [Group G] [MulAction G X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector]

/-- The additive bulk bivector at cutoff height `Y`. -/
def bivectorCoordinate (M : ModularBerryCarrier G X Rotor Bivector) (Y : ℝ) : Bivector :=
  M.bridgeData.bulkIntegral Y

/-- The bulk rotor readout at cutoff height `Y`. -/
def bulkInvariant (M : ModularBerryCarrier G X Rotor Bivector) (Y : ℝ) : Rotor :=
  M.bridgeData.bulkRotor Y

/-- The ordered boundary anomaly readout at cutoff height `Y`. -/
def boundarySymmetryReadout (M : ModularBerryCarrier G X Rotor Bivector) (Y : ℝ) : Rotor :=
  M.bridgeData.stabilizerProduct *
    M.bridgeData.cocycle M.bridgeData.cuspGenerator (M.bridgeData.cuspRay Y)

/-- The limiting boundary anomaly. -/
def totalBoundaryAnomaly (M : ModularBerryCarrier G X Rotor Bivector) : Rotor :=
  M.bridgeData.boundaryRotor

/-- Finite-height Stokes matching. -/
structure FiniteStokesGate (M : ModularBerryCarrier G X Rotor Bivector) where
  stokes_match : ∀ Y : ℝ, M.bulkInvariant Y = M.boundarySymmetryReadout Y

/-- Cusp convergence gate. -/
structure AnalyticCuspGate (M : ModularBerryCarrier G X Rotor Bivector) where
  cusp_limit : Tendsto M.boundarySymmetryReadout atTop (nhds M.totalBoundaryAnomaly)

/-- Specialization into the actual modular Berry data. -/
structure GeometricSpecialization (M : ModularBerryCarrier G X Rotor Bivector) where
  finite_stokes : FiniteStokesGate M
  cusp_convergence : AnalyticCuspGate M

/--
Main bridge theorem.

The exponentiated bulk rotor is determined by the ordered boundary anomalies
once the finite Stokes law and cusp limit are supplied.
-/
theorem bulkInvariant_limit_eq_totalAnomaly_of_specialization
    {M : ModularBerryCarrier G X Rotor Bivector}
    (hM : GeometricSpecialization M) :
    Tendsto M.bulkInvariant atTop (nhds M.totalBoundaryAnomaly) := by
  have hfun : M.bulkInvariant = M.boundarySymmetryReadout := by
    funext Y
    exact hM.finite_stokes.stokes_match Y
  rw [hfun]
  exact hM.cusp_convergence.cusp_limit

/-- Canonical wrapper around the verified bridge data. -/
def canonicalModularBerry
    (D : RealModularBerryBridgeData G X Rotor Bivector) :
    ModularBerryCarrier G X Rotor Bivector :=
  { bridgeData := D }

/-- The canonical specialization induced by the bridge data. -/
def canonicalSpecialization
    (D : RealModularBerryBridgeData G X Rotor Bivector) :
    GeometricSpecialization (canonicalModularBerry D) where
  finite_stokes := { stokes_match := fun Y => D.finite_stokes_law Y }
  cusp_convergence := by
    refine ⟨?_⟩
    have hmul :
        Tendsto
          (fun Y : ℝ =>
            D.stabilizerProduct * D.cocycle D.cuspGenerator (D.cuspRay Y))
          atTop
          (nhds (D.stabilizerProduct * D.cuspAnomaly)) := by
      exact tendsto_const_nhds.mul D.cusp_tendsto
    simpa [
      canonicalModularBerry,
      ModularBerryCarrier.boundarySymmetryReadout,
      ModularBerryCarrier.totalBoundaryAnomaly,
      RealModularBerryBridgeData.boundaryRotor
    ] using hmul

/-- Canonical bulk-to-boundary limit theorem. -/
theorem canonical_bulkInvariant_eq_totalAnomaly
    (D : RealModularBerryBridgeData G X Rotor Bivector) :
    Tendsto (canonicalModularBerry D).bulkInvariant
      atTop
      (nhds (canonicalModularBerry D).totalBoundaryAnomaly) :=
  bulkInvariant_limit_eq_totalAnomaly_of_specialization
    (canonicalSpecialization D)

end ModularBerryCarrier

/--
Preferred bridge name.

The exponentiated regularized bulk bivector integral tends exactly to the
ordered rotor product of the geometric symmetry anomalies.
-/
theorem bulk_bivector_limit_eq_boundary_rotors
    {G X Rotor Bivector : Type*}
    [Group G] [MulAction G X]
    [Group Rotor] [TopologicalSpace Rotor] [ContinuousMul Rotor]
    [NormedAddCommGroup Bivector] [NormedSpace ℝ Bivector]
    (D : RealModularBerryBridgeData G X Rotor Bivector) :
    Tendsto D.bulkRotor atTop (nhds D.boundaryRotor) :=
  D.bulkBoundary_tendsto

end ModularBerryTranslation

end InfoGeometry.Bridge
