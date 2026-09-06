import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic
import proofs.ThermalBoostLorentzSuperalgebra
import proofs.KTheoryChernConfinementSignature
import proofs.NonAbelianBrillouinKleinBottle
import proofs.DikinGoutevTonevBridge

/-!
# Thermodynamic Lorentz boost: closed symbolic K₀ bookkeeping layer

This file records the finite symbolic K₀ carrier used by the current graph and
proves the closed fact that this carrier is independent of the chosen boost
parameter.  It stays at the symbolic bookkeeping layer rather than introducing
an analytic crossed product, KMS modular action, Kasparov cycle, or homotopy
transport.
-/

noncomputable section

namespace ThermodynamicLorentzBoost

/-- Thermodynamic rapidity / boost parameter. -/
structure BoostParameter where
  eta : ℝ
  eta_nonneg : 0 ≤ eta

/-- Zero boost. -/
def zeroBoost : BoostParameter where
  eta := 0
  eta_nonneg := le_rfl

/--
Symbolic carrier for the Cuntz-wallpaper algebra with a thermodynamic boost.

This is bookkeeping data only.  The actual crossed product and KMS action are
not asserted here.
-/
structure EquivariantCuntzP6m (p : ℕ) [Fact (Nat.Prime p)] where
  carrier : Type*
  boost : BoostParameter
  kmsScaling : ℝ → ℝ

/--
Symbolic K₀ carrier for the equivariant boost layer.

For `p = 3`, the current graph records three `ZMod 2` parity labels and two
integer sectors.  For other primes, this closed symbolic layer records `ℤ`.
The boost parameter is intentionally unused.
-/
def K0EquivariantBoost
    (p : ℕ) [Fact (Nat.Prime p)] (_b : BoostParameter) : Type :=
  if p = 3 then
    (ZMod 2) × (ZMod 2) × (ZMod 2) × ℤ × ℤ
  else
    ℤ

/--
Closed symbolic boost-invariance of the K₀ carrier.

This is definitional because `K0EquivariantBoost` does not depend on the
rapidity value.  The analytic statement that an actual equivariant K-theory
class is invariant under a continuous KMS/Lorentz homotopy is not proved here.
-/
theorem equivariant_lorentz_boost_signature
    (p : ℕ) [Fact (Nat.Prime p)] (b : BoostParameter) :
    K0EquivariantBoost p b = K0EquivariantBoost p zeroBoost := by
  rfl

/--
Closed kernel for the thermodynamic Lorentz layer.

This theorem is deliberately assembled from already-existing checked kernels:
thermal zero-boost bookkeeping, the finite K-theory/Chern counter, the BKB
fold/parity layer, the Dirac-Cuntz dispersion layer, and the Dikin
core/harmonic-null bridge.  No analytic crossed-product or KMS claim is hidden
inside the Lean kernel.
-/
theorem closed_thermodynamic_lorentz_boost_kernel
    (X : ThermalBoostLorentzSuperalgebra.ScreenCoord)
    (ℏ K vF kx ky ε : ℝ) (A : ℂ)
    (k : NonAbelianBrillouinKleinBottle.MomentumPoint)
    (ψ : TopologicalAndreevPump.ParafermionLane)
    (opK : ℝ) (v : Carrier → ℝ) :
    ThermalBoostLorentzSuperalgebra.lorentzBoost 0 X = X ∧
    ThermalBoostLorentzSuperalgebra.gammaOfRapidity 0 = 1 ∧
    ThermalBoostLorentzSuperalgebra.qOfRapidity ℏ 0 = 1 ∧
    ThermalBoostLorentzSuperalgebra.safeDispersionFactor 0 = 1 ∧
    modularFlow K 0 A = A ∧
    CuntzP6MWallpaperBoundary.sectorArity
      CuntzP6MWallpaperBoundary.PrimeSector.p3 = 3 ∧
    KTheoryChernConfinementSignature.cuntzK0Modulus 3 = 2 ∧
    KTheoryChernConfinementSignature.fixedOrbitCountP6M = 3 ∧
    KTheoryChernConfinementSignature.blochFreeRank = 2 ∧
    KTheoryChernConfinementSignature.crossedProductK1Rank = 2 ∧
    KTheoryChernConfinementSignature.jonesIndexD6 = 12 ∧
    KTheoryChernConfinementSignature.chernParity 0 = false ∧
    NonAbelianBrillouinKleinBottle.bkbFold
      (NonAbelianBrillouinKleinBottle.bkbFold k) = k ∧
    NonAbelianBrillouinKleinBottle.bkbChernNumber = 0 ∧
    NonAbelianBrillouinKleinBottle.kleinParityInvariant true = true ∧
    NonAbelianBrillouinKleinBottle.bkbLaneTransition
      (NonAbelianBrillouinKleinBottle.bkbLaneTransition ψ) = ψ ∧
    DiracCuntzCrystalDispersion.masslessDiracCuntzEnergySq vF kx ky 0 =
      vF^2 * DiracCuntzCrystalDispersion.kNormSq kx ky ∧
    dikinCoreQuadratic v =
      dikinCoreQuadratic (corePart v) ∧
    dikinCoreQuadratic (harmonicPart v) = 0 ∧
    SouriauOperatorThermodynamics.OperatorSouriauSystem.goutevTonevUnit
      (A := ℝ) ε opK =
      ((ε ^ 2 / 2 : ℝ) : ℝ) • (opK * opK) := by
  constructor
  · exact ThermalBoostLorentzSuperalgebra.lorentzBoost_zero X
  constructor
  · exact ThermalBoostLorentzSuperalgebra.gamma_zero
  constructor
  · exact ThermalBoostLorentzSuperalgebra.qOfRapidity_zero ℏ
  constructor
  · exact ThermalBoostLorentzSuperalgebra.safeDispersionFactor_zero
  constructor
  · exact BuresInformationGeodesicFlow.modularFlow_zero_time K A
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact KTheoryChernConfinementSignature.chernParity_zero
  constructor
  · exact NonAbelianBrillouinKleinBottle.bkbFold_involutive k
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact NonAbelianBrillouinKleinBottle.bkbLaneTransition_involutive ψ
  constructor
  · exact DiracCuntzCrystalDispersion.masslessDiracCuntzEnergySq_zero_rapidity vF kx ky
  constructor
  · exact DikinGoutevTonevBridge.dikinCoreQuadratic_corePart v
  constructor
  · exact DikinGoutevTonevBridge.dikinCoreQuadratic_harmonicPart_zero v
  · exact DikinGoutevTonevBridge.goutevTonevUnit_eq ε opK

#check closed_thermodynamic_lorentz_boost_kernel

end ThermodynamicLorentzBoost

end noncomputable section
