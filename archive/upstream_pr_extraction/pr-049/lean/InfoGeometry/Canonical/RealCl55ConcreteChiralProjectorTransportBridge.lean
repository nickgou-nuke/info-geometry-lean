import Mathlib
import InfoGeometry.Canonical.Cl55MasterCoordinateChiralBlockBridge
import InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

/-!
# Conditional transport of the master chiral projectors

The master `Fin 32` chiral projectors and the concrete doubled Hestenes
chirality are defined through separate finite bases.  This owner transports
the projector action to the native embedded image under an explicit
chirality-compatibility hypothesis.  It does not infer that compatibility
from the already available Hodge--Dirac compatibility.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55ConcreteChiralProjectorTransportBridge

open InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateChiralBlockBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.HodgeFockEmbeddingBridge
open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

def concreteChiralProjectorPlus : DoubledExterior3End :=
  (1 / 2 : ℝ) • (1 + concreteChirality3)

def concreteChiralProjectorMinus : DoubledExterior3End :=
  (1 / 2 : ℝ) • (1 - concreteChirality3)

theorem masterChiralProjectorPlusFin32_action_intertwines
    (x : DoubledExterior3)
    (hΓ : Matrix.mulVec masterChiralityFin32
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding
        (exteriorToSpinor8 (concreteChirality3 x).1,
          exteriorToSpinor8 (concreteChirality3 x).2)) :
    Matrix.mulVec masterChiralProjectorPlusFin32
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding
        (exteriorToSpinor8 (concreteChiralProjectorPlus x).1,
          exteriorToSpinor8 (concreteChiralProjectorPlus x).2) := by
  have hp : masterChiralProjectorPlusFin32 =
      (1 / 2 : ℝ) • (1 + masterChiralityFin32) := by
    simp [masterChiralProjectorPlusFin32, masterChiralProjectorPlus,
      masterChiralityFin32, map_smul, map_add, map_one]
  rw [hp]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hΓ]
  simp [concreteChiralProjectorPlus, doubledFockEmbedding,
    doubledDiagonal, exteriorToSpinor8]
  module

theorem masterChiralProjectorMinusFin32_action_intertwines
    (x : DoubledExterior3)
    (hΓ : Matrix.mulVec masterChiralityFin32
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding
        (exteriorToSpinor8 (concreteChirality3 x).1,
          exteriorToSpinor8 (concreteChirality3 x).2)) :
    Matrix.mulVec masterChiralProjectorMinusFin32
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding
        (exteriorToSpinor8 (concreteChiralProjectorMinus x).1,
          exteriorToSpinor8 (concreteChiralProjectorMinus x).2) := by
  have hm : masterChiralProjectorMinusFin32 =
      (1 / 2 : ℝ) • (1 - masterChiralityFin32) := by
    simp [masterChiralProjectorMinusFin32, masterChiralProjectorMinus,
      masterChiralityFin32, map_smul, map_sub, map_one]
  rw [hm]
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hΓ]
  simp [concreteChiralProjectorMinus, doubledFockEmbedding,
    doubledDiagonal, exteriorToSpinor8]
  module

theorem nativeMasterChiralProjectorPlus_action_intertwines
    (x : DoubledExterior3)
    (hΓ : Matrix.mulVec masterChiralityFin32
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding
        (exteriorToSpinor8 (concreteChirality3 x).1,
          exteriorToSpinor8 (concreteChirality3 x).2)) :
    nativeCoordinateAction masterChiralProjectorPlusFin32
        (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteChiralProjectorPlus x) := by
  rw [nativeConcreteHestenesEmbedding_apply,
    nativeCoordinateAction_on_coordinate]
  exact congrArg coordinateToNative
    (masterChiralProjectorPlusFin32_action_intertwines x hΓ)

theorem nativeMasterChiralProjectorMinus_action_intertwines
    (x : DoubledExterior3)
    (hΓ : Matrix.mulVec masterChiralityFin32
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding
        (exteriorToSpinor8 (concreteChirality3 x).1,
          exteriorToSpinor8 (concreteChirality3 x).2)) :
    nativeCoordinateAction masterChiralProjectorMinusFin32
        (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteChiralProjectorMinus x) := by
  rw [nativeConcreteHestenesEmbedding_apply,
    nativeCoordinateAction_on_coordinate]
  exact congrArg coordinateToNative
    (masterChiralProjectorMinusFin32_action_intertwines x hΓ)

end InfoGeometry.Canonical.RealCl55ConcreteChiralProjectorTransportBridge
