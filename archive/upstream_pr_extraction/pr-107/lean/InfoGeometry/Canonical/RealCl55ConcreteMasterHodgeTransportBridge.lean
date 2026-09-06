import Mathlib.Tactic
import InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
import InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge

/-!
# Conditional native transport to the fixed Cl(5,5) Hodge matrix

The master Hodge matrix and the concrete doubled Hestenes Dirac matrix are
defined through independent finite bases.  Given the explicit compatibility
hypothesis equating those matrices, this owner transports the master action to
the native Euclidean carrier on the embedded Hestenes image.  The hypothesis
is retained in the theorem statement; no basis identification is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55ConcreteMasterHodgeTransportBridge

open InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.HodgeFockEmbeddingBridge
open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

theorem masterHodgeNativeAction_intertwines_concrete
    (v : V3) (φ : Module.Dual ℝ V3)
    (hD : dirac32 (transportedConcreteDiracMatrix v φ) =
      masterHodgeDiracFin32) (x : DoubledExterior3) :
    nativeCoordinateAction masterHodgeDiracFin32
        (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteDirac3 v φ x) := by
  rw [nativeConcreteHestenesEmbedding_apply,
    nativeCoordinateAction_on_coordinate]
  have h := concreteDoubledDirac_to_fixed_master_hodge_intertwine
    v φ hD x
  simpa using congrArg coordinateToNative h

theorem nativeMasterHodgeDirac_intertwines_concrete
    (v : V3) (φ : Module.Dual ℝ V3)
    (hD : dirac32 (transportedConcreteDiracMatrix v φ) =
      masterHodgeDiracFin32) (x : DoubledExterior3) :
    nativeMasterHodgeDirac
        (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteDirac3 v φ x) := by
  simpa [nativeMasterHodgeDirac] using
    masterHodgeNativeAction_intertwines_concrete v φ hD x

end InfoGeometry.Canonical.RealCl55ConcreteMasterHodgeTransportBridge
