import Mathlib
import InfoGeometry.Topology.ChiralBasisChangeTopological
import InfoGeometry.Topology.SymbolicLatentSpace

/-!
# Native symbolic latent chart for the chiral soldering coordinates

The chiral coordinates and the native split-octonion coordinates are two
observational presentations of the same real eight-dimensional carrier.  This
owner records the native coordinate observables obtained by the verified
chiral-to-native homeomorphism.  It does not add a spinor representation or a
Clifford action.
-/

namespace InfoGeometry.Topology

noncomputable section

abbrev RealNativeBasisCoordinates := Fin 8 → ℝ

def realNativeCoefficientSystem :
    FiniteSymbolicLatentSystem RealNativeBasisCoordinates (Fin 8) :=
  fun i =>
    { toFun := fun d => realChiralToNative.symm d i
      continuous_toFun := continuous_apply i |>.comp realChiralToNative.symm.continuous }

@[simp] theorem realNativeCoefficientSystem_observationMap
  (d : RealNativeBasisCoordinates) :
    symbolicObservationMap realNativeCoefficientSystem d =
      realChiralToNative.symm d := by
  funext i
  rfl

theorem realNativeCoefficientSystem_isEmbedding :
    Topology.IsEmbedding
      (symbolicObservationMap realNativeCoefficientSystem) := by
  rw [show symbolicObservationMap realNativeCoefficientSystem =
      realChiralToNative.symm by
    funext d
    exact realNativeCoefficientSystem_observationMap d]
  exact realChiralToNative.symm.isEmbedding

def realNativeCoefficientChart :
    SymbolicLatentChart RealNativeBasisCoordinates (Fin 8) where
  system := realNativeCoefficientSystem
  isEmbedding := realNativeCoefficientSystem_isEmbedding

theorem realNativeCoefficientSystem_solutionSet_singleton
  (c : RealChiralBasisCoordinates) :
    realNativeCoefficientSystem.solutionSet c =
      ({realChiralToNative c} : Set RealNativeBasisCoordinates) := by
  ext d
  constructor
  · intro hc
    apply Set.mem_singleton_iff.mpr
    have hsymm : realChiralToNative.symm d = c := by
      funext i
      simpa [realNativeCoefficientSystem] using hc i
    calc
      d = realChiralToNative (realChiralToNative.symm d) :=
        (realChiralToNative.right_inv d).symm
      _ = realChiralToNative c := congrArg realChiralToNative hsymm
  · intro hc
    rw [Set.mem_singleton_iff.mp hc]
    intro i
    change realChiralToNative.symm (realChiralToNative c) i = c i
    exact congrFun (realChiralToNative.left_inv c) i

def chiralToNativeLatentMap :
    RealChiralBasisCoordinates → RealNativeBasisCoordinates :=
  realChiralToNative

def nativeToChiralLatentMap :
    RealNativeBasisCoordinates → RealChiralBasisCoordinates :=
  realChiralToNative.symm

theorem chiralToNative_latent_roundtrip (c : RealChiralBasisCoordinates) :
    nativeToChiralLatentMap (chiralToNativeLatentMap c) = c := by
  exact realChiralToNative.left_inv c

theorem nativeToChiral_latent_roundtrip (d : RealNativeBasisCoordinates) :
    chiralToNativeLatentMap (nativeToChiralLatentMap d) = d := by
  exact realChiralToNative.right_inv d

theorem chiralToNative_latent_observation_transport
    (c : RealChiralBasisCoordinates) :
    symbolicObservationMap realNativeCoefficientSystem
      (chiralToNativeLatentMap c) = c := by
  funext i
  change realChiralToNative.symm (realChiralToNative c) i = c i
  exact congrFun (realChiralToNative.left_inv c) i

end
end InfoGeometry.Topology
