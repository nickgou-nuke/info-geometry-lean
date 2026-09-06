import InfoGeometry.Architecture.SymmetricSpace
import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Core.SymmetricLie

/-!
# Core Symmetric Spaces

Core façade for group-level symmetric-space and Cartan data.
-/

namespace InfoGeometry.Core

section GroupModel

variable {G : Type _} [Group G]

lemma cartanSymmetry_involutive
    (θ : InfoGeometry.Architecture.CartanInvolution G) (x y : G) :
    InfoGeometry.Architecture.cartanSymmetry θ x
      (InfoGeometry.Architecture.cartanSymmetry θ x y) = y :=
  InfoGeometry.Architecture.cartanSymmetry_involutive θ x y

lemma cartanSymmetry_fixpoint
    (θ : InfoGeometry.Architecture.CartanInvolution G) (x : G) :
    InfoGeometry.Architecture.cartanSymmetry θ x x = x :=
  InfoGeometry.Architecture.cartanSymmetry_fixpoint θ x

lemma cartanSymmetry_involutive_ofInvolutiveMulAut
    (θ : InfoGeometry.Architecture.InvolutiveMulAut G) (x y : G) :
    InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut θ x
      (InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut θ x y) = y :=
  InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut_involutive θ x y

lemma cartanSymmetry_fixpoint_ofInvolutiveMulAut
    (θ : InfoGeometry.Architecture.InvolutiveMulAut G) (x : G) :
    InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut θ x x = x :=
  InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut_fixpoint θ x

lemma symmetricPair_K_eq_fixedSubgroup
    (S : InfoGeometry.Architecture.SymmetricPair G) :
    S.K = InfoGeometry.Architecture.fixedSubgroup S.θ.toMulAut :=
  InfoGeometry.Architecture.SymmetricPair.K_eq_fixedSubgroup S

lemma symmetricPairOfInvolutiveMulAut_K_eq_fixedSubgroup
    (θ : InfoGeometry.Architecture.InvolutiveMulAut G) :
    (InfoGeometry.Architecture.symmetricPairOfInvolutiveMulAut θ).K
      = InfoGeometry.Architecture.fixedSubgroup θ.1 := by
  simpa using
    InfoGeometry.Architecture.SymmetricPair.K_eq_fixedSubgroup
      (InfoGeometry.Architecture.symmetricPairOfInvolutiveMulAut θ)

end GroupModel

end InfoGeometry.Core
