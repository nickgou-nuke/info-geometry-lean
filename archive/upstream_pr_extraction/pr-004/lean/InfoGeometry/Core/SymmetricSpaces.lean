import InfoGeometry.Architecture.SymmetricSpace

/-!
# Core Symmetric Spaces

Core façade for group-level symmetric-space and Cartan data.
-/

namespace InfoGeometry.Core

/-- Core alias for group-level Cartan involutions. -/
abbrev CartanInvolution (G : Type _) [Group G] :=
  InfoGeometry.Architecture.CartanInvolution G

/-- Core alias for involutive group automorphisms as a subtype. -/
abbrev InvolutiveMulAut (G : Type _) [Group G] :=
  InfoGeometry.Architecture.InvolutiveMulAut G

/-- Core alias for symmetric pairs. -/
abbrev SymmetricPair (G : Type _) [Group G] :=
  InfoGeometry.Architecture.SymmetricPair G

section GroupModel

variable {G : Type _} [Group G]

/-- Core alias for fixed-point subgroup of a group automorphism. -/
abbrev fixedSubgroup (θ : MulAut G) : Subgroup G :=
  InfoGeometry.Architecture.fixedSubgroup θ

/-- Core alias for Cartan group-model point symmetry. -/
abbrev cartanSymmetry (θ : CartanInvolution G) (x y : G) : G :=
  InfoGeometry.Architecture.cartanSymmetry θ x y

/-- Core alias for point symmetry induced by an involutive `MulAut` subtype. -/
abbrev cartanSymmetryOfInvolutiveMulAut
    (θ : InvolutiveMulAut G) (x y : G) : G :=
  InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut θ x y

/-- Core alias for the canonical symmetric pair induced by an involutive `MulAut` subtype. -/
abbrev symmetricPairOfInvolutiveMulAut (θ : InvolutiveMulAut G) : SymmetricPair G :=
  InfoGeometry.Architecture.symmetricPairOfInvolutiveMulAut θ

export InfoGeometry.Architecture
  (cartanSymmetry_involutive
   cartanSymmetry_fixpoint
   cartanSymmetryOfInvolutiveMulAut_involutive
   cartanSymmetryOfInvolutiveMulAut_fixpoint)

export InfoGeometry.Architecture.SymmetricPair (K_eq_fixedSubgroup)

lemma cartanSymmetry_involutive_ofInvolutiveMulAut
    (θ : InvolutiveMulAut G) (x y : G) :
    cartanSymmetryOfInvolutiveMulAut θ x
      (cartanSymmetryOfInvolutiveMulAut θ x y) = y :=
  cartanSymmetryOfInvolutiveMulAut_involutive θ x y

lemma cartanSymmetry_fixpoint_ofInvolutiveMulAut
    (θ : InvolutiveMulAut G) (x : G) :
    cartanSymmetryOfInvolutiveMulAut θ x x = x :=
  cartanSymmetryOfInvolutiveMulAut_fixpoint θ x

lemma symmetricPair_K_eq_fixedSubgroup
    (S : SymmetricPair G) :
    S.K = fixedSubgroup S.θ.toMulAut :=
  K_eq_fixedSubgroup S

lemma symmetricPairOfInvolutiveMulAut_K_eq_fixed
    (θ : InvolutiveMulAut G) :
    (symmetricPairOfInvolutiveMulAut θ).K = fixedSubgroup θ.1 := by
  simpa [symmetricPairOfInvolutiveMulAut, fixedSubgroup] using
    K_eq_fixedSubgroup
      (InfoGeometry.Architecture.symmetricPairOfInvolutiveMulAut θ)

lemma symmetricPairOfInvolutiveMulAut_K_eq_fixedSubgroup
    (θ : InvolutiveMulAut G) :
    (symmetricPairOfInvolutiveMulAut θ).K = fixedSubgroup θ.1 :=
  symmetricPairOfInvolutiveMulAut_K_eq_fixed θ

end GroupModel

end InfoGeometry.Core
