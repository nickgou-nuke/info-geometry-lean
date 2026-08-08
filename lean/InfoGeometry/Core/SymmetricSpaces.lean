import InfoGeometry.Architecture.SymmetricSpace

/-!
# Core Symmetric Spaces

Core façade for symmetric-space and Cartan data.

This file is intentionally group-level:
- abstract symmetric spaces;
- Cartan involutions and fixed subgroups;
- canonical symmetric pairs;
- canonical symmetric-space structures induced by involutions.
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

section SpaceModel

variable {M : Type _}

/-- Core alias for point symmetry in a symmetric space. -/
abbrev symmetry (S : InfoGeometry.Architecture.SymmetricSpace M) (x y : M) : M :=
  S.symmetry x y

export InfoGeometry.Architecture
  (symmetry_symmetry
   symmetry_self)

lemma symmetry_involutive
    (S : InfoGeometry.Architecture.SymmetricSpace M) (x y : M) :
    symmetry S x (symmetry S x y) = y :=
  symmetry_symmetry S x y

lemma symmetry_fixpoint
    (S : InfoGeometry.Architecture.SymmetricSpace M) (x : M) :
    symmetry S x x = x :=
  symmetry_self S x

end SpaceModel

section GroupModel

variable {G : Type _} [Group G]

/-- Build a core Cartan involution from an involutive group automorphism. -/
abbrev cartanInvolutionOfMulAutInvolution
    (θ : MulAut G) (hθ : Function.Involutive θ) :
    CartanInvolution G :=
  InfoGeometry.Architecture.CartanInvolution.ofMulAutInvolution θ hθ

/-- Forget a Cartan involution to the canonical subtype of involutive automorphisms. -/
abbrev CartanInvolution.toInvolutiveMulAut
    (θ : CartanInvolution G) :
    InvolutiveMulAut G :=
  InfoGeometry.Architecture.CartanInvolution.toInvolutiveMulAut θ

/-- Core alias for fixed-point subgroup of a group automorphism. -/
abbrev fixedSubgroup (θ : MulAut G) : Subgroup G :=
  InfoGeometry.Architecture.fixedSubgroup θ

/-- Fixed-point subgroup attached to a Cartan involution. -/
abbrev CartanInvolution.fixedSubgroup
    (θ : CartanInvolution G) : Subgroup G :=
  InfoGeometry.Architecture.CartanInvolution.fixedSubgroup θ

/-- Core alias for Cartan group-model point symmetry. -/
abbrev cartanSymmetry (θ : CartanInvolution G) (x y : G) : G :=
  InfoGeometry.Architecture.cartanSymmetry θ x y

/-- Core alias for point symmetry induced by an involutive `MulAut` subtype. -/
abbrev cartanSymmetryOfInvolutiveMulAut
    (θ : InvolutiveMulAut G) (x y : G) : G :=
  InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut θ x y

/-- Core alias for the canonical symmetric pair induced by an involution property. -/
abbrev symmetricPairOfInvolution
    (θ : MulAut G) (hθ : Function.Involutive θ) : SymmetricPair G :=
  InfoGeometry.Architecture.symmetricPairOfInvolution θ hθ

/-- Core alias for the canonical symmetric pair induced by an involutive `MulAut` subtype. -/
abbrev symmetricPairOfInvolutiveMulAut (θ : InvolutiveMulAut G) : SymmetricPair G :=
  InfoGeometry.Architecture.symmetricPairOfInvolutiveMulAut θ

/-- Canonical symmetric pair induced by a Cartan involution. -/
abbrev symmetricPairOfCartan
    (θ : CartanInvolution G) : SymmetricPair G :=
  symmetricPairOfInvolution θ.toMulAut θ.involutive

/-- Canonical symmetric space induced by a Cartan involution. -/
abbrev symmetricSpaceOfCartan
    (θ : CartanInvolution G) : InfoGeometry.Architecture.SymmetricSpace G :=
  InfoGeometry.Architecture.symmetricSpaceOfCartan θ

/-- Canonical symmetric space induced by an involutive `MulAut` subtype. -/
abbrev symmetricSpaceOfInvolutiveMulAut
    (θ : InvolutiveMulAut G) : InfoGeometry.Architecture.SymmetricSpace G :=
  InfoGeometry.Architecture.symmetricSpaceOfInvolutiveMulAut θ

export InfoGeometry.Architecture
  (mem_fixedSubgroup_iff
   cartanSymmetry_involutive
   cartanSymmetry_fixpoint
   cartanSymmetryOfInvolutiveMulAut_involutive
   cartanSymmetryOfInvolutiveMulAut_fixpoint)

export InfoGeometry.Architecture.SymmetricPair (K_eq_fixedSubgroup)

@[simp] lemma CartanInvolution.toInvolutiveMulAut_val
    (θ : CartanInvolution G) :
    θ.toInvolutiveMulAut.1 = θ.toMulAut :=
  rfl

@[simp] lemma mem_fixedSubgroup_of_cartan_iff
    (θ : CartanInvolution G) (g : G) :
    g ∈ θ.fixedSubgroup ↔ θ.toMulAut g = g := by
  simp [CartanInvolution.fixedSubgroup]

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

lemma symmetricPairOfCartan_K_eq_fixedSubgroup
    (θ : CartanInvolution G) :
    (symmetricPairOfCartan θ).K = θ.fixedSubgroup := by
  simpa [symmetricPairOfCartan, CartanInvolution.fixedSubgroup, symmetricPairOfInvolution, fixedSubgroup] using
    K_eq_fixedSubgroup (symmetricPairOfCartan θ)

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

@[simp] lemma symmetricSpaceOfCartan_symmetry
    (θ : CartanInvolution G) (x y : G) :
    (symmetricSpaceOfCartan θ).symmetry x y = cartanSymmetry θ x y :=
  rfl

@[simp] lemma symmetricSpaceOfInvolutiveMulAut_symmetry
    (θ : InvolutiveMulAut G) (x y : G) :
    (symmetricSpaceOfInvolutiveMulAut θ).symmetry x y =
      cartanSymmetryOfInvolutiveMulAut θ x y :=
  rfl

lemma symmetricSpaceOfCartan_involutive
    (θ : CartanInvolution G) (x y : G) :
    (symmetricSpaceOfCartan θ).symmetry x
      ((symmetricSpaceOfCartan θ).symmetry x y) = y :=
  cartanSymmetry_involutive θ x y

lemma symmetricSpaceOfCartan_fixpoint
    (θ : CartanInvolution G) (x : G) :
    (symmetricSpaceOfCartan θ).symmetry x x = x :=
  cartanSymmetry_fixpoint θ x

end GroupModel

end InfoGeometry.Core
