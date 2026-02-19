import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Symmetric Space Architecture

Core Cartan-Loos style abstractions for symmetric spaces.
-/

namespace InfoGeometry.Architecture

/-- A minimal Cartan-Loos symmetric space structure. -/
structure SymmetricSpace (M : Type _) where
  /-- Point-reflection at `x`, applied to `y`. -/
  symmetry : M → M → M
  /-- Each point-reflection is an involution. -/
  symm_involutive : ∀ x y, symmetry x (symmetry x y) = y
  /-- The center point is fixed by its own reflection. -/
  symm_fixpoint : ∀ x, symmetry x x = x

@[simp]
lemma symmetry_symmetry
    {M : Type _}
    (S : SymmetricSpace M) (x y : M) :
    S.symmetry x (S.symmetry x y) = y :=
  S.symm_involutive x y

@[simp]
lemma symmetry_self
    {M : Type _}
    (S : SymmetricSpace M) (x : M) :
    S.symmetry x x = x :=
  S.symm_fixpoint x

/-- A Cartan involution modeled as an involutive group automorphism. -/
structure CartanInvolution (G : Type _) [Group G] where
  toMulAut : MulAut G
  involutive : ∀ g, toMulAut (toMulAut g) = g

attribute [simp] CartanInvolution.involutive

/-- A symmetric pair `(G, K)` with fixed-point subgroup `K = Fix(θ)`. -/
structure SymmetricPair (G : Type _) [Group G] where
  θ : CartanInvolution G
  K : Subgroup G
  fix_eq : ∀ g, g ∈ K ↔ θ.toMulAut g = g

section CanonicalGroup

variable {G : Type _} [Group G]

/-- Involutive elements of `MulAut G` (`θ ∘ θ = id`) as a subtype. -/
abbrev InvolutiveMulAut (G : Type _) [Group G] :=
  { θ : MulAut G // Function.Involutive θ }

/-- Build a `CartanInvolution` from a `MulAut` involution witness. -/
def CartanInvolution.ofMulAutInvolution
    (θ : MulAut G) (hθ : Function.Involutive θ) :
    CartanInvolution G where
  toMulAut := θ
  involutive := hθ

/-- Forget a `CartanInvolution` to the canonical subtype of involutive `MulAut`s. -/
def CartanInvolution.toInvolutiveMulAut
    (θ : CartanInvolution G) :
    InvolutiveMulAut G :=
  ⟨θ.toMulAut, θ.involutive⟩

/-- Fixed-point subgroup of an automorphism. -/
def fixedSubgroup (θ : MulAut G) : Subgroup G where
  carrier := { g : G | θ g = g }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : θ a = a := by simpa using ha
    have hb' : θ b = b := by simpa using hb
    simp [ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : θ a = a := by simpa using ha
    calc
      θ a⁻¹ = (θ a)⁻¹ := by simp
      _ = a⁻¹ := by simp [ha']

@[simp] lemma mem_fixedSubgroup_iff (θ : MulAut G) (g : G) :
    g ∈ fixedSubgroup θ ↔ θ g = g :=
  Iff.rfl

/-- Fixed-point subgroup attached to a Cartan involution. -/
def CartanInvolution.fixedSubgroup (θ : CartanInvolution G) : Subgroup G :=
  InfoGeometry.Architecture.fixedSubgroup θ.toMulAut

@[simp] lemma CartanInvolution.mem_fixedSubgroup_iff
    (θ : CartanInvolution G) (g : G) :
    g ∈ θ.fixedSubgroup ↔ θ.toMulAut g = g :=
  by
    simp [CartanInvolution.fixedSubgroup, fixedSubgroup]

/-- Canonical symmetric pair attached to an involutive `MulAut`. -/
def symmetricPairOfInvolution
    (θ : MulAut G) (hθ : Function.Involutive θ) :
    SymmetricPair G where
  θ := CartanInvolution.ofMulAutInvolution θ hθ
  K := fixedSubgroup θ
  fix_eq := by
    intro g
    rfl

/-- Canonical symmetric pair attached to a subtype value of involutive `MulAut`. -/
def symmetricPairOfInvolutiveMulAut
    (θ : InvolutiveMulAut G) :
    SymmetricPair G :=
  symmetricPairOfInvolution θ.1 θ.2

/-- Any symmetric pair has its subgroup equal to the fixed subgroup of its involution. -/
lemma SymmetricPair.K_eq_fixedSubgroup (S : SymmetricPair G) :
    S.K = fixedSubgroup S.θ.toMulAut := by
  ext g
  exact S.fix_eq g

end CanonicalGroup

section GroupModel

variable {G : Type _} [Group G]

/-- Group-model point reflection induced by a Cartan involution. -/
def cartanSymmetry
    (θ : CartanInvolution G) (x y : G) : G :=
  x * θ.toMulAut (x⁻¹ * y)

lemma cartanSymmetry_involutive
    (θ : CartanInvolution G) (x y : G) :
    cartanSymmetry θ x (cartanSymmetry θ x y) = y := by
  unfold cartanSymmetry
  calc
    x * θ.toMulAut (x⁻¹ * (x * θ.toMulAut (x⁻¹ * y)))
        = x * θ.toMulAut ((x⁻¹ * x) * θ.toMulAut (x⁻¹ * y)) := by
            simp
    _ = x * θ.toMulAut (θ.toMulAut (x⁻¹ * y)) := by simp
    _ = x * (x⁻¹ * y) := by simp
    _ = y := by simp

lemma cartanSymmetry_fixpoint
    (θ : CartanInvolution G) (x : G) :
    cartanSymmetry θ x x = x := by
  unfold cartanSymmetry
  simp

/-- Group-model point reflection induced directly by an involutive `MulAut` subtype. -/
def cartanSymmetryOfInvolutiveMulAut
    (θ : InvolutiveMulAut G) (x y : G) : G :=
  cartanSymmetry (CartanInvolution.ofMulAutInvolution θ.1 θ.2) x y

lemma cartanSymmetryOfInvolutiveMulAut_involutive
    (θ : InvolutiveMulAut G) (x y : G) :
    cartanSymmetryOfInvolutiveMulAut θ x
      (cartanSymmetryOfInvolutiveMulAut θ x y) = y := by
  simpa [cartanSymmetryOfInvolutiveMulAut] using
    cartanSymmetry_involutive
      (CartanInvolution.ofMulAutInvolution θ.1 θ.2) x y

lemma cartanSymmetryOfInvolutiveMulAut_fixpoint
    (θ : InvolutiveMulAut G) (x : G) :
    cartanSymmetryOfInvolutiveMulAut θ x x = x := by
  simpa [cartanSymmetryOfInvolutiveMulAut] using
    cartanSymmetry_fixpoint
      (CartanInvolution.ofMulAutInvolution θ.1 θ.2) x

/-- Symmetric space canonically induced by a Cartan involution. -/
def symmetricSpaceOfCartan
    (θ : CartanInvolution G) : SymmetricSpace G where
  symmetry := cartanSymmetry θ
  symm_involutive := cartanSymmetry_involutive θ
  symm_fixpoint := cartanSymmetry_fixpoint θ

/-- Symmetric space canonically induced by an involutive `MulAut` subtype. -/
def symmetricSpaceOfInvolutiveMulAut
    (θ : InvolutiveMulAut G) : SymmetricSpace G where
  symmetry := cartanSymmetryOfInvolutiveMulAut θ
  symm_involutive := cartanSymmetryOfInvolutiveMulAut_involutive θ
  symm_fixpoint := cartanSymmetryOfInvolutiveMulAut_fixpoint θ

end GroupModel

end InfoGeometry.Architecture
