import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding
import InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
import InfoGeometry.Exceptional.RealSplitAlbertFreudenthal

/-!
# Algebraic soldering transport for the split-Albert derivation lane

The relevant abstraction is not a bare vector-space identification.  A
`soldering` must intertwine the two Jordan products.  Once that is available,
Leibniz derivations transport formally across the linear equivalence.
-/

noncomputable section

namespace InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport

open InfoGeometry.Algebra
open InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
open InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding

/-- Generic transport of a Leibniz derivation through a product-preserving
linear equivalence.  No Jordan-specific identities are needed here: this is
pure algebraic soldering. -/
theorem derivation_transport
    {A J : Type*}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup J] [Module ℝ J]
    (mulA : A → A → A) (mulJ : J → J → J)
    (S : A ≃ₗ[ℝ] J)
    (hS : ∀ x y, S (mulA x y) = mulJ (S x) (S y))
    (D : Module.End ℝ A)
    (hD : ∀ x y,
      D (mulA x y) = mulA (D x) y + mulA x (D y)) :
    let Dh : Module.End ℝ J :=
      S.toLinearMap.comp (D.comp S.symm.toLinearMap)
    ∀ X Y,
      Dh (mulJ X Y) = mulJ (Dh X) Y + mulJ X (Dh Y) := by
  dsimp
  intro X Y
  let x : A := S.symm X
  let y : A := S.symm Y
  have hX : S x = X := S.apply_symm_apply X
  have hY : S y = Y := S.apply_symm_apply Y
  rw [← hX, ← hY]
  simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
  rw [← hS x y]
  simp only [LinearEquiv.symm_apply_apply]
  rw [hD, map_add, hS, hS]

/-- Linear map underlying the maintained real-Albert to `H3Zorn` carrier
alignment. -/
def realAlbertToH3Linear : RealAlbertMatrix →ₗ[ℝ] H3Zorn ℝ where
  toFun := toH3
  map_add' X Y := by
    simpa using toH3_add X Y
  map_smul' r X := by
    simpa using toH3_smul r X

/-- The carrier alignment is bijective because the repository already owns the
explicit inverse `fromH3`. -/
theorem realAlbertToH3Linear_bijective :
    Function.Bijective realAlbertToH3Linear := by
  constructor
  · intro X Y h
    exact equiv.injective h
  · intro Y
    exact ⟨fromH3 Y, equiv.apply_symm_apply Y⟩

/-- Algebraic soldering from explicit real Albert coordinates to the installed
native `H3Zorn` Jordan carrier. -/
noncomputable def h3Soldering : RealAlbertMatrix ≃ₗ[ℝ] H3Zorn ℝ :=
  LinearEquiv.ofBijective realAlbertToH3Linear realAlbertToH3Linear_bijective

@[simp] theorem h3Soldering_apply (X : RealAlbertMatrix) :
    h3Soldering X = toH3 X := rfl

/-- The crucial algebraic-soldering law: the maintained coordinate Jordan
product is transported exactly to the installed `H3Zorn` Jordan product. -/
theorem h3Soldering_jordan_intertwines (X Y : RealAlbertMatrix) :
    h3Soldering (RealAlbertMatrix.mul X Y) = h3Soldering X * h3Soldering Y := by
  rw [h3Soldering_apply, h3Soldering_apply, h3Soldering_apply]
  rw [InfoGeometry.Algebra.RealAlbertMatrix.toH3_mul]
  exact candidateJordanMul_eq_mul _ _

/-- Coordinate-side Jordan Leibniz predicate. -/
def CoordinateJordanDerivation (D : Module.End ℝ RealAlbertMatrix) : Prop :=
  ∀ X Y,
    D (RealAlbertMatrix.mul X Y) =
      RealAlbertMatrix.mul (D X) Y + RealAlbertMatrix.mul X (D Y)

/-- Transport an explicit-coordinate derivation into the installed native
`H3Zorn` product. -/
noncomputable def transportCoordinateEnd
    (D : Module.End ℝ RealAlbertMatrix) : Module.End ℝ (H3Zorn ℝ) :=
  h3Soldering.toLinearMap.comp (D.comp h3Soldering.symm.toLinearMap)

/-- Product preservation makes coordinate Leibniz transport formal. -/
theorem transportCoordinateEnd_is_H3_derivation
    (D : Module.End ℝ RealAlbertMatrix)
    (hD : CoordinateJordanDerivation D) :
    H3ZornJordanDerivation (transportCoordinateEnd D) := by
  exact derivation_transport
    RealAlbertMatrix.mul
    (fun X Y : H3Zorn ℝ => X * Y)
    h3Soldering
    h3Soldering_jordan_intertwines
    D hD

/-- If a coordinate action solders to the raw entrywise `G2` action, then its
coordinate Leibniz theorem immediately certifies the native H3 action. -/
theorem entrywise_compatible_of_coordinate_soldering
    (D : G2Derivation)
    (Dcoord : Module.End ℝ RealAlbertMatrix)
    (hcoord : CoordinateJordanDerivation Dcoord)
    (hsolder : transportCoordinateEnd Dcoord = liftG2End D) :
    EntrywiseJordanCompatible D := by
  rw [EntrywiseJordanCompatible, ← hsolder]
  exact transportCoordinateEnd_is_H3_derivation Dcoord hcoord

/-- Hence full entrywise `G2 -> F4` compatibility follows once every native
split-octonion derivation admits a coordinate-side soldered Leibniz action. -/
theorem entrywiseCompatibleG2_eq_top_of_algebraic_soldering
    (Dcoord : G2Derivation → Module.End ℝ RealAlbertMatrix)
    (hcoord : ∀ D, CoordinateJordanDerivation (Dcoord D))
    (hsolder : ∀ D, transportCoordinateEnd (Dcoord D) = liftG2End D) :
    entrywiseCompatibleG2 = ⊤ := by
  refine le_antisymm le_top ?_
  intro D hD
  exact entrywise_compatible_of_coordinate_soldering
    D (Dcoord D) (hcoord D) (hsolder D)

end InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport
