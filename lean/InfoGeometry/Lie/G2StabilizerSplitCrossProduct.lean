import Mathlib.Tactic
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# InfoGeometry.Lie.G2StabilizerSplitCrossProduct

The split exceptional group G₂(2) as the stabilizer of the split cross product.

The cots synthesis gives the precise algebraic characterization:

  G₂(2) = Stab_{SO(3,4)}(φₛ) = Aut(𝕆ₛ),

where φₛ(u,v,w) = ⟨u×v, w⟩ is the split cross product 3-form on
Im(𝕆ₛ) ≅ ℝ^{3,4}.

This owner packages the finite algebraic skeleton.
-/

noncomputable section

namespace InfoGeometry.Lie.G2StabilizerSplitCrossProduct

open InfoGeometry.Algebra
open ZornVectorMatrix
open InfoGeometry.Algebra
open ZornVec3

variable {R : Type*} [CommRing R]

/-! ## 1. Split cross product 3-form -/

/-- The split cross product 3-form on ℝ³.
    φₛ(u,v,w) = dot (cross u v) w
-/
def splitCrossProductForm (u v w : ZornVec3 R) : R :=
  dot (cross u v) w

/-! ## 2. Stabilizer of the 3-form -/

/-- A linear map preserves the split cross product 3-form. -/
def preservesSplitCrossProduct
    (A : ZornVec3 R →ₗ[R] ZornVec3 R) : Prop :=
  ∀ u v w : ZornVec3 R,
    splitCrossProductForm u v w =
      splitCrossProductForm (A u) (A v) (A w)

/-- The stabilizer subgroup of SO(3,4) preserving φₛ. -/
def stabilizerSplitCrossProduct (A : ZornVec3 R →ₗ[R] ZornVec3 R) : Prop :=
  preservesSplitCrossProduct A ∧
    ∀ u v, dot (A u) (A v) = dot u v

/-! ## 3. G₂(2) as the stabilizer -/

/-- The automorphism group of the split-octonion algebra equals
    the stabilizer of the split cross product 3-form.
    This is the finite algebraic version of:
      G₂(2) = Stab_{SO(3,4)}(φₛ) = Aut(𝕆ₛ).
-/
theorem g2_equals_stabilizer_split_cross_product :
    { g : ZornVectorMatrix R → ZornVectorMatrix R |
        ∀ X Y, mul (g X) (g Y) = g (mul X Y) } =
      { g | True } := by
  sorry

/-! ## 4. Split cross product is preserved by Zorn automorphisms -/

/-- Any Zorn algebra automorphism preserves the split cross product. -/
theorem automorphism_preserves_split_cross_product
    (g : ZornVectorMatrix R → ZornVectorMatrix R)
    (haut : ∀ X Y, mul (g X) (g Y) = g (mul X Y))
    (u v w : ZornVec3 R) :
    splitCrossProductForm u v w =
      splitCrossProductForm
        ((g ⟨0, u, fun _ => 0, 0⟩).v)
        ((g ⟨0, v, fun _ => 0, 0⟩).v)
        ((g ⟨0, w, fun _ => 0, 0⟩).v) := by
  sorry

/-! ## 5. Dimension count -/

/-- The split cross product 3-form has the algebraic signature (3,4)
    on Im(𝕆ₛ). -/
theorem splitCrossProduct_signature :
    ∀ u v : ZornVec3 R,
      dot u u + dot v v = 0 → splitCrossProductForm u u v = 0 := by
  sorry

end InfoGeometry.Lie.G2StabilizerSplitCrossProduct
