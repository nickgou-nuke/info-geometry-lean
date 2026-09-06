import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Tensor products and colimits in `ModuleCat`

The preservation instance follows the kernel-checked argument in Atlas,
`AlgebraicTopologyI/code/Section24.lean`: tensoring on the right is naturally
isomorphic, by the braiding, to tensoring on the left, which is a left adjoint
and therefore preserves colimits.

The comparison isomorphism and its formula on colimit injections are then the
native Mathlib constructions `preservesColimitIso` and
`ι_preservesColimitIso_inv`.
-/

noncomputable section

namespace InfoGeometry.Categorical

open CategoryTheory MonoidalCategory Limits

/-- Tensoring on the right with a fixed module preserves all colimits. -/
instance tensorRightPreservesColimits
    (R : Type*) [CommRing R] (M : ModuleCat R) :
    PreservesColimits ((tensoringRight (ModuleCat R)).obj M) := by
  change PreservesColimits (tensorRight M)
  exact preservesColimits_of_natIso
    (NatIso.ofComponents
      (fun X => (_root_.CategoryTheory.BraidedCategory.braiding M X))
      (fun {X Y} f =>
        _root_.CategoryTheory.BraidedCategory.braiding_naturality_right M f) :
      tensorLeft M ≅ tensorRight M)

/-- Tensor product with a fixed module commutes with an arbitrary existing
colimit in `ModuleCat`. -/
noncomputable def tensorColimitIso
    {R : Type*} [CommRing R]
    {J : Type*} [Category J]
    (F : J ⥤ ModuleCat R) (M : ModuleCat R)
    [HasColimit F]
    [PreservesColimit F ((tensoringRight (ModuleCat R)).obj M)]
    [HasColimit (F ⋙ (tensoringRight (ModuleCat R)).obj M)] :
    colimit (F ⋙ (tensoringRight (ModuleCat R)).obj M) ≅
      ((tensoringRight (ModuleCat R)).obj M).obj (CategoryTheory.Limits.colimit F) :=
  (preservesColimitIso
    ((tensoringRight (ModuleCat R)).obj M) F).symm

/-- The tensor-colimit comparison commutes with every canonical stage
injection. -/
@[reassoc]
theorem tensorColimitIso_ι
    {R : Type*} [CommRing R]
    {J : Type*} [Category J]
    (F : J ⥤ ModuleCat R) (M : ModuleCat R)
    [HasColimit F]
    [PreservesColimit F ((tensoringRight (ModuleCat R)).obj M)]
    [HasColimit (F ⋙ (tensoringRight (ModuleCat R)).obj M)]
    (j : J) :
    colimit.ι (F ⋙ (tensoringRight (ModuleCat R)).obj M) j ≫
        (tensorColimitIso F M).hom =
      ((tensoringRight (ModuleCat R)).obj M).map
        (colimit.ι F j) :=
  ι_preservesColimitIso_inv
    ((tensoringRight (ModuleCat R)).obj M) F j

end InfoGeometry.Categorical
