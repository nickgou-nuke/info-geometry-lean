import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

universe u v

noncomputable section

namespace FibAnyonFilteredColimit

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable {C : Type v} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C] [HasBinaryCoproducts C]

/--
A filtered-colimit Fibonacci anyon equipped with the canonical braiding inherited
from the ambient braided monoidal category.
-/
structure FilteredFibonacciAnyon (F : J ⥤ C) [HasColimit F] where
  fusion : colimit F ⊗ colimit F ≅ 𝟙_ C ⨿ colimit F

structure BraidedFilteredFibonacciAnyon
(F : J ⥤ C) [HasColimit F]
extends FilteredFibonacciAnyon F where
braid :
colimit F ⊗ colimit F ≅
colimit F ⊗ colimit F
braid_eq :
braid = β_ (colimit F) (colimit F)

/-- The forward braided hexagon identity. -/
def ForwardHexagonIdentity (X Y Z : C) : Prop :=
(α_ X Y Z).hom ≫
(β_ X (Y ⊗ Z)).hom ≫
(α_ Y Z X).hom =
((β_ X Y).hom ▷ Z) ≫
(α_ Y X Z).hom ≫
(Y ◁ (β_ X Z).hom)

/-- The reverse braided hexagon identity. -/
def ReverseHexagonIdentity (X Y Z : C) : Prop :=
(α_ X Y Z).inv ≫
(β_ (X ⊗ Y) Z).hom ≫
(α_ Z X Y).inv =
(X ◁ (β_ Y Z).hom) ≫
(α_ X Z Y).inv ≫
((β_ X Z).hom ▷ Y)

/--
The canonical braiding on the filtered-colimit Fibonacci object satisfies the
forward hexagon identity.
-/
theorem filtered_fibonacci_anyon_forward_hexagon
(F : J ⥤ C) [HasColimit F]
(_anyon : BraidedFilteredFibonacciAnyon F) :
ForwardHexagonIdentity
(colimit F)
(colimit F)
(colimit F) := by
simpa only [ForwardHexagonIdentity] using
(BraidedCategory.hexagon_forward
(colimit F)
(colimit F)
(colimit F))

/--
The canonical braiding on the filtered-colimit Fibonacci object satisfies the
reverse hexagon identity.
-/
theorem filtered_fibonacci_anyon_reverse_hexagon
(F : J ⥤ C) [HasColimit F]
(_anyon : BraidedFilteredFibonacciAnyon F) :
ReverseHexagonIdentity
(colimit F)
(colimit F)
(colimit F) := by
simpa only [ReverseHexagonIdentity] using
(BraidedCategory.hexagon_reverse
(colimit F)
(colimit F)
(colimit F))

/-- The right-associated three-anyon fusion object. -/
def fibonacciTripleTensor
(F : J ⥤ C) [HasColimit F] : C :=
colimit F ⊗ (colimit F ⊗ colimit F)

/--
The first Artin generator on three filtered-colimit Fibonacci anyons.

It braids the first two tensor factors and transports the result to the chosen
right-associated parenthesization.
-/
def braidGeneratorOne
{F : J ⥤ C} [HasColimit F]
(anyon : BraidedFilteredFibonacciAnyon F) :
fibonacciTripleTensor F ≅ fibonacciTripleTensor F :=
(α_ (colimit F) (colimit F) (colimit F)).symm ≪≫
whiskerRightIso anyon.braid (colimit F) ≪≫
α_ (colimit F) (colimit F) (colimit F)

/--
The second Artin generator on three filtered-colimit Fibonacci anyons.
-/
def braidGeneratorTwo
{F : J ⥤ C} [HasColimit F]
(anyon : BraidedFilteredFibonacciAnyon F) :
fibonacciTripleTensor F ≅ fibonacciTripleTensor F :=
whiskerLeftIso (colimit F) anyon.braid

/--
Two automorphisms satisfying the Artin presentation of the three-strand braid
group.
-/
structure BraidGroupThreeRepresentation (X : C) where
generatorOne : X ≅ X
generatorTwo : X ≅ X
artin_relation :
generatorOne ≪≫ generatorTwo ≪≫ generatorOne =
generatorTwo ≪≫ generatorOne ≪≫ generatorTwo

/--
The braiding on the filtered-colimit Fibonacci object satisfies the
three-strand Artin braid relation.
-/
theorem filtered_fibonacci_anyon_braid_relation
{F : J ⥤ C} [HasColimit F]
(anyon : BraidedFilteredFibonacciAnyon F) :
braidGeneratorOne anyon ≪≫
braidGeneratorTwo anyon ≪≫
braidGeneratorOne anyon =
braidGeneratorTwo anyon ≪≫
braidGeneratorOne anyon ≪≫
braidGeneratorTwo anyon := by
simpa only [
braidGeneratorOne,
braidGeneratorTwo,
anyon.braid_eq,
Iso.trans_assoc
] using
(BraidedCategory.yang_baxter_iso
(colimit F)
(colimit F)
(colimit F))

/--
The canonical three-strand braid-group representation carried by the
filtered-colimit Fibonacci anyon.
-/
def filteredFibonacciBraidGroupThreeRepresentation
{F : J ⥤ C} [HasColimit F]
(anyon : BraidedFilteredFibonacciAnyon F) :
BraidGroupThreeRepresentation (fibonacciTripleTensor F) where
generatorOne := braidGeneratorOne anyon
generatorTwo := braidGeneratorTwo anyon
artin_relation := filtered_fibonacci_anyon_braid_relation anyon

end FibAnyonFilteredColimit
