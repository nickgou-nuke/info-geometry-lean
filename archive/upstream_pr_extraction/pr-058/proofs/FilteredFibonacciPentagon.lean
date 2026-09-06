import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory

universe u v

noncomputable section

namespace FibAnyonFilteredColimit

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable {C : Type v} [Category.{v} C] [MonoidalCategory C]
variable [HasBinaryCoproducts C]

/-- Mac Lane's pentagon identity for four objects of a monoidal category. -/
def PentagonIdentity (W X Y Z : C) : Prop :=
((α_ W X Y).hom ▷ Z) ≫
(α_ W (X ⊗ Y) Z).hom ≫
(W ◁ (α_ X Y Z).hom) =
(α_ (W ⊗ X) Y Z).hom ≫
(α_ W X (Y ⊗ Z)).hom

/--
A Fibonacci anyon object obtained as a filtered colimit.

The field `fusion` expresses the Fibonacci fusion rule

`τ ⊗ τ ≅ 𝟙 ⨿ τ`

for `τ = colimit F`.
-/
structure FilteredFibonacciAnyon
(F : J ⥤ C) [HasColimit F] where
fusion :
colimit F ⊗ colimit F ≅
𝟙_ C ⨿ colimit F

/--
The associator on the filtered-colimit Fibonacci object satisfies the genuine
Mac Lane pentagon identity.
-/
theorem filtered_fibonacci_anyon_pentagon
(F : J ⥤ C) [HasColimit F]
(_anyon : FilteredFibonacciAnyon F) :
PentagonIdentity
(colimit F)
(colimit F)
(colimit F)
(colimit F) := by
simpa only [PentagonIdentity] using
(MonoidalCategory.pentagon
(colimit F)
(colimit F)
(colimit F)
(colimit F))

end FibAnyonFilteredColimit
