import Mathlib
import InfoGeometry.Categorical.CategoricalZetaMobius
import Omega.Zeta.XiChainInteriorBooleanFlagClosedForm

namespace InfoGeometry.Categorical.CategoricalZetaMobiusInversion

open Omega.Zeta
open InfoGeometry.Categorical.CategoricalZetaMobius

/--
Theorem: The Category-theoretic Möbius inversion holds for the 2-dimensional
boolean poset category (representing the two isotopic coordinates of the boundary package).
Specifically, the product of the Zeta operator and the Möbius operator is the Kronecker delta.
-/
theorem category_mobius_inversion_bool :
    ∀ X Z : Finset (Fin 2),
      (∑ Y : Finset (Fin 2), (if X ⊆ Y then (1 : ℤ) else 0) * booleanIntervalSign Y Z) =
        if X = Z then 1 else 0 := by
  decide

end InfoGeometry.Categorical.CategoricalZetaMobiusInversion
