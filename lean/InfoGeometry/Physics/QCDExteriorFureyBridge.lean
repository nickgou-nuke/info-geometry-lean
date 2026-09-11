import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
import InfoGeometry.Physics.ColorCARStandardModel

/-!
# Exterior/Furey three-mode bridge

The repository's existing exterior restriction maps the three positive-Witt
basis generators into `2 • chiralPlus55 i`.  The Furey-style generation owner
uses the opposite `chiralMinus55` convention for its creation operators, so
this module routes the exterior image into the explicitly separated conjugate
Furey span instead of silently identifying the two chiral conventions.

No minimal-left-ideal or physical particle interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDExteriorFureyBridge

open InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
open InfoGeometry.Physics.ColorCARStandardModel
open InfoGeometry.Clifford.Clifford55

/-- Every basis generator of the three-mode exterior carrier maps into the
conjugate Furey span on the native `Cl(5,5)` carrier. -/
theorem exterior_basis_generator_mem_fureyConjugateGeneration (i : Fin 3) :
    exterior3ToCl55Carrier (ExteriorAlgebra.ι ℝ (basisVector3 i)) ∈
      (fureyConjugateGeneration : Submodule ℝ Cl55) := by
  rw [exterior3ToCl55Carrier_basis_generator]
  exact Submodule.smul_mem _ _ (carAnn_mem_fureyConjugateGeneration i)

/-- The exterior restriction is injective and its three basis generators land
in the conjugate Furey span. -/
theorem exterior_furey_conjugate_packet :
    Function.Injective exterior3ToCl55Carrier ∧
      (∀ i : Fin 3,
        exterior3ToCl55Carrier (ExteriorAlgebra.ι ℝ (basisVector3 i)) ∈
          (fureyConjugateGeneration : Submodule ℝ Cl55)) :=
  ⟨exterior3ToCl55Carrier_injective,
    exterior_basis_generator_mem_fureyConjugateGeneration⟩

end InfoGeometry.Physics.QCDExteriorFureyBridge

end noncomputable section
