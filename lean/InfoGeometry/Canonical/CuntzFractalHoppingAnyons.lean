import InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge

/-!
# InfoGeometry.Canonical.CuntzFractalHoppingAnyons

Thin bridge for the already owned three-branch Toeplitz--Cuntz hopping lane.
It reexports the explicit Artin generators on the native carrier and transports
their braid relation to `TopCat` via the existing continuous left-action bridge.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzFractalHoppingAnyons

open CategoryTheory
open InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid
open InfoGeometry.Canonical.NativeToeplitzCuntzThree
open InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

abbrev Carrier := InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid.Carrier

/-- First hopping generator on the native three-generator Toeplitz--Cuntz carrier. -/
def hoppingSigma1 : Carrier :=
  InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid.braidGenerator1

/-- Second hopping generator on the native three-generator Toeplitz--Cuntz carrier. -/
def hoppingSigma2 : Carrier :=
  InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid.braidGenerator2

/-- The native hopping generators satisfy the adjacent Artin braid relation. -/
theorem hopping_artin_relation :
  hoppingSigma1 * hoppingSigma2 * hoppingSigma1 =
      hoppingSigma2 * hoppingSigma1 * hoppingSigma2 := by
  simpa [hoppingSigma1, hoppingSigma2] using
    InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid.artin_braid_relation

/-- The Coxeter word is the already-owned cyclic supercharge plus the vacuum defect. -/
theorem hopping_coxeter_decomposition :
    InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid.coxeterElement =
      (generator (0 : Fin 3) * star (generator (1 : Fin 3)) +
        generator (1 : Fin 3) * star (generator (2 : Fin 3)) +
        generator (2 : Fin 3) * star (generator (0 : Fin 3))) + vacuumDefect := by
  simpa using
    InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid.coxeterElement_eq_cyclicSupercharge_add_defect

section Topological

variable {R : Type*} [Ring R] [StarRing R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (g : ToeplitzCuntzThreeGenerators R)

/-- Continuous left multiplication by the first hopping generator. -/
def hoppingSigma1TopCatHom : TopCat.of R ⟶ TopCat.of R :=
  braidGenerator1LeftTopCatHom g

/-- Continuous left multiplication by the second hopping generator. -/
def hoppingSigma2TopCatHom : TopCat.of R ⟶ TopCat.of R :=
  braidGenerator2LeftTopCatHom g

/-- The topological hopping generators satisfy the same Artin relation in `TopCat`. -/
theorem hopping_topCat_artin_relation :
    hoppingSigma1TopCatHom g ≫ hoppingSigma2TopCatHom g ≫ hoppingSigma1TopCatHom g =
      hoppingSigma2TopCatHom g ≫ hoppingSigma1TopCatHom g ≫ hoppingSigma2TopCatHom g := by
  simpa [hoppingSigma1TopCatHom, hoppingSigma2TopCatHom] using
    braidGenerator_left_artin_relation g

/-- The two continuous hopping maps are involutive. -/
theorem hopping_topCat_involutive :
    hoppingSigma1TopCatHom g ≫ hoppingSigma1TopCatHom g =
      𝟙 (TopCat.of R) ∧
    hoppingSigma2TopCatHom g ≫ hoppingSigma2TopCatHom g =
      𝟙 (TopCat.of R) := by
  refine ⟨?_, ?_⟩
  · simpa [hoppingSigma1TopCatHom] using braidGenerator1LeftTopCatHom_involutive g
  · simpa [hoppingSigma2TopCatHom] using braidGenerator2LeftTopCatHom_involutive g

end Topological

end InfoGeometry.Canonical.CuntzFractalHoppingAnyons
