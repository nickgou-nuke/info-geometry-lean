import InfoGeometry.Canonical.ContinuousLeftActionTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge

/-!
# Cuntz three-strand action through the generic `TopCat` action owner

This is the concrete wiring layer: the noncommutative Cuntz carrier uses its
regular continuous left action, while the braid equations are inherited from
the algebraic owner through the generic translation calculus.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeContinuousActionTopCat

open CategoryTheory
open InfoGeometry.Canonical.ContinuousLeftActionTopCat
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

variable {R : Type*} [Ring R] [StarRing R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (g : ToeplitzCuntzThreeGenerators R)

/-- The Cuntz carrier equipped with its regular continuous left action. -/
abbrev cuntzRegularAction : ContinuousLeftAction R R :=
  regularLeftAction

theorem braidGenerator1_translation_eq :
    translation cuntzRegularAction (braidGenerator1 g) =
      braidGenerator1LeftTopCatHom g := by
  rfl

theorem braidGenerator2_translation_eq :
    translation cuntzRegularAction (braidGenerator2 g) =
      braidGenerator2LeftTopCatHom g := by
  rfl

theorem braidGenerator_artin_via_regular_action :
    translation cuntzRegularAction (braidGenerator1 g) ≫
        translation cuntzRegularAction (braidGenerator2 g) ≫
        translation cuntzRegularAction (braidGenerator1 g) =
      translation cuntzRegularAction (braidGenerator2 g) ≫
        translation cuntzRegularAction (braidGenerator1 g) ≫
        translation cuntzRegularAction (braidGenerator2 g) := by
  rw [translation_word, translation_word]
  exact congrArg (fun z : R => translation cuntzRegularAction z)
    (artin_braid_relation g)

theorem braidGenerator1_involutive_via_regular_action :
    translation cuntzRegularAction (braidGenerator1 g) ≫
        translation cuntzRegularAction (braidGenerator1 g) =
      𝟙 (TopCat.of R) := by
  rw [translation_comp]
  rw [braidGenerator1_sq g]
  exact translation_one cuntzRegularAction

theorem braidGenerator2_involutive_via_regular_action :
    translation cuntzRegularAction (braidGenerator2 g) ≫
        translation cuntzRegularAction (braidGenerator2 g) =
      𝟙 (TopCat.of R) := by
  rw [translation_comp]
  rw [braidGenerator2_sq g]
  exact translation_one cuntzRegularAction

theorem coxeter_translation_cube :
    translation cuntzRegularAction (coxeterElement g) ≫
        translation cuntzRegularAction (coxeterElement g) ≫
        translation cuntzRegularAction (coxeterElement g) =
      𝟙 (TopCat.of R) := by
  rw [translation_word, coxeterElement_cube g]
  exact translation_one cuntzRegularAction

theorem cyclicSupercharge_translation_eq_compressed_coxeter :
    translation cuntzRegularAction (cyclicSupercharge g) =
      translation cuntzRegularAction g.susyHamiltonian ≫
        translation cuntzRegularAction (coxeterElement g) ≫
        translation cuntzRegularAction g.susyHamiltonian := by
  rw [translation_word]
  exact congrArg (fun z : R => translation cuntzRegularAction z)
    (cyclicSupercharge_eq_compressed_coxeter g)

theorem cyclicSupercharge_vacuum_annihilation_right_topCat :
    translation cuntzRegularAction (cyclicSupercharge g) ≫
        translation cuntzRegularAction g.P0 =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change g.P0 * (cyclicSupercharge g * x) = 0
  rw [← mul_assoc, cyclicSupercharge_defect_annihilation_left g,
    zero_mul]

theorem cyclicSupercharge_vacuum_annihilation_left_topCat :
    translation cuntzRegularAction g.P0 ≫
        translation cuntzRegularAction (cyclicSupercharge g) =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change cyclicSupercharge g * (g.P0 * x) = 0
  rw [← mul_assoc, cyclicSupercharge_defect_annihilation_right g,
    zero_mul]

end InfoGeometry.Canonical.ToeplitzCuntzThreeContinuousActionTopCat
