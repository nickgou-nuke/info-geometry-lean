import InfoGeometry.Canonical.ContinuousLeftActionTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ToeplitzCuntzThreeAnyonBraidCentralChargeBridge

/-!
# Topological braided central charge on the Cuntz carrier

The algebraic full-twist and cubic-compression theorems are transported to
`TopCat` through regular continuous translations.  The order of factors is
kept explicit: categorical composition acts on the right, hence translations
reverse multiplication order.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeAnyonBraidCentralChargeTopological

open CategoryTheory
open InfoGeometry.Canonical.ContinuousLeftActionTopCat
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeAnyonBraidCentralChargeBridge

variable {A : Type*} [Ring A] [StarRing A]
variable [TopologicalSpace A] [ContinuousMul A]
variable (g : ToeplitzCuntzThreeGenerators A)
variable (D : BraidedExcitationData g)

abbrev regularAction : ContinuousLeftAction A A := regularLeftAction

theorem braidedCubicSupercharge_cube_topCat :
    translation regularAction (braidedCubicSupercharge g D) ≫
        translation regularAction (braidedCubicSupercharge g D) ≫
        translation regularAction (braidedCubicSupercharge g D) =
      translation regularAction g.susyHamiltonian ≫
        translation regularAction (fullTwist g D) := by
  rw [translation_word, translation_comp]
  exact congrArg (fun z : A => translation regularAction z)
    (braidedCubicSupercharge_cube_eq_fullTwist_hamiltonian g D)

theorem fullTwist_hamiltonian_commutation_topCat :
    translation regularAction g.susyHamiltonian ≫
        translation regularAction (fullTwist g D) =
      translation regularAction (fullTwist g D) ≫
        translation regularAction g.susyHamiltonian := by
  rw [translation_comp, translation_comp]
  exact congrArg (fun z : A => translation regularAction z)
    (fullTwist_comm_hamiltonian g D)

theorem braidedCubicSupercharge_vacuum_right_topCat :
    translation regularAction (braidedCubicSupercharge g D) ≫
        translation regularAction g.P0 =
      TopCat.ofHom (ContinuousMap.const A 0) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change g.P0 * (braidedCubicSupercharge g D * x) = 0
  rw [← mul_assoc, vacuum_braidedCubicSupercharge_annihilation g D,
    zero_mul]

theorem braidedCubicSupercharge_vacuum_left_topCat :
    translation regularAction g.P0 ≫
        translation regularAction (braidedCubicSupercharge g D) =
      TopCat.ofHom (ContinuousMap.const A 0) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidedCubicSupercharge g D * (g.P0 * x) = 0
  rw [← mul_assoc, braidedCubicSupercharge_vacuum_annihilation g D,
    zero_mul]

end InfoGeometry.Canonical.ToeplitzCuntzThreeAnyonBraidCentralChargeTopological
