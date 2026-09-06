import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Clifford.Cl55SpinBivectorImage

/-!
# Lie transport of the native `Cl(5,5)` bivector algebra to spinor matrices

The existing `spinBivectorMatrixLinear` is the strict linear realization of
the native bivector subalgebra in `M₃₂(ℝ)`.  This owner packages its two
structural consequences: preservation of the associative commutator and
injectivity.  No arbitrary `so(5,5)` matrix is promoted to a spinor action.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinBivectorLieBridge

open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep

abbrev SpinBivector55 := Cl55SpinBivectorImage.SpinBivector55

theorem spinBivectorMatrixLinear_map_lie (X Y : SpinBivector55) :
    spinBivectorMatrixLinear ⁅X, Y⁆ =
      ⁅spinBivectorMatrixLinear X, spinBivectorMatrixLinear Y⁆ := by
  change cl55SpinorAlgEquiv ⁅(X : Cl55), (Y : Cl55)⁆ =
    ⁅cl55SpinorAlgEquiv (X : Cl55), cl55SpinorAlgEquiv (Y : Cl55)⁆
  simp [Ring.lie_def]

theorem spinBivectorMatrixLinear_injective :
    Function.Injective spinBivectorMatrixLinear := by
  intro X Y h
  apply Subtype.ext
  apply cl55SpinorAlgEquiv.injective
  exact h

noncomputable def spinBivectorMatrixLieHom :
    SpinBivector55 →ₗ⁅ℝ⁆ SpinorMatrix 5 where
  toFun := spinBivectorMatrixLinear
  map_add' := spinBivectorMatrixLinear.map_add
  map_smul' := spinBivectorMatrixLinear.map_smul
  map_lie' := by
    intro X Y
    exact spinBivectorMatrixLinear_map_lie X Y

theorem spinBivectorMatrixLieHom_apply (X : SpinBivector55) :
    spinBivectorMatrixLieHom X = spinBivectorMatrixLinear X := by
  rfl

theorem spinBivectorMatrixLieHom_injective :
    Function.Injective spinBivectorMatrixLieHom := by
  intro X Y h
  apply spinBivectorMatrixLinear_injective
  simpa [spinBivectorMatrixLieHom] using h

end InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
