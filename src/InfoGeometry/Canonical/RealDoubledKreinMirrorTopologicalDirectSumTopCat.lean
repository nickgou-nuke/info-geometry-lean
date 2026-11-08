import InfoGeometry.Canonical.RealDoubledKreinMirrorTopologicalDirectSum
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat packaging of the continuous mirror direct sum

The continuous even/odd reconstruction is exposed as a commutative `TopCat`
square.  This is a categorical wrapper around the kernel-checked direct-sum
map; it does not promote the construction to a C*-algebraic completion.
-/

namespace InfoGeometry.Canonical.DoubledHestenesKreinData

open CategoryTheory

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (K : DoubledHestenesKreinData V)

noncomputable def mirrorProjectionToProductTopCatHom :
    TopCat.of (ContinuousOperator V) ⟶
      TopCat.of (mirrorEvenSubmodule K × mirrorOddSubmodule K) :=
  TopCat.ofHom
    { toFun := mirrorProjectionToProduct K
      continuous_toFun := (mirrorProjectionToProduct K).continuous }

noncomputable def mirrorProjectionFromProductTopCatHom :
    TopCat.of (mirrorEvenSubmodule K × mirrorOddSubmodule K) ⟶
      TopCat.of (ContinuousOperator V) :=
  TopCat.ofHom
    { toFun := mirrorProjectionFromProduct K
      continuous_toFun := (mirrorProjectionFromProduct K).continuous }

@[simp] theorem mirrorProjectionToProductTopCatHom_apply
    (T : ContinuousOperator V) :
    mirrorProjectionToProductTopCatHom K T =
      mirrorProjectionToProduct K T := rfl

@[simp] theorem mirrorProjectionFromProductTopCatHom_apply
    (p : mirrorEvenSubmodule K × mirrorOddSubmodule K) :
    mirrorProjectionFromProductTopCatHom K p =
      mirrorProjectionFromProduct K p := rfl

theorem mirrorProjectionTopCat_reconstruction :
    mirrorProjectionToProductTopCatHom K ≫
        mirrorProjectionFromProductTopCatHom K =
      𝟙 (TopCat.of (ContinuousOperator V)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro T
  change mirrorProjectionFromProduct K
      (mirrorProjectionToProduct K T) = T
  exact mirrorProjectionFromProduct_toProduct K T

end
end InfoGeometry.Canonical.DoubledHestenesKreinData
