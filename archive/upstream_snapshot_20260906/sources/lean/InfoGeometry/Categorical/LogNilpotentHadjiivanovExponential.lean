import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Algebra.Equiv
import InfoGeometry.Categorical.LogNilpotentAmbientSymmetric
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Natural Hadjiivanov exponential on finite-nilpotent logarithmic modules

The rank-two Hadjiivanov checked braid uses the affine truncation
`1 + p (N_X ⊗ N_Y)` because the mixed cross term is square-zero there.
That affine formula is not tensor-stable once higher nilpotency appears.

Mathlib already owns the correct finite algebraic replacement:
`IsNilpotent.exp`.  For finite-nilpotent logarithmic modules we therefore use

`R_{X,Y}(p) = exp (p • (N_X ⊗ N_Y))`.

No analytic convergence is involved: `IsNilpotent.exp` is the finite nilpotent
exponential from `Mathlib.RingTheory.Nilpotent.Exp`.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentHadjiivanovExponential

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalCategory
open InfoGeometry.Categorical.LogNilpotentAmbientSymmetric
open InfoGeometry.Clifford.LogCftMonodromy

/-- The mixed logarithmic endomorphism on a tensor product. -/
def crossEnd (X Y : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗ Y) :=
  crossTensorEnd X.toLogEndModule Y.toLogEndModule

/-- Powers of the mixed logarithmic endomorphism remain factorwise. -/
theorem crossEnd_pow (X Y : LogNilpotentModule ℂ) (k : ℕ) :
    crossEnd X Y ^ k = TensorProduct.map (X.N ^ k) (Y.N ^ k) := by
  simpa [crossEnd, crossTensorEnd] using
    (TensorProduct.map_pow X.N Y.N k)

/-- The mixed logarithmic endomorphism is nilpotent as soon as either factor is. -/
theorem crossEnd_isNilpotent (X Y : LogNilpotentModule ℂ) :
    IsNilpotent (crossEnd X Y) := by
  refine ⟨X.nilpotencyOrder, ?_⟩
  rw [crossEnd_pow, X.nilpotent]
  ext x y
  simp

/-- Scalar multiples of the mixed logarithmic endomorphism remain nilpotent. -/
theorem scaledCrossEnd_isNilpotent
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    IsNilpotent (p • crossEnd X Y) :=
  (crossEnd_isNilpotent X Y).smul p

/-- The mixed cross term commutes with the primitive tensor logarithmic
endomorphism for arbitrary finite nilpotency.  The square-zero owner proves the
stronger vanishing statement in the rank-two case; here only commutation is
needed. -/
theorem crossEnd_commute_tensorN (X Y : LogNilpotentModule ℂ) :
    Commute (crossEnd X Y) (X ⊗ Y).N := by
  apply Commute.eq
  ext x y
  simp [crossEnd, crossTensorEnd, Module.End.mul_eq_comp,
    LinearMap.comp_apply, LogEndModule.tensorObj_N_tmul,
    TensorProduct.map_tmul]
  module

/-- The scaled cross term also commutes with the primitive tensor nilpotent. -/
theorem scaledCrossEnd_commute_tensorN
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    Commute (p • crossEnd X Y) (X ⊗ Y).N := by
  apply Commute.eq
  ext x y
  simp [crossEnd, crossTensorEnd, Module.End.mul_eq_comp,
    LinearMap.comp_apply, LogEndModule.tensorObj_N_tmul,
    TensorProduct.map_tmul]
  module

/-- Native finite nilpotent exponential of the mixed Hadjiivanov direction. -/
def crossExpEnd (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗ Y) :=
  IsNilpotent.exp (p • crossEnd X Y)

/-- The nilpotent exponential commutes with the total logarithmic tensor
endomorphism. -/
theorem crossExpEnd_commutes_tensorN
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    (crossExpEnd p X Y).comp (X ⊗ Y).N =
      (X ⊗ Y).N.comp (crossExpEnd p X Y) := by
  let A : Module.End ℂ (X ⊗ Y) := p • crossEnd X Y
  have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p X Y
  have hcomm : A.comp (X ⊗ Y).N = (X ⊗ Y).N.comp A := by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact (scaledCrossEnd_commute_tensorN p X Y).eq
  simpa [crossExpEnd, A] using
    (Module.End.commute_exp_left_of_commute hA hA hcomm)

/-- The finite exponential is an exact linear equivalence.  Its inverse is the
exponential of the negative mixed direction. -/
def crossExpLinearEquiv (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    (X ⊗ Y) ≃ₗ[ℂ] (X ⊗ Y) := by
  let A : Module.End ℂ (X ⊗ Y) := p • crossEnd X Y
  have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p X Y
  apply LinearEquiv.ofLinear (IsNilpotent.exp A) (IsNilpotent.exp (-A))
  · rw [← Module.End.mul_eq_comp]
    exact IsNilpotent.exp_mul_exp_neg_self hA
  · rw [← Module.End.mul_eq_comp]
    exact IsNilpotent.exp_neg_mul_exp_self hA

@[simp]
theorem crossExpLinearEquiv_toLinearMap
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    (crossExpLinearEquiv p X Y).toLinearMap = crossExpEnd p X Y := by
  rfl

/-- The exponential as an endomorphism in the logarithmic category. -/
def crossExpHom (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    X ⊗ Y ⟶ X ⊗ Y where
  hom := crossExpEnd p X Y
  comm := crossExpEnd_commutes_tensorN p X Y

/-- The finite exponential as an isomorphism in `LogNilpotentModule`. -/
def crossExpIso (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    X ⊗ Y ≅ X ⊗ Y where
  hom := crossExpHom p X Y
  inv := crossExpHom (-p) X Y
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    change (crossExpEnd (-p) X Y).comp (crossExpEnd p X Y) = LinearMap.id
    let A : Module.End ℂ (X ⊗ Y) := p • crossEnd X Y
    have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p X Y
    have hneg : (-p : ℂ) • crossEnd X Y = -A := by
      simp [A]
    rw [crossExpEnd, crossExpEnd, hneg]
    rw [← Module.End.mul_eq_comp]
    exact IsNilpotent.exp_neg_mul_exp_self hA
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    change (crossExpEnd p X Y).comp (crossExpEnd (-p) X Y) = LinearMap.id
    let A : Module.End ℂ (X ⊗ Y) := p • crossEnd X Y
    have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p X Y
    have hneg : (-p : ℂ) • crossEnd X Y = -A := by
      simp [A]
    rw [crossExpEnd, crossExpEnd, hneg]
    rw [← Module.End.mul_eq_comp]
    exact IsNilpotent.exp_mul_exp_neg_self hA

/-- Two-object logarithmic braiding candidate: apply the finite Hadjiivanov
exponential and then the canonical tensor exchange. -/
def logarithmicBraidingIso
    (p : ℂ) (X Y : LogNilpotentModule ℂ) : X ⊗ Y ≅ Y ⊗ X :=
  crossExpIso p X Y ≪≫ LogNilpotentModule.symmetricSwapIso X Y

/-- Tensor-product intertwiners carry the mixed cross endomorphism naturally. -/
theorem tensorHom_intertwines_scaledCross
    (p : ℂ)
    {X X' Y Y' : LogNilpotentModule ℂ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (p • crossEnd X' Y').comp (LogNilpotentModule.tensorHom f g).hom =
      (LogNilpotentModule.tensorHom f g).hom.comp (p • crossEnd X Y) := by
  ext x y
  simp [crossEnd, crossTensorEnd, LinearMap.comp_apply,
    TensorProduct.map_tmul, LogEndModule.Hom.map_N]

/-- Naturality of the finite mixed exponential under logarithmic intertwiners. -/
theorem tensorHom_intertwines_crossExp
    (p : ℂ)
    {X X' Y Y' : LogNilpotentModule ℂ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (crossExpEnd p X' Y').comp (LogNilpotentModule.tensorHom f g).hom =
      (LogNilpotentModule.tensorHom f g).hom.comp (crossExpEnd p X Y) := by
  exact Module.End.commute_exp_left_of_commute
    (scaledCrossEnd_isNilpotent p X Y)
    (scaledCrossEnd_isNilpotent p X' Y')
    (tensorHom_intertwines_scaledCross p f g)

/-- Right-variable naturality of the logarithmic braiding candidate. -/
theorem logarithmicBraiding_naturality_right
    (p : ℂ) (X : LogNilpotentModule ℂ)
    {Y Z : LogNilpotentModule ℂ} (f : Y ⟶ Z) :
    X ◁ f ≫ (logarithmicBraidingIso p X Z).hom =
      (logarithmicBraidingIso p X Y).hom ≫ f ▷ X := by
  change
    LogNilpotentModule.tensorHom (𝟙 X) f ≫
        (crossExpHom p X Z ≫
          (LogNilpotentModule.symmetricSwapIso X Z).hom) =
      (crossExpHom p X Y ≫
          (LogNilpotentModule.symmetricSwapIso X Y).hom) ≫
        LogNilpotentModule.tensorHom f (𝟙 X)
  rw [← Category.assoc]
  have hExp :
      LogNilpotentModule.tensorHom (𝟙 X) f ≫ crossExpHom p X Z =
        crossExpHom p X Y ≫ LogNilpotentModule.tensorHom (𝟙 X) f := by
    apply LogEndModule.Hom.ext
    exact (tensorHom_intertwines_crossExp p (𝟙 X) f).symm
  rw [hExp, Category.assoc]
  letI : BraidedCategory (LogNilpotentModule ℂ) := ambientBraidedCategory
  change
    crossExpHom p X Y ≫
        (X ◁ f ≫ (β_ X Z).hom) =
      crossExpHom p X Y ≫
        ((β_ X Y).hom ≫ f ▷ X)
  rw [BraidedCategory.braiding_naturality_right]

/-- Left-variable naturality of the logarithmic braiding candidate. -/
theorem logarithmicBraiding_naturality_left
    (p : ℂ)
    {X Y : LogNilpotentModule ℂ} (f : X ⟶ Y)
    (Z : LogNilpotentModule ℂ) :
    f ▷ Z ≫ (logarithmicBraidingIso p Y Z).hom =
      (logarithmicBraidingIso p X Z).hom ≫ Z ◁ f := by
  change
    LogNilpotentModule.tensorHom f (𝟙 Z) ≫
        (crossExpHom p Y Z ≫
          (LogNilpotentModule.symmetricSwapIso Y Z).hom) =
      (crossExpHom p X Z ≫
          (LogNilpotentModule.symmetricSwapIso X Z).hom) ≫
        LogNilpotentModule.tensorHom (𝟙 Z) f
  rw [← Category.assoc]
  have hExp :
      LogNilpotentModule.tensorHom f (𝟙 Z) ≫ crossExpHom p Y Z =
        crossExpHom p X Z ≫ LogNilpotentModule.tensorHom f (𝟙 Z) := by
    apply LogEndModule.Hom.ext
    exact (tensorHom_intertwines_crossExp p f (𝟙 Z)).symm
  rw [hExp, Category.assoc]
  letI : BraidedCategory (LogNilpotentModule ℂ) := ambientBraidedCategory
  change
    crossExpHom p X Z ≫
        (f ▷ Z ≫ (β_ Y Z).hom) =
      crossExpHom p X Z ≫
        ((β_ X Z).hom ≫ Z ◁ f)
  rw [BraidedCategory.braiding_naturality_left]

/-- The physical specialization uses the repository-owned Hadjiivanov shear
`-2πi`. -/
abbrev hadjiivanovBraidingIso
    (X Y : LogNilpotentModule ℂ) : X ⊗ Y ≅ Y ⊗ X :=
  logarithmicBraidingIso logShearBase X Y

end InfoGeometry.Categorical.LogNilpotentHadjiivanovExponential
