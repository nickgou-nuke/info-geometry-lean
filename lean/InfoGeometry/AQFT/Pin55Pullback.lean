import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace InfoGeometry.AQFT.Pin55Pullback

lemma card_finset_fin_five : Fintype.card (Finset (Fin 5)) = 32 := by
  decide

noncomputable def bladeMatrixEquiv : Finset (Fin 5) ≃ Fin 32 :=
  Fintype.equivFinOfCardEq card_finset_fin_five

variable {R W A : Type*}
variable [CommRing R] [AddCommGroup W] [Module R W]
variable [Ring A] [Algebra R A]

noncomputable def chevalleyMatrixFusionOfBasis
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W)) :
    Module.End R (ExteriorAlgebra R W) ≃ₐ[R] Matrix (Fin 32) (Fin 32) R :=
  LinearMap.toMatrixAlgEquiv exteriorBasis

noncomputable def matrixRepresentationOfBasis
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W))
    (ρ : A →ₐ[R] Module.End R (ExteriorAlgebra R W)) :
    A →ₐ[R] Matrix (Fin 32) (Fin 32) R :=
  (chevalleyMatrixFusionOfBasis exteriorBasis).toAlgHom.comp ρ

@[simp]
theorem matrixRepresentationOfBasis_apply
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W))
    (ρ : A →ₐ[R] Module.End R (ExteriorAlgebra R W))
    (a : A) :
    matrixRepresentationOfBasis exteriorBasis ρ a =
      LinearMap.toMatrix exteriorBasis exteriorBasis (ρ a) := by
  rfl

end InfoGeometry.AQFT.Pin55Pullback
