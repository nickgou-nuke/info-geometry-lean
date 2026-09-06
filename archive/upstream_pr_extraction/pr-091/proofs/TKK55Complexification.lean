import proofs.SO55HyperbolicDiagonalLieEquiv
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Complexification of the native TKK--`so(5,5)` Lie equivalence -/

noncomputable section
namespace TKK55Complexification

open scoped TensorProduct
open SplitOctonionTKK55LieEquivalence
open SO55HyperbolicDiagonalLieEquiv

abbrev ComplexTKK := ℂ ⊗[ℝ] TKKBlockCarrier
abbrev ComplexDiagonalSO55 := ℂ ⊗[ℝ] diagonalSO55

def complexTkkDiagonalLinearEquiv :
    ComplexTKK ≃ₗ[ℂ] ComplexDiagonalSO55 :=
  tkkDiagonalLieEquiv.toLinearEquiv.baseChange ℝ ℂ _ _

@[simp] theorem complexTkkDiagonalLinearEquiv_tmul
    (z : ℂ) (x : TKKBlockCarrier) :
    complexTkkDiagonalLinearEquiv (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] tkkDiagonalLieEquiv x := by
  rfl

theorem complexTkkDiagonalLinearEquiv_lie
    (x y : ComplexTKK) :
    complexTkkDiagonalLinearEquiv ⁅x, y⁆ =
      ⁅complexTkkDiagonalLinearEquiv x,
        complexTkkDiagonalLinearEquiv y⁆ := by
  let f : ComplexTKK →ₗ⁅ℝ⁆ ComplexDiagonalSO55 :=
    LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
      tkkDiagonalLieEquiv.toLieHom
  have hf (u : ComplexTKK) : complexTkkDiagonalLinearEquiv u = f u := by
    refine u.induction_on ?_ ?_ ?_
    · rfl
    · intro z a
      rfl
    · intro u v hu hv
      rw [map_add, map_add, hu, hv]
  rw [hf, hf, hf]
  exact f.map_lie x y

def complexTkkDiagonalLieHom :
    ComplexTKK →ₗ⁅ℂ⁆ ComplexDiagonalSO55 where
  toLinearMap := complexTkkDiagonalLinearEquiv.toLinearMap
  map_lie' := fun {x y} => complexTkkDiagonalLinearEquiv_lie x y

/-- Scalar extension preserves the genuine native TKK Lie equivalence. -/
def complexTkkDiagonalLieEquiv :
    ComplexTKK ≃ₗ⁅ℂ⁆ ComplexDiagonalSO55 :=
  LieEquiv.ofBijective complexTkkDiagonalLieHom <| by
    change Function.Bijective complexTkkDiagonalLinearEquiv
    exact complexTkkDiagonalLinearEquiv.bijective

@[simp] theorem complexTkkDiagonalLieEquiv_tmul
    (z : ℂ) (x : TKKBlockCarrier) :
    complexTkkDiagonalLieEquiv (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] tkkDiagonalLieEquiv x := by
  exact complexTkkDiagonalLinearEquiv_tmul z x

end TKK55Complexification
end noncomputable section
