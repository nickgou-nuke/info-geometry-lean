import Mathlib.LinearAlgebra.Complex.Module
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.RealifiedTokenOperatorBridge

/-!
# Explicit real coordinates for the finite complex token carrier

The canonical Mathlib realification of `ℂ` is `Complex.equivRealProdLm`.
This owner applies it pointwise.  It records coordinates only; it does not
turn the operator algebra into a scalar algebra.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

abbrev RealTokenCoordinates := (V × Fin 2) → (ℝ × ℝ)

noncomputable def realTokenCoordinateEquiv :
    RealTokenHilbertSpace (V := V) ≃ₗ[ℝ] RealTokenCoordinates (V := V) where
  toFun ψ := fun i => Complex.equivRealProdLm (ψ i)
  invFun c := fun i => Complex.equivRealProdLm.symm (c i)
  left_inv := by
    intro ψ
    funext i
    exact Complex.equivRealProdLm.symm_apply_apply (ψ i)
  right_inv := by
    intro c
    funext i
    exact Complex.equivRealProdLm.apply_symm_apply (c i)
  map_add' := by
    intro ψ φ
    funext i
    exact Complex.equivRealProdLm.map_add (ψ i) (φ i)
  map_smul' := by
    intro r ψ
    funext i
    exact Complex.equivRealProdLm.map_smul r (ψ i)

@[simp] theorem realTokenCoordinateEquiv_apply
    (ψ : RealTokenHilbertSpace (V := V)) (i : V × Fin 2) :
    realTokenCoordinateEquiv ψ i = (Complex.re (ψ i), Complex.im (ψ i)) := by
  rfl

@[simp] theorem realTokenCoordinateEquiv_symm_apply
    (c : RealTokenCoordinates (V := V)) (i : V × Fin 2) :
    realTokenCoordinateEquiv.symm c i = (c i).1 + (c i).2 * Complex.I := by
  exact Complex.equivRealProdLm_symm_apply (c i)

theorem realTokenCoordinateEquiv_coordinates_re_im
    (ψ : RealTokenHilbertSpace (V := V)) (i : V × Fin 2) :
    (realTokenCoordinateEquiv ψ i).1 = Complex.re (ψ i) ∧
      (realTokenCoordinateEquiv ψ i).2 = Complex.im (ψ i) := by
  simp

end
end InfoGeometry.Dynamics
