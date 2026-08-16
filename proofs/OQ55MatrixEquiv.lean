import proofs.RealO55CartanDieudonne

/-! # Equivalence of the native quadratic and diagonal matrix models of O(5,5) -/

noncomputable section
namespace OQ55MatrixEquiv

open Clifford55
open SplitOctonionTKK55
open V55Fin10Coordinates
open RealOrthogonalGroup55
open RealPin55QuadraticRepresentation
open RealPin55MatrixRepresentation
open RealPin55TwistedAction
open RealO55CartanDieudonne

def matrixUnitLinearEquiv (A : M10ˣ) :
    (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  LinearEquiv.ofLinear (Matrix.toLin' (A : M10))
    (Matrix.toLin' (A⁻¹ : M10ˣ))
    (by
      rw [← Matrix.toLin'_mul]
      change Matrix.toLin' ((A * A⁻¹ : M10ˣ) : M10) = LinearMap.id
      rw [mul_inv_cancel]
      exact Matrix.toLin'_one)
    (by
      rw [← Matrix.toLin'_mul]
      change Matrix.toLin' ((A⁻¹ * A : M10ˣ) : M10) = LinearMap.id
      rw [inv_mul_cancel]
      exact Matrix.toLin'_one)

@[simp] theorem matrixUnitLinearEquiv_apply (A : M10ˣ) (x : Fin 10 → ℝ) :
    matrixUnitLinearEquiv A x = (A : M10).mulVec x := rfl

def matrixUnitV55Equiv (A : M10ˣ) : V55 ≃ₗ[ℝ] V55 :=
  v55Fin10Equiv.trans ((matrixUnitLinearEquiv A).trans v55Fin10Equiv.symm)

@[simp] theorem matrixUnitV55Equiv_coordinates (A : M10ˣ) (v : V55) :
    v55Fin10Equiv (matrixUnitV55Equiv A v) =
      (A : M10).mulVec (v55Fin10Equiv v) := by
  simp [matrixUnitV55Equiv]

theorem matrix_preserves_eta_quadratic {A : M10ˣ}
    (hA : (A : M10).transpose * eta55 * (A : M10) = eta55)
    (x : Fin 10 → ℝ) :
    dotProduct ((A : M10).mulVec x)
        (eta55.mulVec ((A : M10).mulVec x)) =
      dotProduct x (eta55.mulVec x) := by
  calc
    dotProduct ((A : M10).mulVec x)
        (eta55.mulVec ((A : M10).mulVec x)) =
      dotProduct (Matrix.vecMul x (A : M10).transpose)
        (eta55.mulVec ((A : M10).mulVec x)) := by
          rw [Matrix.vecMul_transpose]
    _ = dotProduct
        (Matrix.vecMul (Matrix.vecMul x (A : M10).transpose) eta55)
        ((A : M10).mulVec x) := Matrix.dotProduct_mulVec _ _ _
    _ = dotProduct (Matrix.vecMul x ((A : M10).transpose * eta55))
        ((A : M10).mulVec x) := by rw [Matrix.vecMul_vecMul]
    _ = dotProduct x
        (((A : M10).transpose * eta55).mulVec ((A : M10).mulVec x)) :=
          (Matrix.dotProduct_mulVec _ _ _).symm
    _ = dotProduct x
        (((A : M10).transpose * eta55 * (A : M10)).mulVec x) := by
          rw [Matrix.mulVec_mulVec]
    _ = dotProduct x (eta55.mulVec x) := by rw [hA]

def o55ToOQ55 (g : O55) : OQ55 where
  val := matrixUnitV55Equiv g.1
  property v := by
    rw [Q55_eq_eta55, matrixUnitV55Equiv_coordinates, Q55_eq_eta55]
    exact matrix_preserves_eta_quadratic g.2 (v55Fin10Equiv v)

theorem matrixUnitOf_matrixUnitV55Equiv (A : M10ˣ) :
    matrixUnitOfLinearEquiv (matrixUnitV55Equiv A) = A := by
  apply Units.ext
  change LinearMap.toMatrix fin10Basis55 fin10Basis55
      (matrixUnitV55Equiv A).toLinearMap = (A : M10)
  rw [← LinearMap.toMatrix_toLin (v₁ := fin10Basis55)
    (v₂ := fin10Basis55) (A : M10)]
  congr 1

/-- The signature-correct Clifford representation is constructively
surjective onto the concrete diagonal matrix group `O(5,5)`. -/
theorem fullPinToO55_surjective : Function.Surjective fullPinToO55 := by
  intro g
  rcases fullPinToOQ55_surjective (o55ToOQ55 g) with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  have hlin : fullPinVectorRepresentation p = matrixUnitV55Equiv g.1 := by
    exact congrArg Subtype.val hp
  change matrixUnitOfLinearEquiv (fullPinVectorRepresentation p) = g.1
  rw [hlin, matrixUnitOf_matrixUnitV55Equiv]

/-! ## Compatibility with the quadratic-linear representation -/

/--
The coordinate-matrix and quadratic-linear realizations of the full Pin
action form one commuting square.
-/
theorem fullPinToOQ55_eq_o55ToOQ55_fullPinToO55
    (g : RealPin55Core.FullPin55) :
    RealPin55QuadraticRepresentation.fullPinToOQ55 g =
      o55ToOQ55 (RealPin55MatrixRepresentation.fullPinToO55 g) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change
    ((RealPin55QuadraticRepresentation.fullPinToOQ55 g).1 v) =
      matrixUnitV55Equiv
        (RealPin55MatrixRepresentation.fullPinToO55 g).1 v
  apply v55Fin10Equiv.injective
  change
    v55Fin10Equiv
        ((RealPin55QuadraticRepresentation.fullPinToOQ55 g).1 v) =
      v55Fin10Equiv
        (matrixUnitV55Equiv
          (RealPin55MatrixRepresentation.fullPinToO55 g).1 v)
  rw [matrixUnitV55Equiv_coordinates]
  rw [RealPin55MatrixRepresentation.fullPinToO55_coe]
  rw [RealPin55QuadraticRepresentation.fullPinToOQ55_apply]
  exact (RealPin55MatrixRepresentation.fullPinMatrix_mulVec g v).symm

end OQ55MatrixEquiv
end noncomputable section
