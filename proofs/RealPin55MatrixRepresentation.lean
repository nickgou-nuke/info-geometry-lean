import proofs.V55Fin10Coordinates
import proofs.RealOrthogonalGroup55

/-! # The ten-dimensional matrix representation of the full real Pin group -/

noncomputable section
namespace RealPin55MatrixRepresentation

open Clifford55
open SplitOctonionTKK55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55OrthogonalAction
open V55Fin10Coordinates
open RealOrthogonalGroup55

def matrixUnitOfLinearEquiv (f : V55 ≃ₗ[ℝ] V55) : M10ˣ where
  val := LinearMap.toMatrix fin10Basis55 fin10Basis55 f
  inv := LinearMap.toMatrix fin10Basis55 fin10Basis55 f.symm
  val_inv := by
    rw [← LinearMap.toMatrix_comp]
    simp
  inv_val := by
    rw [← LinearMap.toMatrix_comp]
    simp

@[simp] theorem coe_matrixUnitOfLinearEquiv (f : V55 ≃ₗ[ℝ] V55) :
    (matrixUnitOfLinearEquiv f : M10) =
      LinearMap.toMatrix fin10Basis55 fin10Basis55 f := rfl

def linearEquivToMatrixUnits : (V55 ≃ₗ[ℝ] V55) →* M10ˣ where
  toFun := matrixUnitOfLinearEquiv
  map_one' := by
    apply Units.ext
    simp [matrixUnitOfLinearEquiv]
  map_mul' f g := by
    apply Units.ext
    change LinearMap.toMatrix fin10Basis55 fin10Basis55 (f * g) =
      LinearMap.toMatrix fin10Basis55 fin10Basis55 f *
        LinearMap.toMatrix fin10Basis55 fin10Basis55 g
    exact LinearMap.toMatrix_comp _ _ _ _ _

/-- Concrete ten-dimensional matrix representation before restricting its
codomain to the verified subgroup `O55`. -/
def fullPinMatrixRepresentation : FullPin55 →* M10ˣ :=
  linearEquivToMatrixUnits.comp fullPinVectorRepresentation

theorem fullPinMatrix_mulVec (g : FullPin55) (v : V55) :
    ((fullPinMatrixRepresentation g : M10ˣ) : M10).mulVec
        (v55Fin10Equiv v) =
      v55Fin10Equiv (twistedVector g v) := by
  simp only [fullPinMatrixRepresentation, MonoidHom.comp_apply,
    linearEquivToMatrixUnits,
    v55Fin10Equiv]
  change (LinearMap.toMatrix fin10Basis55 fin10Basis55
    (fullPinVectorRepresentation g)).mulVec (fin10Basis55.repr v) =
      fin10Basis55.repr (twistedVector g v)
  rw [LinearMap.toMatrix_mulVec_repr]
  rfl

theorem fullPinMatrix_mem_O55 (g : FullPin55) :
    fullPinMatrixRepresentation g ∈ O55 := by
  let A : M10 := (fullPinMatrixRepresentation g : M10ˣ)
  let F : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ) := Matrix.toLin' A
  have hF (x : Fin 10 → ℝ) :
      F x = v55Fin10Equiv (twistedVector g (v55Fin10Equiv.symm x)) := by
    change A.mulVec x = _
    simpa using fullPinMatrix_mulVec g (v55Fin10Equiv.symm x)
  have hcomp : Qcoord55.comp F = Qcoord55 := by
    ext x
    rw [QuadraticMap.comp_apply, hF]
    simp only [Qcoord55, QuadraticMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact fullPin55_preserves_Q g (v55Fin10Equiv.symm x)
  have hm := congrArg QuadraticMap.toMatrix' hcomp
  rw [QuadraticMap.toMatrix'_comp, Qcoord55_toMatrix] at hm
  change A.transpose * eta55 * A = eta55
  simpa [F, A] using hm

/-- The concrete signature-correct Pin representation in the native matrix
group `O(5,5)`. -/
def fullPinToO55 : FullPin55 →* O55 where
  toFun g := ⟨fullPinMatrixRepresentation g, fullPinMatrix_mem_O55 g⟩
  map_one' := by
    apply Subtype.ext
    exact fullPinMatrixRepresentation.map_one
  map_mul' g h := by
    apply Subtype.ext
    exact fullPinMatrixRepresentation.map_mul g h

@[simp] theorem fullPinToO55_coe (g : FullPin55) :
    ((fullPinToO55 g : O55) : M10ˣ) = fullPinMatrixRepresentation g := rfl

end RealPin55MatrixRepresentation
end noncomputable section
