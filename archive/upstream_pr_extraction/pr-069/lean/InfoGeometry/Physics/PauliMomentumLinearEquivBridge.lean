import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra

/-!
# Native linear Pauli soldering

The existing Hestenes owner proves pointwise Pauli soldering round-trips.  This
owner packages the same finite carrier as a native `LinearEquiv`, so later
Clifford/Cantor readouts can target a typed linear carrier rather than an
unstructured coordinate function.
-/

noncomputable section

namespace InfoGeometry.Physics.PauliMomentumLinearEquivBridge

open Matrix
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Physics.LorentzChiralCuntzBridge

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def pauliMomentumLinear : FourMomentum →ₗ[ℂ] M2C where
  toFun := pauliMomentum
  map_add' P Q := by
    simpa [addFourMomentum] using pauliMomentum_add P Q
  map_smul' c P := by
    rcases P with ⟨E, px, py, pz⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliMomentum, Matrix.smul_apply] <;> ring

def fourMomentumOfMatrixLinear : M2C →ₗ[ℂ] FourMomentum where
  toFun := fourMomentumOfMatrix
  map_add' X Y := by
    apply Prod.ext
    · simp [fourMomentumOfMatrix, recoverE, Matrix.trace, Matrix.add_apply] <;> ring
    · apply Prod.ext
      · simp [fourMomentumOfMatrix, recoverPx, σ1, Matrix.trace,
          Matrix.mul_apply, Matrix.add_apply] <;> ring
      · apply Prod.ext
        · simp [fourMomentumOfMatrix, recoverPy, σ2, Matrix.trace,
            Matrix.mul_apply, Matrix.add_apply] <;> ring
        · simp [fourMomentumOfMatrix, recoverPz, σ3, Matrix.trace,
            Matrix.mul_apply, Matrix.add_apply] <;> ring
  map_smul' c X := by
    apply Prod.ext
    · simp [fourMomentumOfMatrix, recoverE, Matrix.trace, Matrix.smul_apply] <;> ring
    · apply Prod.ext
      · simp [fourMomentumOfMatrix, recoverPx, σ1, Matrix.trace,
          Matrix.mul_apply, Matrix.smul_apply] <;> ring
      · apply Prod.ext
        · simp [fourMomentumOfMatrix, recoverPy, σ2, Matrix.trace,
            Matrix.mul_apply, Matrix.smul_apply] <;> ring
        · simp [fourMomentumOfMatrix, recoverPz, σ3, Matrix.trace,
            Matrix.mul_apply, Matrix.smul_apply] <;> ring

/-- Native linear equivalence underlying the finite Pauli/Hestenes soldering. -/
def pauliMomentumLinearEquiv : FourMomentum ≃ₗ[ℂ] M2C where
  toLinearMap := pauliMomentumLinear
  invFun := fourMomentumOfMatrix
  left_inv P := by
    exact InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra.vector_coordinate_roundtrip P
  right_inv X := by
    exact pauliMomentum_fourMomentumOfMatrix X

@[simp] theorem pauliMomentumLinearEquiv_apply (P : FourMomentum) :
    pauliMomentumLinearEquiv P = pauliMomentum P := rfl

@[simp] theorem pauliMomentumLinearEquiv_symm_apply (X : M2C) :
    pauliMomentumLinearEquiv.symm X = fourMomentumOfMatrix X := rfl

end InfoGeometry.Physics.PauliMomentumLinearEquivBridge
