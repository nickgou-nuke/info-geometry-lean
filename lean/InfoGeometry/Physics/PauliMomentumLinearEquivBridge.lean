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

noncomputable def fourMomentumCoordEquiv : FourMomentum ≃ (Fin 4 → ℂ) where
  toFun P := ![P.E, P.px, P.py, P.pz]
  invFun v := ⟨v 0, v 1, v 2, v 3⟩
  left_inv P := by cases P <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl

noncomputable instance : AddCommGroup FourMomentum :=
  Equiv.addCommGroup fourMomentumCoordEquiv

noncomputable instance : Module ℂ FourMomentum :=
  Equiv.module ℂ fourMomentumCoordEquiv

theorem addFourMomentum_eq_add (P Q : FourMomentum) :
    addFourMomentum P Q = P + Q := by
  apply fourMomentumCoordEquiv.injective
  funext i
  fin_cases i <;> rfl

theorem smul_fourMomentum (c : ℂ) (P : FourMomentum) :
    c • P = ⟨c * P.E, c * P.px, c * P.py, c * P.pz⟩ := by
  apply fourMomentumCoordEquiv.injective
  funext i
  fin_cases i <;> rfl

@[simp] theorem add_fourMomentum (P Q : FourMomentum) :
    P + Q = ⟨P.E + Q.E, P.px + Q.px, P.py + Q.py, P.pz + Q.pz⟩ := by
  rw [← addFourMomentum_eq_add]
  rfl

def pauliMomentumLinear : FourMomentum →ₗ[ℂ] M2C where
  toFun := pauliMomentum
  map_add' P Q := by
    rw [← addFourMomentum_eq_add]
    exact pauliMomentum_add P Q
  map_smul' c P := by
    rcases P with ⟨E, px, py, pz⟩
    rw [smul_fourMomentum]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliMomentum, Matrix.smul_apply]
      <;> ring

def fourMomentumOfMatrixLinear : M2C →ₗ[ℂ] FourMomentum where
  toFun := fourMomentumOfMatrix
  map_add' X Y := by
    apply fourMomentum_ext_of_pauliMomentum_eq
    calc
      pauliMomentum (fourMomentumOfMatrix (X + Y)) = X + Y :=
        pauliMomentum_fourMomentumOfMatrix (X + Y)
      _ = pauliMomentum (addFourMomentum (fourMomentumOfMatrix X)
          (fourMomentumOfMatrix Y)) :=
        by simpa only [pauliMomentum_fourMomentumOfMatrix] using
          (pauliMomentum_add (fourMomentumOfMatrix X)
            (fourMomentumOfMatrix Y)).symm
      _ = pauliMomentum (fourMomentumOfMatrix X + fourMomentumOfMatrix Y) :=
        congrArg pauliMomentum (addFourMomentum_eq_add _ _)
  map_smul' c X := by
    rw [smul_fourMomentum]
    apply fourMomentum_ext_of_pauliMomentum_eq
    ext i j
    fin_cases i <;> fin_cases j
    simp [pauliMomentum, fourMomentumOfMatrix, recoverE, recoverPx,
      recoverPy, recoverPz, σ1, σ2, σ3, Matrix.trace, Matrix.mul_apply]
    all_goals (try simp [Complex.I_mul_I])
    all_goals ring_nf
    all_goals (try simp [pauliMomentum, fourMomentumOfMatrix, recoverE, recoverPx,
      recoverPy, recoverPz, σ1, σ2, σ3, Matrix.trace, Matrix.mul_apply,
      Matrix.smul_apply] <;> ring)

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
