import InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
import InfoGeometry.Clifford.Cl55IntegerRealMatrixBridge
import InfoGeometry.Clifford.Cl55WittOrthogonalReflections

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
open InfoGeometry.Clifford.Cl55IntegerRealMatrixBridge

/-!
# Coordinate readout of the native `Q55` reflections

The integer matrix owner and the native `V55` owner use the same ordered
coordinates, but they do not share a carrier definition.  This file supplies
the explicit real-linear equivalence between them and proves the two
coordinate reflection readouts.  It does not identify the integer matrices
with Clifford elements; the native Pin identification remains in the
`Cl55WittPin*` owners.
-/

abbrev V10R := Fin 10 → ℝ

def finTenSumFiveEquiv : Fin 5 ⊕ Fin 5 ≃ Fin 10 :=
  finSumFinEquiv.trans (finCongr (by norm_num))

def v55SumFunctionProdEquiv :
    ((Fin 5 ⊕ Fin 5) → ℝ) ≃ₗ[ℝ] V55 where
  toFun f := (fun i => f (.inl i), fun i => f (.inr i))
  invFun p := Sum.elim p.1 p.2
  left_inv f := by ext i <;> cases i <;> rfl
  right_inv p := by ext i <;> rfl
  map_add' x y := by ext i <;> rfl
  map_smul' c x := by ext i <;> rfl

noncomputable def v55Flatten : V55 ≃ₗ[ℝ] V10R where
  toFun x := fun k =>
    if h : k.val < 5 then x.1 ⟨k.val, h⟩
    else x.2 ⟨k.val - 5, by omega⟩
  invFun y :=
    (fun i => y ⟨i.val, by omega⟩,
      fun i => y ⟨i.val + 5, by omega⟩)
  left_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv y := by
    funext k
    fin_cases k <;> rfl
  map_add' x y := by
    funext k
    by_cases hk : k.val < 5
    · simp [hk, Pi.add_apply]
    · simp [hk, Pi.add_apply]
  map_smul' c x := by
    funext k
    by_cases hk : k.val < 5
    · simp [hk, Pi.smul_apply]
    · simp [hk, Pi.smul_apply]

theorem v55Flatten_apply (x : V55) (k : Fin 10) :
    v55Flatten x k =
      if h : k.val < 5 then x.1 ⟨k.val, h⟩
      else x.2 ⟨k.val - 5, by omega⟩ := by
  fin_cases k <;> rfl

@[simp] theorem v55Flatten_first (x : V55) (i : Fin 5) :
    v55Flatten x ⟨i.val, by omega⟩ = x.1 i := by
  fin_cases i <;> rfl

@[simp] theorem v55Flatten_second (x : V55) (i : Fin 5) :
    v55Flatten x ⟨i.val + 5, by omega⟩ = x.2 i := by
  fin_cases i <;> rfl

theorem pinReflectReal_mulVec (k : Fin 10) (x : V10R) :
    (intMatrixToReal (pinReflect k)).mulVec x =
      fun i => if i = k then -x i else x i := by
  funext i
  simp [intMatrixToReal, pinReflect, Matrix.mulVec, dotProduct]

theorem v55Flatten_negativeReflection_matrix (i : Fin 5) (x : V55) :
    v55Flatten (negativeReflection i x) =
      (intMatrixToReal (pinReflect ⟨i.val + 5, by omega⟩)).mulVec
        (v55Flatten x) := by
  funext k
  rw [pinReflectReal_mulVec]
  fin_cases i <;> fin_cases k <;>
    simp [v55Flatten, negativeReflection]

theorem v55Flatten_positiveReflection_matrix (i : Fin 5) (x : V55) :
    v55Flatten (positiveReflection i x) =
      (intMatrixToReal (pinReflect ⟨i.val, by omega⟩)).mulVec
        (v55Flatten x) := by
  funext k
  rw [pinReflectReal_mulVec]
  fin_cases i <;> fin_cases k <;>
    simp [v55Flatten, positiveReflection]

end InfoGeometry.Clifford.Clifford55
