import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Clifford.Cl11Matrix

/-!
# InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge

Finite Celik--Kocak endpoint lane:

`V_n -> F_n -> Cl_{2n} -> Pauli tensor-product matrices`.

The concrete matrix identification is theorem-backed in the `n = 1` base case
and the finite bridge facts are re-exported here.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge

open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge


/-! ## 1. The `n = 1` matrix base case -/

open InfoGeometry.Clifford.Cl11Matrix

/-- The paper's first finite Pauli pair in the `Cl(1,1)` matrix model. -/
@[rep_depth operator]
noncomputable def cl11PauliBridge : Fin 2 → Mat2 := fun i =>
  match i with
  | ⟨0, _⟩ => Eplus
  | ⟨1, _⟩ => J1

@[rep_depth operator]
theorem cl11PauliBridge_sq
    (i : Fin 2) :
    cl11PauliBridge i * cl11PauliBridge i = 1 := by
  fin_cases i
  · simpa [cl11PauliBridge, Eplus] using Eplus_sq
  · simpa [cl11PauliBridge, J1] using J1_sq

@[rep_depth operator]
theorem cl11PauliBridge_anticomm
    {i j : Fin 2} (hij : i ≠ j) :
    cl11PauliBridge i * cl11PauliBridge j =
      -(cl11PauliBridge j * cl11PauliBridge i) := by
  fin_cases i <;> fin_cases j <;> simp [cl11PauliBridge, Eplus, J1]
  · exact False.elim (hij rfl)
  · exact False.elim (hij rfl)

/-- The `n = 1` finite Cantor-Pauli representation is theorem-backed. -/
@[rep_depth operator]
theorem cl11PauliBridge_target :
    cl11PauliBridge ⟨0, by decide⟩ = Eplus ∧
      cl11PauliBridge ⟨1, by decide⟩ = J1 ∧
      (∀ i : Fin (2 * 1),
        cl11PauliBridge i * cl11PauliBridge i = 1) ∧
      (∀ {i j : Fin (2 * 1)}, i ≠ j →
        cl11PauliBridge i * cl11PauliBridge j +
          cl11PauliBridge j * cl11PauliBridge i = 0) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i
    exact cl11PauliBridge_sq i
  · intro i j hij
    rw [cl11PauliBridge_anticomm hij]
    simp

end InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge
