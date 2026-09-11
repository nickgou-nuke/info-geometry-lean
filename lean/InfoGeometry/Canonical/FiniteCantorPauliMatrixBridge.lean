import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- Finite Cantor endpoint functions, indexed by binary addresses of length `n`. -/
abbrev EndpointFunctionSpace (n : ℕ) :=
  FiniteCantorFunctionSpace n

/-- Public finite Pauli matrix bridge alias. -/
abbrev FiniteCantorPauliMatrixBridge
    (n : ℕ)
    (Mat : Type*) [Ring Mat] :=
  FiniteCantorPauliBridge n Mat

namespace FiniteCantorPauliMatrixBridge

variable {n : ℕ} {Mat : Type*} [Ring Mat]
variable (B : FiniteCantorPauliMatrixBridge n Mat)

/-- Re-export: finite Clifford generators square to one. -/
@[rep_depth operator]
theorem psiGamma_sq (i : Fin (2 * n)) :
    B.psiGamma i * B.psiGamma i = 1 :=
  B.clifford_sq i

/-- Re-export: distinct finite Clifford generators anticommute. -/
@[rep_depth operator]
theorem psiGamma_anticomm {i j : Fin (2 * n)} (hij : i ≠ j) :
    B.psiGamma i * B.psiGamma j + B.psiGamma j * B.psiGamma i = 0 := by
  rw [B.clifford_anticomm i j hij]
  simp

end FiniteCantorPauliMatrixBridge

/-! ## 1. The `n = 1` matrix base case -/

open InfoGeometry.Clifford.Cl11Matrix

/-- The paper's first finite Pauli pair in the `Cl(1,1)` matrix model. -/
@[rep_depth operator]
noncomputable def cl11PauliBridge : FiniteCantorPauliBridge 1 Mat2 where
  psiGamma := fun i =>
    match i with
    | ⟨0, _⟩ => Eplus
    | ⟨1, _⟩ => J1
  clifford_sq := by
    intro i
    fin_cases i
    · simpa [Eplus] using Eplus_sq
    · simpa [J1] using J1_sq
  clifford_anticomm := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Eplus, J1]
    · exact False.elim (hij rfl)
    · exact False.elim (hij rfl)

/-- The `n = 1` finite Cantor-Pauli representation is theorem-backed. -/
@[rep_depth operator]
theorem cl11PauliBridge_target :
    (cl11PauliBridge).psiGamma ⟨0, by decide⟩ = Eplus ∧
      (cl11PauliBridge).psiGamma ⟨1, by decide⟩ = J1 ∧
      (∀ i : Fin (2 * 1),
        (cl11PauliBridge).psiGamma i * (cl11PauliBridge).psiGamma i = 1) ∧
      (∀ {i j : Fin (2 * 1)}, i ≠ j →
        (cl11PauliBridge).psiGamma i * (cl11PauliBridge).psiGamma j +
          (cl11PauliBridge).psiGamma j * (cl11PauliBridge).psiGamma i = 0) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i
    exact (cl11PauliBridge).clifford_sq i
  · intro i j hij
    simpa using (FiniteCantorPauliMatrixBridge.psiGamma_anticomm cl11PauliBridge hij)

/-- The `n = 1` finite Cantor-Pauli bridge recovers the first paper generator. -/
@[rep_depth operator]
theorem cl11PauliBridge_psiGamma_zero :
    (cl11PauliBridge).psiGamma ⟨0, by decide⟩ = Eplus := by
  rfl

/-- The `n = 1` finite Cantor-Pauli bridge recovers the second paper generator. -/
@[rep_depth operator]
theorem cl11PauliBridge_psiGamma_one :
    (cl11PauliBridge).psiGamma ⟨1, by decide⟩ = J1 := by
  rfl

/-- The `n = 1` matrix model decomposes in the Pauli basis. -/
@[rep_depth operator]
theorem cl11PauliBridge_mat2_decompose (M : Mat2) :
    M =
      (InfoGeometry.Clifford.Cl11Matrix.alpha M) • (1 : Mat2) +
      (InfoGeometry.Clifford.Cl11Matrix.beta M) • Eplus +
      (InfoGeometry.Clifford.Cl11Matrix.gamma M) • Eminus +
      (InfoGeometry.Clifford.Cl11Matrix.delta M) • J1 :=
  InfoGeometry.Clifford.Cl11Matrix.mat2_decompose M

/-- The `Cl(1,1)` matrix equivalence is the paper's base isomorphism. -/
@[rep_depth operator]
noncomputable def cl11PauliBridge_equivMat :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 ≃ₐ[ℝ] Mat2 :=
  InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat

end InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge
