import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

/-!
# InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge

Finite Celik--Kocak endpoint lane:

`V_n -> F_n -> Cl_{2n} -> Pauli tensor-product matrices`.

The concrete matrix identification is carried by the `pauli_tensor_law` witness
from `FiniteCantorPauliBridge`; this file separates that finite matrix owner
surface from the infinite fractal/Fock and metric-graph lanes.
-/

noncomputable section

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

/-- The Pauli tensor-product matrix law carried by this finite owner lane. -/
@[rep_depth operator]
def pauli_tensor_law_statement : Prop :=
  B.pauli_tensor_law

end FiniteCantorPauliMatrixBridge

/-- Packaged owner for the finite Cantor-Pauli matrix lane. -/
@[rep_depth operator]
structure FiniteCantorPauliMatrixOwner where
  n : ℕ
  Mat : Type
  instRing : Ring Mat
  bridge : @FiniteCantorPauliBridge n Mat instRing

/-- Owner target for the finite Cantor-Pauli matrix bridge. -/
def FiniteCantorPauliMatrixBridgeTarget : Prop :=
  Nonempty FiniteCantorPauliMatrixOwner

/-- Constructor for the finite Cantor-Pauli matrix owner target. -/
@[rep_depth operator]
theorem constructFiniteCantorPauliMatrixBridgeTarget
    {n : ℕ} {Mat : Type} [Ring Mat]
    (B : FiniteCantorPauliBridge n Mat) :
    FiniteCantorPauliMatrixBridgeTarget := by
  exact ⟨{ n := n, Mat := Mat, instRing := inferInstance, bridge := B }⟩

end InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge
