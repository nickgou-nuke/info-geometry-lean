import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace JordanLieMetriplectic

section Metriplectic

variable {A : Type*} [Ring A]

/-- Symmetric Jordan product over the associative algebra -/
def jordan_prod (a b : A) : A := a * b + b * a

/-- Anti-symmetric Lie bracket representing the symplectic structure -/
def lie_bracket (a b : A) : A := a * b - b * a

/-- Metriplectic Souriau equations bridging the Hamiltonian and dissipative brackets -/
def metriplectic_flow (f H S : A) : A :=
  lie_bracket f H + jordan_prod f S

/-- Rigorous decomposition of the associative product into Jordan and Lie components -/
theorem assoc_split (a b : A) : a * b + a * b = jordan_prod a b + lie_bracket a b := by
  dsimp [jordan_prod, lie_bracket]
  abel

end Metriplectic

end JordanLieMetriplectic
