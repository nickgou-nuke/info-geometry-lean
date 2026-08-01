import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SupergradedChiralSuperchargeBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Supergraded Lie Algebra Anti-Commutator {A, B} = A * B + B * A. -/
def superAntiCommutator {A : Type*} [Ring A] (a b : A) : A :=
  a * b + b * a

/-- **Theorem**: Supercharge Anti-Commutator Self-Relation {Q, Q} = 2 * Q². -/
theorem supercharge_anti_commute_self {A : Type*} [Ring A] (Q : A) :
    superAntiCommutator Q Q = 2 * (Q * Q) := by
  dsimp [superAntiCommutator]
  noncomm_ring

/-- **Theorem**: Nilpotent Supercharge Self-Anti-Commutator Vanishing (Q² = 0 ⟹ {Q, Q} = 0). -/
theorem supercharge_nilpotent_anti_commute_zero {A : Type*} [Ring A] (Q : A) (hQ : Q * Q = 0) :
    superAntiCommutator Q Q = 0 := by
  rw [supercharge_anti_commute_self, hQ, mul_zero]

/-- **Theorem**: Native Mathlib Clifford Involute Parity Reflection on Fermionic Supercharge.
    For any fermionic vector generator v in CliffordAlgebra Q, involute(ι(v)) = - ι(v). -/
theorem clifford_fermionic_supercharge_parity (Q : QuadraticForm R V) (v : V) :
    CliffordAlgebra.involute (CliffordAlgebra.ι Q v) = - CliffordAlgebra.ι Q v :=
  CliffordAlgebra.involute_ι v

end InfoGeometry.Canonical.SupergradedChiralSuperchargeBridge
