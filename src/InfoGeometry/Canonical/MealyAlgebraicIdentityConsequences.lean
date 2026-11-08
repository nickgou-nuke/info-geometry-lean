import Mathlib.Algebra.Order.Field.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Linarith

namespace InfoGeometry.Canonical

/-!
# Algebraic consequences of a Mealy-type identity

This owner deliberately does not package the geometric identity as structure
data.  It records only the scalar consequences that are valid once an actual
octonionic owner supplies the identity and the sign condition.
-/

theorem mealy_phi_sq_ge_one_of_identity
    (phiSq q : ℚ)
    (h_identity : phiSq = 1 - (1 / 4 : ℚ) * q)
    (h_nonpos : q ≤ 0) :
    1 ≤ phiSq := by
  linarith

theorem mealy_equality_iff_norm_zero_of_identity
    (phiSq q : ℚ)
    (h_identity : phiSq = 1 - (1 / 4 : ℚ) * q) :
    phiSq = 1 ↔ q = 0 := by
  constructor <;> intro h
  · linarith
  · linarith

theorem mealy_algebraic_identity_consequences
    (phiSq q : ℚ)
    (h_identity : phiSq = 1 - (1 / 4 : ℚ) * q)
    (h_nonpos : q ≤ 0) :
    (1 ≤ phiSq) ∧ (phiSq = 1 ↔ q = 0) :=
  ⟨mealy_phi_sq_ge_one_of_identity phiSq q h_identity h_nonpos,
    mealy_equality_iff_norm_zero_of_identity phiSq q h_identity⟩

end InfoGeometry.Canonical
