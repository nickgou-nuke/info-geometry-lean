import Mathlib

/-!
# Finite Clifford-braiding central-core packet

This file mirrors `tools/sympy/clifford_braiding_center.py`.

It proves only finite `2 × 2` integer-matrix facts:
* `J² = -I` for a concrete square-root of central inversion;
* `E² = I` and `EJ + JE = 0` for a split `Cl(1,1)` atom;
* conjugation by `J` preserves the central core `{+I, -I}`;
* the finite pseudoscalar `EJ` squares to `I`.

It does **not** prove a general Clifford-module braiding theorem, anyon braid
statistics, Lorentz/Spin/Pin representation theory, parafermion CFT, super-Kähler geometry,
Cuntz-boundary losslessness, metric-symplectic emergence, or infinite categorical
closure.
-/

namespace InfoGeometry.Algebra.CliffordBraidingTheorem

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- The discrete central signs tracked by the finite packet. -/
inductive CentralCore : Type
  | pos : CentralCore
  | neg : CentralCore
  deriving DecidableEq, Repr

/-- The concrete central matrix attached to a sign. -/
def centralMatrix : CentralCore → Mat2Z
  | CentralCore.pos => 1
  | CentralCore.neg => -1

/-- Concrete square-root of the central inversion. -/
def J : Mat2Z :=
  ![![0, 1], ![-1, 0]]

/-- Split `Cl(1,1)` partner with positive square. -/
def E : Mat2Z :=
  ![![1, 0], ![0, -1]]

/-- Finite split pseudoscalar. -/
def P : Mat2Z := E * J

@[simp]
theorem J_sq : J * J = -(1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply]

@[simp]
theorem J_inv_left : (-J) * J = (1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply]

@[simp]
theorem J_inv_right : J * (-J) = (1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply]

@[simp]
theorem E_sq : E * E = (1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E, Matrix.mul_apply]

@[simp]
theorem E_anticomm_J : E * J + J * E = (0 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E, J, Matrix.mul_apply]

@[simp]
theorem pseudoscalar_sq : P * P = (1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, E, J, Matrix.mul_apply]

/-- Internal conjugation by the finite braid-root matrix `J`. -/
def conjByJ (A : Mat2Z) : Mat2Z := J * A * (-J)

@[simp]
theorem conjByJ_one : conjByJ (1 : Mat2Z) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjByJ, J, Matrix.mul_apply]

@[simp]
theorem conjByJ_neg_one : conjByJ (-(1 : Mat2Z)) = -(1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjByJ, J, Matrix.mul_apply]

/-- Conjugation by `J` preserves each element of the central `{+I,-I}` core. -/
theorem central_core_preserved_by_J_conj (z : CentralCore) :
    conjByJ (centralMatrix z) = centralMatrix z := by
  cases z <;> simp [centralMatrix]

/-- Central inversion commutes with the concrete braid-root matrix `J`. -/
theorem central_inversion_commutes_with_J :
    J * (-(1 : Mat2Z)) = (-(1 : Mat2Z)) * J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply]

/-- A structure encoding the core properties of the finite Clifford braiding packet,
ensuring we don't just leave these as loosely collected facts but package them properly. -/
structure FiniteCliffordPacket where
  J : Mat2Z
  E : Mat2Z
  P : Mat2Z
  J_sq : J * J = -1
  E_sq : E * E = 1
  E_anticomm_J : E * J + J * E = 0
  P_def : P = E * J
  P_sq : P * P = 1
  central_core_preserved : ∀ z : CentralCore, J * (centralMatrix z) * (-J) = centralMatrix z

/-- Concrete instantiation of the finite Clifford braiding packet to prove it is non-vacuous. -/
def concreteFiniteCliffordPacket : FiniteCliffordPacket where
  J := J
  E := E
  P := P
  J_sq := J_sq
  E_sq := E_sq
  E_anticomm_J := E_anticomm_J
  P_def := rfl
  P_sq := pseudoscalar_sq
  central_core_preserved := central_core_preserved_by_J_conj

/-- Summary theorem for backward compatibility. -/
theorem finite_clifford_braiding_center_packet :
    J * J = -(1 : Mat2Z) ∧
      E * E = (1 : Mat2Z) ∧
      E * J + J * E = (0 : Mat2Z) ∧
      P * P = (1 : Mat2Z) ∧
      (∀ z : CentralCore, conjByJ (centralMatrix z) = centralMatrix z) := by
  exact ⟨J_sq, E_sq, E_anticomm_J, pseudoscalar_sq, central_core_preserved_by_J_conj⟩

end InfoGeometry.Algebra.CliffordBraidingTheorem
