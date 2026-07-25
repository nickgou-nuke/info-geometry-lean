import Mathlib.Tactic

/-!
# Finite q-commutator shadow for the Peirce-Witt lane

This module is the Lean twin of
`tools/sympy/parafermionic_q_commutator_shadow.py`.

It records only the elementary finite `2 × 2` matrix identities for the
canonical nilpotent Peirce-Witt slots:

* `U * D - q • (D * U) = E₊ - q • E₋`;
* `U * D - D * U = H`;
* `U * D + D * U = I`.

Honest scope: this is a finite matrix shadow.  It does not prove Cuntz
representation closure, braid/Yang-Baxter coherence, wallpaper forcing,
parafermionic field theory, or a global automorphism classification.
-/

namespace InfoGeometry.OperatorAlgebra.ParafermionicQCommutatorShadow

abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Matrix unit over `ℤ` in the `2 × 2` carrier. -/
def mUnit (i j : Fin 2) : M2Z :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- Upper nilpotent Peirce-Witt slot. -/
def U : M2Z :=
  mUnit 0 1

/-- Lower nilpotent Peirce-Witt slot. -/
def D : M2Z :=
  mUnit 1 0

/-- Positive Peirce idempotent. -/
def EPlus : M2Z :=
  mUnit 0 0

/-- Negative Peirce idempotent. -/
def EMinus : M2Z :=
  mUnit 1 1

/-- Hyperbolic grading shadow. -/
def H : M2Z :=
  EPlus - EMinus

/-- Explicit integer scalar multiplication on the finite matrix carrier. -/
def scaleZ (q : ℤ) (M : M2Z) : M2Z :=
  fun i j => q * M i j

@[simp] theorem scaleZ_apply (q : ℤ) (M : M2Z) (i j : Fin 2) :
    scaleZ q M i j = q * M i j :=
  rfl

/-- The upper Peirce-Witt slot is nilpotent. -/
theorem U_sq_zero : U * U = 0 := by
  decide

/-- The lower Peirce-Witt slot is nilpotent. -/
theorem D_sq_zero : D * D = 0 := by
  decide

/-- `U D` is the positive Peirce idempotent. -/
theorem U_mul_D : U * D = EPlus := by
  decide

/-- `D U` is the negative Peirce idempotent. -/
theorem D_mul_U : D * U = EMinus := by
  decide

/-- Finite q-commutator accounting identity. -/
theorem q_commutator_shadow (q : ℤ) :
    U * D - scaleZ q (D * U) = EPlus - scaleZ q EMinus := by
  rw [U_mul_D, D_mul_U]

/-- The ordinary commutator is the hyperbolic grading shadow. -/
theorem commutator_eq_H :
    U * D - D * U = H := by
  decide

/-- The ordinary anticommutator is the identity. -/
theorem anticommutator_eq_one :
    U * D + D * U = 1 := by
  decide

/-- Consolidated finite q-commutator shadow packet. -/
theorem parafermionic_q_commutator_shadow_packet (q : ℤ) :
    U * U = 0 ∧
      D * D = 0 ∧
      U * D = EPlus ∧
      D * U = EMinus ∧
      U * D - scaleZ q (D * U) = EPlus - scaleZ q EMinus ∧
      U * D - D * U = H ∧
      U * D + D * U = 1 := by
  exact ⟨U_sq_zero, D_sq_zero, U_mul_D, D_mul_U, q_commutator_shadow q,
    commutator_eq_H, anticommutator_eq_one⟩

end InfoGeometry.OperatorAlgebra.ParafermionicQCommutatorShadow
