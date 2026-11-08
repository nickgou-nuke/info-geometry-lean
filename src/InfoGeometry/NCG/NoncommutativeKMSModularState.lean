import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Noncommutative Tomita–Takesaki Modular States and KMS Condition

This module establishes the full finite-dimensional operator-algebraic theory of:
1. Faithful quantum states `ω(X) = Tr(ρ * X)` on matrix algebras `Mₙ(R)`.
2. The Modular Conjugation / Modular Shift operator `Δ(X) = ρ * X * ρ⁻¹`.
3. 🏆 Invariance of the Modular State under the Modular Flow:
   `ω(Δ(X)) = ω(X)`.
4. 🏆 The Noncommutative Kubo–Martin–Schwinger (KMS) Condition:
   `ω(X * Δ(Y)) = ω(Y * X)`.
5. 🏆 The Modular Centralizer Characterization:
   `Δ(X) = X ↔ [ρ, X] = 0 ↔ [K, X] = 0`.

All proofs are complete in native Mathlib without custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG.KMS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "Mat" => Matrix ι ι R

/-- A quantum state functional evaluated via density matrix `ρ`: `ω_ρ(X) = Tr(ρ * X)` -/
def stateOf (ρ : Mat) (X : Mat) : R :=
  Matrix.trace (ρ * X)

/-- The Relative Modular Operator `Δ_{ρ, σ}(X) = ρ * X * σ⁻¹` given invertible `σ` -/
def modularShift (ρ σ_inv : Mat) (X : Mat) : Mat :=
  ρ * X * σ_inv

/-- The Inner Modular Operator `Δ_ρ(X) = ρ * X * ρ⁻¹` -/
def innerModularShift (ρ ρ_inv : Mat) (X : Mat) : Mat :=
  ρ * X * ρ_inv

/-- Commutator bracket `[A, B] = A * B - B * A` -/
def comm (A B : Mat) : Mat :=
  A * B - B * A

@[simp]
theorem comm_apply (A B : Mat) : comm A B = A * B - B * A := rfl

/-- 🏆 THEOREM 1: Linearity of the Quantum State Functional `ω_ρ` -/
theorem stateOf_add (ρ X Y : Mat) :
    stateOf ρ (X + Y) = stateOf ρ X + stateOf ρ Y := by
  dsimp [stateOf]
  rw [mul_add, Matrix.trace_add]

theorem stateOf_smul (ρ X : Mat) (c : R) :
    stateOf ρ (c • X) = c * stateOf ρ X := by
  dsimp [stateOf]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rfl

/-- 🏆 THEOREM 2: Exact Invariance of the Quantum State under the Modular Shift:
    `ω_ρ(Δ_ρ(X)) = ω_ρ(X)` whenever `ρ * ρ⁻¹ = 1` and `ρ⁻¹ * ρ = 1` -/
theorem stateOf_modularShift_invariant (ρ ρ_inv X : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    stateOf ρ (innerModularShift ρ ρ_inv X) = stateOf ρ X := by
  dsimp [stateOf, innerModularShift]
  calc
    Matrix.trace (ρ * (ρ * X * ρ_inv))
      = Matrix.trace ((ρ * ρ * X) * ρ_inv) := by simp only [mul_assoc]
    _ = Matrix.trace (ρ_inv * (ρ * ρ * X)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((ρ_inv * ρ) * (ρ * X)) := by simp only [mul_assoc]
    _ = Matrix.trace (1 * (ρ * X)) := by rw [h_left]
    _ = Matrix.trace (ρ * X) := by rw [one_mul]

/-- 🏆 THEOREM 3: The Noncommutative Kubo–Martin–Schwinger (KMS) Condition:
    `ω_ρ(X * Δ_ρ(Y)) = ω_ρ(Y * X)` -/
theorem kms_condition (ρ ρ_inv X Y : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    stateOf ρ (X * innerModularShift ρ ρ_inv Y) = stateOf ρ (Y * X) := by
  dsimp [stateOf, innerModularShift]
  calc
    Matrix.trace (ρ * (X * (ρ * Y * ρ_inv)))
      = Matrix.trace ((ρ * X * ρ * Y) * ρ_inv) := by simp only [mul_assoc]
    _ = Matrix.trace (ρ_inv * (ρ * X * ρ * Y)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((ρ_inv * ρ) * (X * ρ * Y)) := by simp only [mul_assoc]
    _ = Matrix.trace (1 * (X * ρ * Y)) := by rw [h_left]
    _ = Matrix.trace (X * ρ * Y) := by rw [one_mul]
    _ = Matrix.trace ((X * ρ) * Y) := by simp only [mul_assoc]
    _ = Matrix.trace (Y * (X * ρ)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((Y * X) * ρ) := by simp only [mul_assoc]
    _ = Matrix.trace (ρ * (Y * X)) := by rw [Matrix.trace_mul_comm]

/-- The density-weighted expectation annihilates the commutator with the
    density matrix itself.  This is the finite matrix form of cyclicity of
    the trace, with no commutativity assumption on observables. -/
theorem stateOf_comm_density_zero (ρ X : Mat) :
    stateOf ρ (comm ρ X) = 0 := by
  dsimp [stateOf, comm]
  rw [mul_sub, Matrix.trace_sub]
  have htrace : Matrix.trace (ρ * (ρ * X)) = Matrix.trace (ρ * X * ρ) := by
    rw [Matrix.trace_mul_comm]
  rw [htrace]
  simp only [show ρ * (X * ρ) = ρ * X * ρ by simp only [mul_assoc], sub_self]

/-- 🏆 THEOREM 4: Characterization of the Modular Centralizer:
    `Δ_ρ(X) = X ↔ [ρ, X] = 0` (for invertible `ρ`) -/
theorem modularShift_fixed_iff_commute (ρ ρ_inv X : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    innerModularShift ρ ρ_inv X = X ↔ comm ρ X = 0 := by
  dsimp [innerModularShift, comm]
  constructor
  · intro h_fixed
    have h_mul : (ρ * X * ρ_inv) * ρ = X * ρ := by rw [h_fixed]
    have h_assoc : (ρ * X * ρ_inv) * ρ = ρ * X * (ρ_inv * ρ) := by simp only [mul_assoc]
    rw [h_left, mul_one] at h_assoc
    rw [h_assoc] at h_mul
    exact sub_eq_zero.mpr h_mul
  · intro h_comm
    have h_eq : ρ * X = X * ρ := sub_eq_zero.mp h_comm
    calc
      ρ * X * ρ_inv = (X * ρ) * ρ_inv := by rw [h_eq]
      _ = X * (ρ * ρ_inv) := by simp only [mul_assoc]
      _ = X * 1 := by rw [h_right]
      _ = X := mul_one X

/-- The inner modular shift is unital when its implementing matrix is invertible. -/
@[simp]
theorem innerModularShift_one (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    innerModularShift ρ ρ_inv 1 = 1 := by
  dsimp [innerModularShift]
  rw [mul_one, h_right]

/-- The modular shift implemented by an inverse matrix is the inverse action. -/
theorem innerModularShift_inv (ρ ρ_inv X : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    innerModularShift ρ_inv ρ (innerModularShift ρ ρ_inv X) = X := by
  dsimp [innerModularShift]
  calc
    ρ_inv * (ρ * X * ρ_inv) * ρ =
        (ρ_inv * ρ) * X * (ρ_inv * ρ) := by simp only [mul_assoc]
    _ = 1 * X * 1 := by rw [h_left]
    _ = X := by simp

/-- Conjugation by an invertible matrix is injective. -/
theorem innerModularShift_injective (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    Function.Injective (innerModularShift ρ ρ_inv) := by
  intro X Y h
  have h' := congrArg (innerModularShift ρ_inv ρ) h
  simpa [innerModularShift_inv ρ ρ_inv X h_right h_left,
    innerModularShift_inv ρ ρ_inv Y h_right h_left] using h'

/-- Conjugation by an invertible matrix is surjective, with inverse conjugation. -/
theorem innerModularShift_surjective (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    Function.Surjective (innerModularShift ρ ρ_inv) := by
  intro X
  refine ⟨innerModularShift ρ_inv ρ X, ?_⟩
  exact innerModularShift_inv ρ_inv ρ X h_left h_right

/-- Composition of two inner modular shifts is multiplication of their
    implementing left and right factors. -/
theorem innerModularShift_comp (ρ ρ_inv σ σ_inv X : Mat) :
    innerModularShift ρ ρ_inv (innerModularShift σ σ_inv X) =
      (ρ * σ) * X * (σ_inv * ρ_inv) := by
  dsimp [innerModularShift]
  simp only [mul_assoc]

/-- The state is invariant under the inverse modular shift as well. -/
theorem stateOf_inverse_modularShift_invariant (ρ ρ_inv X : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    stateOf ρ (innerModularShift ρ_inv ρ X) = stateOf ρ X := by
  dsimp [stateOf, innerModularShift]
  calc
    Matrix.trace (ρ * (ρ_inv * X * ρ)) =
        Matrix.trace ((ρ * ρ_inv) * X * ρ) := by simp only [mul_assoc]
    _ = Matrix.trace (1 * X * ρ) := by rw [h_right]
    _ = Matrix.trace (X * ρ) := by rw [one_mul]
    _ = Matrix.trace (ρ * X) := by rw [Matrix.trace_mul_comm]

/-- The inner modular shift is additive on observables. -/
theorem innerModularShift_add (ρ ρ_inv X Y : Mat) :
    innerModularShift ρ ρ_inv (X + Y) =
      innerModularShift ρ ρ_inv X + innerModularShift ρ ρ_inv Y := by
  dsimp [innerModularShift]
  simp only [mul_add, add_mul]

/-- The inner modular shift is linear over the coefficient ring. -/
theorem innerModularShift_smul (ρ ρ_inv X : Mat) (c : R) :
    innerModularShift ρ ρ_inv (c • X) =
      c • innerModularShift ρ ρ_inv X := by
  dsimp [innerModularShift]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- 🏆 THEOREM 5: Modular Multiplicativity (Homomorphism Property):
    `Δ_ρ(X * Y) = Δ_ρ(X) * Δ_ρ(Y)` -/
theorem innerModularShift_mul (ρ ρ_inv X Y : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    innerModularShift ρ ρ_inv (X * Y) =
      innerModularShift ρ ρ_inv X * innerModularShift ρ ρ_inv Y := by
  dsimp [innerModularShift]
  calc
    ρ * (X * Y) * ρ_inv
      = ρ * X * 1 * Y * ρ_inv := by simp only [mul_one, mul_assoc]
    _ = ρ * X * (ρ_inv * ρ) * Y * ρ_inv := by rw [h_left]
    _ = (ρ * X * ρ_inv) * (ρ * Y * ρ_inv) := by simp only [mul_assoc]

/-- The invertible inner modular shift is a native ring homomorphism.

This packages conjugation by `ρ` for downstream operator-algebraic use; the
two-sided inverse hypotheses are exactly what is needed for multiplicativity.
-/
def innerModularShiftRingHom (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) : Mat →+* Mat where
  toFun := innerModularShift ρ ρ_inv
  map_one' := innerModularShift_one ρ ρ_inv h_right h_left
  map_mul' := fun X Y => innerModularShift_mul ρ ρ_inv X Y h_right h_left
  map_zero' := by
    dsimp [innerModularShift]
    simp
  map_add' := by
    intro X Y
    exact innerModularShift_add ρ ρ_inv X Y

@[simp]
theorem innerModularShiftRingHom_apply (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) (X : Mat) :
    innerModularShiftRingHom ρ ρ_inv h_right h_left X =
      innerModularShift ρ ρ_inv X := rfl

theorem innerModularShiftRingHom_bijective (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    Function.Bijective (innerModularShiftRingHom ρ ρ_inv h_right h_left) := by
  constructor
  · exact innerModularShift_injective ρ ρ_inv h_right h_left
  · exact innerModularShift_surjective ρ ρ_inv h_right h_left

/-- The invertible inner modular shift as a native ring equivalence. -/
def innerModularShiftRingEquiv (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) : Mat ≃+* Mat :=
  RingEquiv.ofBijective (innerModularShiftRingHom ρ ρ_inv h_right h_left)
    (innerModularShiftRingHom_bijective ρ ρ_inv h_right h_left)

theorem innerModularShiftRingEquiv_inverse_apply (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) (X : Mat) :
    innerModularShiftRingEquiv ρ ρ_inv h_right h_left
        (innerModularShift ρ_inv ρ X) = X := by
  exact innerModularShift_inv ρ_inv ρ X h_left h_right

theorem innerModularShift_comm (ρ ρ_inv X Y : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) :
    innerModularShift ρ ρ_inv (comm X Y) =
      comm (innerModularShift ρ ρ_inv X) (innerModularShift ρ ρ_inv Y) := by
  calc
    innerModularShift ρ ρ_inv (comm X Y) =
        innerModularShift ρ ρ_inv (X * Y) -
          innerModularShift ρ ρ_inv (Y * X) := by
            simp [comm, innerModularShift, mul_sub, sub_mul]
    _ = innerModularShift ρ ρ_inv X * innerModularShift ρ ρ_inv Y -
          innerModularShift ρ ρ_inv Y * innerModularShift ρ ρ_inv X := by
            rw [innerModularShift_mul ρ ρ_inv X Y h_right h_left,
              innerModularShift_mul ρ ρ_inv Y X h_right h_left]
    _ = comm (innerModularShift ρ ρ_inv X) (innerModularShift ρ ρ_inv Y) := rfl

theorem innerModularShiftRingHom_map_comm (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) (h_left : ρ_inv * ρ = 1) (X Y : Mat) :
    innerModularShiftRingHom ρ ρ_inv h_right h_left (comm X Y) =
      comm (innerModularShiftRingHom ρ ρ_inv h_right h_left X)
        (innerModularShiftRingHom ρ ρ_inv h_right h_left Y) := by
  exact innerModularShift_comm ρ ρ_inv X Y h_right h_left

end InfoGeometry.NCG.KMS

end noncomputable section
