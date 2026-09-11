import InfoGeometry.Algebra.InfiniteInductiveSUSY
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.InfiniteHestenesKrein

Finite-stage Hestenes/Krein transport in an algebraic infinite tower.

This file does not claim Tomita-Takesaki completion, unbounded modular theory,
or a concrete operator-algebraic standard form.  It records the algebraic
inductive skeleton that is already used elsewhere in the repository:

* a one-step bonding family;
* a compatible cone into a target ring;
* transported Hestenes/Krein relations at every finite stage;
* stage-independent readback through the compatible cone.

The underlying relations are the algebraic ones that the real Hestenes/Krein
modules already expose: a phase axis squaring to `-1`, a modular weight that
commutes with the generator, and the Krein self-adjointness relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.InfiniteHestenesKrein

open InfoGeometry.Algebra.InfiniteInductiveSUSY

universe u

section Tower

variable {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
variable {Limit : Type u} [Ring Limit]

/--
A stagewise Hestenes/Krein algebraic tower.

The tower carries the three basic real relations used throughout the Hestenes/
Krein modules:

* `phaseAxis² = -1`;
* `modularWeight` commutes with `modularGenerator`;
* `phaseAxis * modularGenerator * phaseAxis = modularGenerator`.
-/
structure HestenesKreinTower where
  /-- One-step bonding maps. -/
  bond : ∀ n : ℕ, Stage n →+* Stage (n + 1)
  /-- Compatible cone into a target ring. -/
  toLimit : ∀ n : ℕ, Stage n →+* Limit
  /-- Cone compatibility. -/
  hcone : CompatibleCone bond toLimit
  /-- Stagewise phase axis. -/
  phaseAxis : ∀ n : ℕ, Stage n
  /-- Stagewise modular weight. -/
  modularWeight : ∀ n : ℕ, Stage n
  /-- Stagewise modular generator. -/
  modularGenerator : ∀ n : ℕ, Stage n
  /-- Stage-zero phase-axis square law. -/
  phaseAxis_sq_zero : phaseAxis 0 * phaseAxis 0 = -(1 : Stage 0)
  /-- Stage-zero weight-generator commutation. -/
  modularWeight_comm_generator_zero :
    modularWeight 0 * modularGenerator 0 = modularGenerator 0 * modularWeight 0
  /-- Stage-zero Krein self-adjointness. -/
  generator_krein_selfadjoint_zero :
    phaseAxis 0 * modularGenerator 0 * phaseAxis 0 = modularGenerator 0
  /-- Phase-axis transport. -/
  phaseAxis_step : ∀ n : ℕ, bond n (phaseAxis n) = phaseAxis (n + 1)
  /-- Modular-weight transport. -/
  modularWeight_step : ∀ n : ℕ, bond n (modularWeight n) = modularWeight (n + 1)
  /-- Modular-generator transport. -/
  modularGenerator_step : ∀ n : ℕ, bond n (modularGenerator n) = modularGenerator (n + 1)

namespace HestenesKreinTower

variable (P : HestenesKreinTower (Stage := Stage) (Limit := Limit))

/-- The phase axis squares to `-1` at every finite stage. -/
theorem phaseAxis_square_all :
    ∀ n : ℕ, P.phaseAxis n * P.phaseAxis n = -(1 : Stage n) := by
  intro n
  induction n with
  | zero =>
      exact P.phaseAxis_sq_zero
  | succ n ih =>
      calc
        P.phaseAxis (n + 1) * P.phaseAxis (n + 1)
            = P.bond n (P.phaseAxis n) * P.bond n (P.phaseAxis n) := by
                rw [P.phaseAxis_step n]
        _ = P.bond n (P.phaseAxis n * P.phaseAxis n) := by
              rw [map_mul]
        _ = P.bond n (-(1 : Stage n)) := by
              rw [ih]
        _ = -(1 : Stage (n + 1)) := by
              simp

/-- The modular weight commutes with the modular generator at every stage. -/
theorem modularWeight_commutes_modularGenerator_all :
    ∀ n : ℕ,
      P.modularWeight n * P.modularGenerator n =
        P.modularGenerator n * P.modularWeight n := by
  intro n
  induction n with
  | zero =>
      exact P.modularWeight_comm_generator_zero
  | succ n ih =>
      calc
        P.modularWeight (n + 1) * P.modularGenerator (n + 1)
            = P.bond n (P.modularWeight n * P.modularGenerator n) := by
                simp [P.modularWeight_step n, P.modularGenerator_step n, map_mul]
        _ = P.bond n (P.modularGenerator n * P.modularWeight n) := by
              rw [ih]
        _ = P.modularGenerator (n + 1) * P.modularWeight (n + 1) := by
              simp [P.modularWeight_step n, P.modularGenerator_step n, map_mul]

/-- The phase axis is Krein self-adjoint at every stage. -/
theorem generator_kreinSelfadjoint_all :
    ∀ n : ℕ,
      P.phaseAxis n * P.modularGenerator n * P.phaseAxis n =
        P.modularGenerator n := by
  intro n
  induction n with
  | zero =>
      exact P.generator_krein_selfadjoint_zero
  | succ n ih =>
      calc
        P.phaseAxis (n + 1) * P.modularGenerator (n + 1) * P.phaseAxis (n + 1)
            = P.bond n (P.phaseAxis n * P.modularGenerator n * P.phaseAxis n) := by
                simp [P.phaseAxis_step n, P.modularGenerator_step n, map_mul, mul_assoc]
        _ = P.bond n (P.modularGenerator n) := by
              rw [ih]
        _ = P.modularGenerator (n + 1) := by
              rw [P.modularGenerator_step n]

/-- The phase axis has stage-independent image in the compatible target. -/
theorem phaseAxis_limit_image (n : ℕ) :
    P.toLimit n (P.phaseAxis n) = P.toLimit 0 (P.phaseAxis 0) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        P.toLimit (n + 1) (P.phaseAxis (n + 1))
            = P.toLimit (n + 1) (P.bond n (P.phaseAxis n)) := by
                rw [P.phaseAxis_step n]
        _ = P.toLimit n (P.phaseAxis n) := P.hcone n (P.phaseAxis n)
        _ = P.toLimit 0 (P.phaseAxis 0) := ih

/-- The modular weight has stage-independent image in the compatible target. -/
theorem modularWeight_limit_image (n : ℕ) :
    P.toLimit n (P.modularWeight n) = P.toLimit 0 (P.modularWeight 0) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        P.toLimit (n + 1) (P.modularWeight (n + 1))
            = P.toLimit (n + 1) (P.bond n (P.modularWeight n)) := by
                rw [P.modularWeight_step n]
        _ = P.toLimit n (P.modularWeight n) := P.hcone n (P.modularWeight n)
        _ = P.toLimit 0 (P.modularWeight 0) := ih

/-- The modular generator has stage-independent image in the compatible target. -/
theorem modularGenerator_limit_image (n : ℕ) :
    P.toLimit n (P.modularGenerator n) = P.toLimit 0 (P.modularGenerator 0) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        P.toLimit (n + 1) (P.modularGenerator (n + 1))
            = P.toLimit (n + 1) (P.bond n (P.modularGenerator n)) := by
                rw [P.modularGenerator_step n]
        _ = P.toLimit n (P.modularGenerator n) := P.hcone n (P.modularGenerator n)
        _ = P.toLimit 0 (P.modularGenerator 0) := ih

end HestenesKreinTower

end Tower

end InfoGeometry.Canonical.InfiniteHestenesKrein
