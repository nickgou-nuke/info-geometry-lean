import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic

/-!
# InfoGeometry.Canonical.KnillLaflammeQEC

Concrete finite-dimensional Knill–Laflamme quantum error correction.
Full native proofs with zero `sorry`s.
-/

noncomputable section

namespace InfoGeometry.Canonical.KnillLaflammeQEC

open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R] [StarRing R]

/-! ## 1. Code space -/

/-- A quantum error-correcting code is a subspace of the ambient Hilbert space.
    We represent it by its orthogonal projection P_C.
-/
structure QuantumCode (n : Type*) [Fintype n] (R : Type*) [CommRing R] [StarRing R] where
  /-- The code space projector P_C (idempotent and self-adjoint). -/
  P_C : Matrix n n R
  /-- P_C is a projector: P_C^2 = P_C. -/
  h_proj : P_C * P_C = P_C
  /-- P_C is self-adjoint: P_Cᴴ = P_C. -/
  h_selfAdjoint : P_Cᴴ = P_C

/-- A density matrix ρ is in the code subspace if P_C ρ P_C = ρ. -/
def IsCodeState (code : QuantumCode n R) (ρ : Matrix n n R) : Prop :=
  code.P_C * ρ * code.P_C = ρ

/-! ## 2. Error operators -/

/-- A finite family of error operators {E_a} on the ambient Hilbert space. -/
structure ErrorOperators (n : Type*) [Fintype n] (R : Type*) [CommRing R] [StarRing R] where
  carrier : Type*
  [fintypeCarrier : Fintype carrier]
  [decidableCarrier : DecidableEq carrier]
  E : carrier → Matrix n n R

attribute [instance] ErrorOperators.fintypeCarrier ErrorOperators.decidableCarrier

/-! ## 3. Knill–Laflamme condition -/

/-- The general Knill–Laflamme condition: P_C E_a† E_b P_C = α_{ab} • P_C. -/
def knillLaflammeCondition (code : QuantumCode n R) (errors : ErrorOperators n R) : Prop :=
  ∃ α : errors.carrier → errors.carrier → R,
    ∀ a b : errors.carrier,
      code.P_C * (errors.E a)ᴴ * errors.E b * code.P_C =
        α a b • code.P_C

/-- Orthogonal Knill–Laflamme condition where errors map to orthogonal syndrome spaces:
    P_C E_a† E_b P_C = δ_{ab} • P_C. -/
def orthogonalKnillLaflamme (code : QuantumCode n R) (errors : ErrorOperators n R) : Prop :=
  ∀ a b : errors.carrier,
    code.P_C * (errors.E a)ᴴ * errors.E b * code.P_C =
      (if a = b then (1 : R) else 0) • code.P_C

/-- The canonical quantum recovery channel for orthogonal error sets:
    R(σ) = ∑_a P_C E_a† σ E_a P_C. -/
def recoveryChannel (code : QuantumCode n R) (errors : ErrorOperators n R)
    (σ : Matrix n n R) : Matrix n n R :=
  ∑ a : errors.carrier, code.P_C * (errors.E a)ᴴ * σ * errors.E a * code.P_C

/-! ## 4. Main QEC Correction Theorems -/

/-- 
  MASTER QEC RECOVERY THEOREM:
  If the error operators satisfy the orthogonal Knill–Laflamme condition,
  then for every error E_k and every code state ρ (P_C ρ P_C = ρ),
  the recovery channel perfectly restores the state:
    recoveryChannel (E_k ρ E_k†) = ρ.
-/
theorem canCorrectErrors_orthogonal
    (code : QuantumCode n R) (errors : ErrorOperators n R)
    (hkl : orthogonalKnillLaflamme code errors)
    (k : errors.carrier) (ρ : Matrix n n R)
    (h_code : IsCodeState code ρ) :
    recoveryChannel code errors (errors.E k * ρ * (errors.E k)ᴴ) = ρ := by
  dsimp [recoveryChannel]
  have h_term (a : errors.carrier) :
      code.P_C * (errors.E a)ᴴ * (errors.E k * ρ * (errors.E k)ᴴ) * errors.E a * code.P_C =
        if a = k then ρ else 0 := by
    have h_assoc1 :
        code.P_C * (errors.E a)ᴴ * (errors.E k * ρ * (errors.E k)ᴴ) * errors.E a * code.P_C =
          (code.P_C * (errors.E a)ᴴ * errors.E k * code.P_C) * ρ *
            (code.P_C * (errors.E k)ᴴ * errors.E a * code.P_C) := by
      calc
        code.P_C * (errors.E a)ᴴ * (errors.E k * ρ * (errors.E k)ᴴ) * errors.E a * code.P_C
            = (code.P_C * (errors.E a)ᴴ * errors.E k) * ρ * ((errors.E k)ᴴ * errors.E a * code.P_C) := by
                simp only [mul_assoc]
        _ = (code.P_C * (errors.E a)ᴴ * errors.E k) * (code.P_C * ρ * code.P_C) * ((errors.E k)ᴴ * errors.E a * code.P_C) := by
                rw [h_code]
        _ = (code.P_C * (errors.E a)ᴴ * errors.E k * code.P_C) * ρ *
              (code.P_C * (errors.E k)ᴴ * errors.E a * code.P_C) := by
                simp only [mul_assoc]

    rw [h_assoc1]
    by_cases hak : a = k
    · subst hak
      have h1 := hkl a a
      simp only [if_true, one_smul] at h1
      rw [h1]
      rw [if_pos rfl]
      exact h_code
    · have h1 := hkl a k
      have h2 := hkl k a
      simp only [if_neg hak, zero_smul] at h1
      simp only [if_neg (Ne.symm hak), zero_smul] at h2
      rw [h1, h2, if_neg hak]
      simp only [zero_mul, mul_zero]

  have h_sum :
      (∑ a : errors.carrier, code.P_C * (errors.E a)ᴴ * (errors.E k * ρ * (errors.E k)ᴴ) * errors.E a * code.P_C) =
        ∑ a : errors.carrier, if a = k then ρ else 0 := by
    exact Finset.sum_congr rfl (fun a _ => h_term a)

  rw [h_sum]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

/-- Syndrome projectivity on orthogonal error subspaces. -/
theorem syndrome_orthogonal
    (code : QuantumCode n R) (errors : ErrorOperators n R)
    (hkl : orthogonalKnillLaflamme code errors)
    (a b : errors.carrier) (hab : a ≠ b) :
    code.P_C * (errors.E a)ᴴ * errors.E b * code.P_C = 0 := by
  have h := hkl a b
  simp [hab] at h
  exact h

/-! ## 5. Distance of a code -/

/-- The number of correctable error operators in the finite error set. -/
def codeErrorCapacity (errors : ErrorOperators n R) : ℕ :=
  Fintype.card errors.carrier

end InfoGeometry.Canonical.KnillLaflammeQEC
