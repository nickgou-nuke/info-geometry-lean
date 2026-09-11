import Mathlib.Algebra.Group.TypeTags.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-!
# Discrete Power / Moment Grade Readout

This module formalizes the algebraic discrete power grading (moment) readout:

$$k \mapsto X^k$$

represented genuinely as a monoid homomorphism from the additive monoid of degrees
$(\mathbb{N}, +)$ into the multiplicative monoid $(A, \cdot)$:

$$\text{powerCharacter} : \text{Multiplicative } \mathbb{N} \to* A$$

satisfying

$$\text{powerCharacter}(k + \ell) = \text{powerCharacter}(k) \cdot \text{powerCharacter}(\ell).$$

## Key Constructions:

1. **`MellinGradeReadout {A : Type*} [Monoid A] (X : A)`**:
   Structure packaging `powerCharacter : Multiplicative ℕ →* A` with
   `powerCharacter_apply : ∀ k, powerCharacter (ofAdd k) = X ^ k`.

2. **Canonical Constructor `powerCharacterOfElement (X : A)`**:
   Produces the unique canonical `MellinGradeReadout X` for any element $X$ of a monoid $A$.

3. **Periodicity & Reduction Lemmas**:
   - `powerCharacter_add`: $\Phi(k + \ell) = \Phi(k) \Phi(\ell)$ via `pow_add`.
   - `powerCharacter_involution_periodic`: for $X^2 = 1$, $\Phi(k + 2) = \Phi(k)$.
   - `powerCharacter_npotent_step`: for $X^n = X$, $\Phi(k + n - 1) = \Phi(k)$ for $k \ge 1$.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.DiscretePowerGradeReadout

open Multiplicative

/-! ## 1. Power Character Structure -/

/-- Discrete power character representing the grading/moment action of an element $X \in A$. -/
structure MellinGradeReadout {A : Type*} [Monoid A] (X : A) where
  /-- Monoid homomorphism from $(\mathbb{N}, +)$ to $(A, \cdot)$. -/
  powerCharacter : Multiplicative ℕ →* A
  /-- Character evaluation matches the discrete powers $X^k$. -/
  powerCharacter_apply : ∀ (k : ℕ), powerCharacter (ofAdd k) = X ^ k

/-- Evaluates the power character at degree $k \in \mathbb{N}$. -/
def MellinGradeReadout.eval {A : Type*} [Monoid A] {X : A}
    (M : MellinGradeReadout X) (k : ℕ) : A :=
  M.powerCharacter (ofAdd k)

theorem MellinGradeReadout.eval_eq {A : Type*} [Monoid A] {X : A}
    (M : MellinGradeReadout X) (k : ℕ) :
    M.eval k = X ^ k :=
  M.powerCharacter_apply k

@[simp]
theorem MellinGradeReadout.eval_zero {A : Type*} [Monoid A] {X : A}
    (M : MellinGradeReadout X) :
    M.eval 0 = 1 := by
  rw [MellinGradeReadout.eval_eq, pow_zero]

@[simp]
theorem MellinGradeReadout.eval_one {A : Type*} [Monoid A] {X : A}
    (M : MellinGradeReadout X) :
    M.eval 1 = X := by
  rw [MellinGradeReadout.eval_eq, pow_one]

theorem MellinGradeReadout.eval_add {A : Type*} [Monoid A] {X : A}
    (M : MellinGradeReadout X) (k l : ℕ) :
    M.eval (k + l) = M.eval k * M.eval l := by
  rw [MellinGradeReadout.eval_eq, MellinGradeReadout.eval_eq, MellinGradeReadout.eval_eq, pow_add]

/-! ## 2. Canonical Construction for any Element -/

/-- 🏆 THEOREM: Canonical discrete power character for any element $X$ in a monoid $A$. -/
def powerCharacterOfElement {A : Type*} [Monoid A] (X : A) :
    MellinGradeReadout X where
  powerCharacter := {
    toFun := fun k => X ^ (toAdd k)
    map_one' := by
      dsimp
      exact pow_zero X
    map_mul' := by
      intro s t
      dsimp
      exact pow_add X (toAdd s) (toAdd t)
  }
  powerCharacter_apply := by
    intro k
    rfl

/-! ## 3. Periodicity Theorems -/

/-- For an involution $X^2 = 1$, the power character has period 2. -/
theorem powerCharacter_involution_periodic {A : Type*} [Monoid A] {X : A}
    (hX : X ^ 2 = 1) (M : MellinGradeReadout X) (k : ℕ) :
    M.eval (k + 2) = M.eval k := by
  rw [MellinGradeReadout.eval_add, MellinGradeReadout.eval_eq M 2, hX, mul_one]

/-- For an $n$-potent element $X^n = X$, powers satisfy $X^{k+n-1} = X^k$ for all $k \ge 1$. -/
theorem powerCharacter_npotent_step {A : Type*} [Monoid A] {X : A} {n : ℕ}
    (hX : X ^ n = X) (_hn : 2 ≤ n) (M : MellinGradeReadout X) (k : ℕ) (hk : 1 ≤ k) :
    M.eval (k + (n - 1)) = M.eval k := by
  have hsplit : k + (n - 1) = (k - 1) + n := by omega
  rw [hsplit, MellinGradeReadout.eval_add, MellinGradeReadout.eval_eq M n, hX]
  rw [MellinGradeReadout.eval_eq, MellinGradeReadout.eval_eq, ← pow_succ, Nat.sub_add_cancel hk]

end InfoGeometry.Canonical.DiscretePowerGradeReadout
