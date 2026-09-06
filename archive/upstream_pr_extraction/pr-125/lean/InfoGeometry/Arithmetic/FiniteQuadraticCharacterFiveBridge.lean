import Mathlib.NumberTheory.LegendreSymbol.Basic
import InfoGeometry.Arithmetic.FiniteDirichletCharacterSupertraceBridge

/-!
# The quadratic character of the real subfield of `ℚ(ζ₅)`

`chi5` is the native Legendre character modulo `5`, viewed as a multiplicative
weight on `ℕ` with values in `ℂ`.  This owner records only the finite
Dirichlet-character facts needed by the μ·χ supertrace bridge; it does not
construct a cyclotomic field or identify a Galois group in Lean.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.FiniteQuadraticCharacterFiveBridge

open InfoGeometry.Arithmetic.FiniteCyclotomicCharacterSupertraceBridge

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def chi5 : ℕ →* ℂ := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact
    { toFun := fun n => (legendreSym 5 (n : ℤ) : ℂ)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Nat.cast_mul]
        rw [legendreSym.mul]
        norm_num }

@[simp] theorem chi5_apply (n : ℕ) :
    chi5 n = (legendreSym 5 (n : ℤ) : ℂ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rfl

theorem chi5_nonzero_residue_value {n : ℕ} (hn : (n : ZMod 5) ≠ 0) :
    chi5 n = 1 ∨ chi5 n = -1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases legendreSym.eq_one_or_neg_one (p := 5) (a := (n : ℤ)) hn with h | h
  · left
    simpa [chi5] using congrArg (fun z : ℤ => (z : ℂ)) h
  · right
    simpa [chi5] using congrArg (fun z : ℤ => (z : ℂ)) h

theorem chi5_mobius_supertrace
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p) (w : ℕ → ℂ) :
    (∏ p ∈ P, (1 - chi5 p * w p)) =
      ∑ S ∈ P.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℂ) *
          chi5 (∏ p ∈ S, p) * ∏ p ∈ S, w p := by
  exact finite_character_mobius_supertrace_monoidHom P hprime chi5 w

end InfoGeometry.Arithmetic.FiniteQuadraticCharacterFiveBridge
