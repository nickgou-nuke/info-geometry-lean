import Mathlib.NumberTheory.DirichletCharacter.Basic
import InfoGeometry.Arithmetic.FiniteCyclotomicCharacterSupertraceBridge

/-!
# Native Dirichlet-character finite supertrace

This is the native-character specialization of the generic finite
Möbius/character factorization.  The Möbius coefficient remains the
squarefree fermionic sign; the Dirichlet character supplies an independent
modular weight.  No Galois realization or infinite `L`-function is asserted.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.FiniteDirichletCharacterSupertraceBridge

open Finset
open InfoGeometry.Arithmetic.FiniteCyclotomicCharacterSupertraceBridge

def dirichletWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q)

@[simp] theorem dirichletWeight_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    dirichletWeight χ 1 = 1 := by
  simp [dirichletWeight]

theorem dirichletWeight_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (a b : ℕ) :
    dirichletWeight χ (a * b) = dirichletWeight χ a * dirichletWeight χ b := by
  simp [dirichletWeight, map_mul]

def dirichletWeightMonoidHom {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ →* ℂ where
  toFun := dirichletWeight χ
  map_one' := dirichletWeight_one χ
  map_mul' := dirichletWeight_mul χ

theorem finite_dirichlet_character_mobius_supertrace
    {q : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (χ : DirichletCharacter ℂ q) (w : ℕ → ℂ) :
    (∏ p ∈ P, (1 - dirichletWeight χ p * w p)) =
      ∑ S ∈ P.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℂ) *
          dirichletWeight χ (∏ p ∈ S, p) * ∏ p ∈ S, w p := by
  exact finite_character_mobius_supertrace P hprime (dirichletWeight χ) w
    (dirichletWeight_one χ) (dirichletWeight_mul χ)

theorem finite_dirichlet_character_mobius_supertrace_monoidHom
    {q : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (χ : DirichletCharacter ℂ q) (w : ℕ → ℂ) :
    (∏ p ∈ P, (1 - dirichletWeight χ p * w p)) =
      ∑ S ∈ P.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℂ) *
          dirichletWeight χ (∏ p ∈ S, p) * ∏ p ∈ S, w p := by
  simpa [dirichletWeightMonoidHom] using
    (finite_character_mobius_supertrace_monoidHom
      P hprime (dirichletWeightMonoidHom χ) w)

end InfoGeometry.Arithmetic.FiniteDirichletCharacterSupertraceBridge
