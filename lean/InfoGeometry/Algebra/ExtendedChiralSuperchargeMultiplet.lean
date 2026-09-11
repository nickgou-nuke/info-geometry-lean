import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Extended chiral supercharge multiplets

This owner supplies the finite indexed carrier for `N` extended chiral
supercharges.  The closure laws are theorem hypotheses: the carrier itself
does not manufacture a super-Poincare or central-charge representation.
-/

noncomputable section

namespace InfoGeometry.Algebra.ExtendedChiralSuperchargeMultiplet

variable {N : ℕ} {A : Type*} [Ring A] [Algebra ℂ A]

structure Data (N : ℕ) where
  QL : Fin N → Fin 2 → A
  QR : Fin N → Fin 2 → A
  P : Fin 4 → A
  Z : Fin N → Fin N → A

def anticommutator (x y : A) : A := x * y + y * x

def epsilon (α β : Fin 2) : ℂ :=
  if α = 0 ∧ β = 1 then 1 else
    if α = 1 ∧ β = 0 then -1 else 0

def internalDelta (I J : Fin N) : ℂ := if I = J then 1 else 0

theorem epsilon_antisymm (α β : Fin 2) :
    epsilon α β = -epsilon β α := by
  fin_cases α <;> fin_cases β <;> simp [epsilon]

theorem delta_eq_zero_of_ne {I J : Fin N} (h : I ≠ J) :
    internalDelta I J = 0 := by
  simp [internalDelta, h]

@[simp] theorem epsilon_diagonal (α : Fin 2) :
    epsilon α α = 0 := by
  fin_cases α <;> simp [epsilon]

theorem mixed_off_diagonal_zero
    (M : Data (A := A) N)
    (h : ∀ (I J : Fin N) (α β : Fin 2),
      anticommutator (M.QL I α) (M.QR J β) =
        (2 : ℂ) • (internalDelta I J •
          (if α = 0 ∧ β = 0 then M.P 0 + M.P 3 else
           if α = 0 ∧ β = 1 then M.P 1 - Complex.I • M.P 2 else
           if α = 1 ∧ β = 0 then M.P 1 + Complex.I • M.P 2 else
             M.P 0 - M.P 3)))
    {I J : Fin N} (hIJ : I ≠ J) (α β : Fin 2) :
    anticommutator (M.QL I α) (M.QR J β) = 0 := by
  rw [h I J α β, delta_eq_zero_of_ne hIJ]
  simp

end InfoGeometry.Algebra.ExtendedChiralSuperchargeMultiplet
