import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace TomitaTakesakiCocycle

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Unitary Connes Radon-Nikodym Cocycle Element u(t) = (Dψ : Dφ)_t in M_n(ℂ). -/
structure RadonNikodymCocycle (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  u_val : Matrix (Fin n) (Fin n) ℂ
  u_star : Matrix (Fin n) (Fin n) ℂ
  h_unitary_left : u_star * u_val = 1
  h_unitary_right : u_val * u_star = 1

namespace RadonNikodymCocycle

variable (u : RadonNikodymCocycle n)

/-- **Theorem**: Radon-Nikodym Cocycle Unitarity Identity u* u = 1. -/
theorem cocycle_unitary_left : u.u_star * u.u_val = 1 :=
  u.h_unitary_left

/-- **Theorem**: Radon-Nikodym Cocycle Right Unitarity Identity u u* = 1. -/
theorem cocycle_unitary_right : u.u_val * u.u_star = 1 :=
  u.h_unitary_right

/-- Identity Cocycle (Dφ : Dφ)_t = 1. -/
def identityCocycle (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] : RadonNikodymCocycle n where
  u_val := 1
  u_star := 1
  h_unitary_left := mul_one 1
  h_unitary_right := mul_one 1

/-- **Theorem**: Identity Cocycle Value is Matrix Identity 1. -/
theorem identity_cocycle_val : (identityCocycle n).u_val = 1 := rfl

/-- Composition of Connes Radon-Nikodym Cocycles u₁₂ * u₂₃. -/
def cocycleComposition (u12 u23 : RadonNikodymCocycle n) : RadonNikodymCocycle n where
  u_val := u12.u_val * u23.u_val
  u_star := u23.u_star * u12.u_star
  h_unitary_left := by
    calc (u23.u_star * u12.u_star) * (u12.u_val * u23.u_val)
      _ = u23.u_star * (u12.u_star * u12.u_val) * u23.u_val := by noncomm_ring
      _ = u23.u_star * 1 * u23.u_val := by rw [u12.h_unitary_left]
      _ = u23.u_star * u23.u_val := by noncomm_ring
      _ = 1 := u23.h_unitary_left
  h_unitary_right := by
    calc (u12.u_val * u23.u_val) * (u23.u_star * u12.u_star)
      _ = u12.u_val * (u23.u_val * u23.u_star) * u12.u_star := by noncomm_ring
      _ = u12.u_val * 1 * u12.u_star := by rw [u23.h_unitary_right]
      _ = u12.u_val * u12.u_star := by noncomm_ring
      _ = 1 := u12.h_unitary_right

/-- **Theorem**: Connes Radon-Nikodym Cocycle Chain Rule Composition Associativity:
    (u12 * u23) * u34 = u12 * (u23 * u34). -/
theorem cocycle_chain_rule_assoc (u12 u23 u34 : RadonNikodymCocycle n) :
    (cocycleComposition (cocycleComposition u12 u23) u34).u_val =
    (cocycleComposition u12 (cocycleComposition u23 u34)).u_val := by
  dsimp [cocycleComposition]
  noncomm_ring

end RadonNikodymCocycle

end TomitaTakesakiCocycle
