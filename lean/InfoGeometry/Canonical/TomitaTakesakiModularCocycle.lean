import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
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
abbrev RadonNikodymCocycle (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] :=
  Matrix.unitaryGroup (Fin n) ℂ

namespace RadonNikodymCocycle

variable (u : RadonNikodymCocycle n)

def u_val : Matrix (Fin n) (Fin n) ℂ :=
  (u : Matrix (Fin n) (Fin n) ℂ)

def u_star : Matrix (Fin n) (Fin n) ℂ :=
  (u_val u).conjTranspose

theorem h_unitary_left : u_star u * u_val u = 1 := by
  change (u : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
      (u : Matrix (Fin n) (Fin n) ℂ) = 1
  exact Matrix.mem_unitaryGroup_iff'.mp u.2

theorem h_unitary_right : u_val u * u_star u = 1 := by
  change (u : Matrix (Fin n) (Fin n) ℂ) *
      (u : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1
  exact Matrix.mem_unitaryGroup_iff.mp u.2

/-- **Theorem**: Radon-Nikodym Cocycle Unitarity Identity u* u = 1. -/
theorem cocycle_unitary_left : u_star u * u_val u = 1 :=
  h_unitary_left u

/-- **Theorem**: Radon-Nikodym Cocycle Right Unitarity Identity u u* = 1. -/
theorem cocycle_unitary_right : u_val u * u_star u = 1 :=
  h_unitary_right u

/-- Identity Cocycle (Dφ : Dφ)_t = 1. -/
def identityCocycle (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] : RadonNikodymCocycle n where
  val := 1
  property := by simp

/-- **Theorem**: Identity Cocycle Value is Matrix Identity 1. -/
theorem identity_cocycle_val : u_val (identityCocycle n) = 1 := rfl

/-- Composition of Connes Radon-Nikodym Cocycles u₁₂ * u₂₃. -/
def cocycleComposition (u12 u23 : RadonNikodymCocycle n) : RadonNikodymCocycle n :=
  u12 * u23

/-- **Theorem**: Connes Radon-Nikodym Cocycle Chain Rule Composition Associativity:
    (u12 * u23) * u34 = u12 * (u23 * u34). -/
theorem cocycle_chain_rule_assoc (u12 u23 u34 : RadonNikodymCocycle n) :
    u_val (cocycleComposition (cocycleComposition u12 u23) u34) =
    u_val (cocycleComposition u12 (cocycleComposition u23 u34)) := by
  simp [cocycleComposition, u_val, mul_assoc]

end RadonNikodymCocycle

end TomitaTakesakiCocycle
