/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-!
# Finite Unitary-Group Matrix Wrapper (Radon–Nikodym Cocycle Naming Shadow)

`RadonNikodymCocycle n` here is a direct `abbrev` for `Matrix.unitaryGroup (Fin n) ℂ`
(a single time-independent unitary matrix). There is no time parameter `t`, no
modular automorphism flow `σ_t`, and no 1-cocycle equation `u(s+t) = u(s) σ_s(u(t))`.
For genuine Connes 1-cocycle formulations over operator flows, see
`InfoGeometry.Modular.ConnesCocycle`,
`InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle`, and
`InfoGeometry.Volume.ConnesCocycle`.
-/

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Type alias for `Matrix.unitaryGroup (Fin n) ℂ` (time-independent unitary matrix). -/
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

/-- Left unitarity identity `u* u = 1` for a unitary matrix in `M_n(ℂ)`. -/
theorem cocycle_unitary_left : u_star u * u_val u = 1 :=
  h_unitary_left u

/-- Right unitarity identity `u u* = 1` for a unitary matrix in `M_n(ℂ)`. -/
theorem cocycle_unitary_right : u_val u * u_star u = 1 :=
  h_unitary_right u

/-- Identity element `1` in `Matrix.unitaryGroup (Fin n) ℂ`. -/
def identityCocycle (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] : RadonNikodymCocycle n where
  val := 1
  property := by simp

/-- Value of `identityCocycle n` is the identity matrix `1`. -/
theorem identity_cocycle_val : u_val (identityCocycle n) = 1 := rfl

/-- Matrix group product `u12 * u23` in `Matrix.unitaryGroup (Fin n) ℂ`. -/
def cocycleComposition (u12 u23 : RadonNikodymCocycle n) : RadonNikodymCocycle n :=
  u12 * u23

/-- Associativity of unitary matrix multiplication: `(u12 * u23) * u34 = u12 * (u23 * u34)`. -/
theorem cocycle_chain_rule_assoc (u12 u23 u34 : RadonNikodymCocycle n) :
    u_val (cocycleComposition (cocycleComposition u12 u23) u34) =
    u_val (cocycleComposition u12 (cocycleComposition u23 u34)) := by
  simp [cocycleComposition, u_val, mul_assoc]

end RadonNikodymCocycle

end TomitaTakesakiCocycle
