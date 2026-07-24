import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.FiniteSingleModeCAR

/-- One fermionic mode has two basis states: unoccupied/occupied. -/
abbrev OneModeState := Bool

/-- Complex wavefunctions on the one-mode Fock basis. -/
abbrev OneModeVec := OneModeState → ℂ

/-- One-mode annihilation operator: `c |0⟩ = 0`, `c |1⟩ = |0⟩`. -/
def ann (ψ : OneModeVec) : OneModeVec :=
  fun occ => if occ then 0 else ψ true

/-- One-mode creation operator: `c† |0⟩ = |1⟩`, `c† |1⟩ = 0`. -/
def cre (ψ : OneModeVec) : OneModeVec :=
  fun occ => if occ then ψ false else 0

/-- One-mode number operator `N = c† c`. -/
def num (ψ : OneModeVec) : OneModeVec := cre (ann ψ)

/-- One-mode identity operator. -/
def idOp (ψ : OneModeVec) : OneModeVec := ψ

/-- Operator addition on one-mode wavefunctions. -/
def opAdd (T U : OneModeVec → OneModeVec) : OneModeVec → OneModeVec :=
  fun ψ occ => T ψ occ + U ψ occ

/-- Operator composition. -/
def opComp (T U : OneModeVec → OneModeVec) : OneModeVec → OneModeVec :=
  fun ψ => T (U ψ)

@[simp] theorem ann_apply_false (ψ : OneModeVec) : ann ψ false = ψ true := by
  simp [ann]

@[simp] theorem ann_apply_true (ψ : OneModeVec) : ann ψ true = 0 := by
  simp [ann]

@[simp] theorem cre_apply_false (ψ : OneModeVec) : cre ψ false = 0 := by
  simp [cre]

@[simp] theorem cre_apply_true (ψ : OneModeVec) : cre ψ true = ψ false := by
  simp [cre]

/-- Nilpotence: `c² = 0`. -/
theorem ann_nilpotent : opComp ann ann = fun _ => 0 := by
  funext ψ occ
  cases occ <;> simp [opComp]

/-- Nilpotence: `(c†)² = 0`. -/
theorem cre_nilpotent : opComp cre cre = fun _ => 0 := by
  funext ψ occ
  cases occ <;> simp [opComp]

/-- The one-mode CAR: `{c,c†}=1`. -/
theorem ann_cre_anticommutator : opAdd (opComp ann cre) (opComp cre ann) = idOp := by
  funext ψ occ
  cases occ <;> simp [opAdd, opComp, idOp]

/-- Number operator is projection onto the occupied state. -/
theorem num_apply (ψ : OneModeVec) (occ : OneModeState) :
    num ψ occ = if occ then ψ true else 0 := by
  cases occ <;> simp [num]

/-- The one-mode number operator is idempotent. -/
theorem num_idempotent : opComp num num = num := by
  funext ψ occ
  cases occ <;> simp [opComp, num]

/-- The one-mode Hamiltonian `H=εN` has eigenvalue `0` on `|0⟩`. -/
theorem vacuum_energy_zero (ε : ℂ) :
    (fun occ => ε * num (fun b => if b = false then (1 : ℂ) else 0) occ) =
      (0 : ℂ) • (fun b => if b = false then (1 : ℂ) else 0) := by
  funext occ
  cases occ <;> simp [num]

/-- The one-mode Hamiltonian `H=εN` has eigenvalue `ε` on `|1⟩`. -/
theorem occupied_energy (ε : ℂ) :
    (fun occ => ε * num (fun b => if b = true then (1 : ℂ) else 0) occ) =
      ε • (fun b => if b = true then (1 : ℂ) else 0) := by
  funext occ
  cases occ <;> simp [num]

/-- One-mode finite Gibbs trace. -/
theorem one_mode_gibbs_trace (ε β : ℝ) :
    (∑ occ : OneModeState, Real.exp (-β * (if occ then ε else 0))) =
      1 + Real.exp (-β * ε) := by
  simp
  ring

end InfoGeometry.Algebra.FiniteSingleModeCAR
