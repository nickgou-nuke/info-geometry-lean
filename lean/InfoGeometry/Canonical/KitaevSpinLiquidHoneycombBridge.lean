import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace KitaevSpinLiquid

/-- Plaquette Flux Operator W_p on hexagonal lattice with Z₂ eigenvalues ±1. -/
structure PlaquetteFlux where
  fluxValue : ℝ
  flux_sq : fluxValue ^ 2 = 1

namespace PlaquetteFlux

variable (W : PlaquetteFlux)

/-- **Theorem**: Z₂ Plaquette Flux Eigenvalues are strictly ±1. -/
theorem flux_eigenvalues_pm_one :
    W.fluxValue = 1 ∨ W.fluxValue = -1 := by
  have h_sq := W.flux_sq
  have h_fact : (W.fluxValue - 1) * (W.fluxValue + 1) = 0 := by
    calc (W.fluxValue - 1) * (W.fluxValue + 1)
      _ = W.fluxValue ^ 2 - 1 := by ring
      _ = 1 - 1 := by rw [h_sq]
      _ = 0 := by ring
  cases mul_eq_zero.mp h_fact with
  | inl h1 => left; linarith
  | inr h2 => right; linarith

/-! The scalar plaquette eigenvalue above is only the sector readout.  The
    conservation statement itself belongs to the operator algebra. -/

/-- Commutator of a plaquette flux operator with a Hamiltonian. -/
def fluxHamiltonianCommutator {A : Type*} [Ring A] (W H : A) : A :=
  W * H - H * W

/-- Exact flux conservation from the operator commutation law. -/
theorem flux_conservation_exact {A : Type*} [Ring A]
    (W H : A) (hcomm : W * H = H * W) :
    fluxHamiltonianCommutator W H = 0 := by
  unfold fluxHamiltonianCommutator
  rw [hcomm, sub_self]

/-- Kitaev Non-Abelian Anyon Phase Gap Inequality J_z < J_x + J_y. -/
def isNonAbelianPhase (Jx Jy Jz : ℝ) : Prop :=
  Jz < Jx + Jy

/-- **Theorem**: Isotropic Point J_x = J_y = J_z = J > 0 is in the Non-Abelian Phase. -/
theorem isotropic_point_non_abelian (J : ℝ) (hJ : 0 < J) :
    isNonAbelianPhase J J J := by
  dsimp [isNonAbelianPhase]
  linarith

end PlaquetteFlux

end KitaevSpinLiquid
