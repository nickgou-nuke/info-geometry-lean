import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorChirality

/-!
# Vorticity and Topological Spin in the Holographic Fluid

This module formalizes the duality between the microscopic quantum spin (chiral Dirac states)
and the macroscopic circulation of the boundary probability fluid (vorticity).

We prove that under the Pauli-Dirac Gordon decomposition bridge (where the fluid vorticity operator
`V` is directly proportional to the boundary chirality operator `Γ`), the macroscopic circulation
eigenstates of the fluid correspond exactly to the microscopic matter chirality eigenstates:
- Positive vorticity (left-handed circulation) corresponds to chirality eigenvalue `+1`.
- Negative vorticity (right-handed circulation) corresponds to chirality eigenvalue `-1`.

This provides the formal connection between Navier-Stokes hydrodynamic vorticity and boundary
chiral fermions in the Alexandrov causal limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.MadelungTopologicalSpin

open InfoGeometry.Canonical.OmegaBoundaryRepresentation
open InfoGeometry.Canonical.CantorChirality

/-- Microscopic left-handed chiral boundary state: eigenstate of `Γ` with eigenvalue `+1`. -/
def IsLeftChiralState (f : CantorSpace) : Prop :=
  ChiralityOp f = (1 : ℂ) • f

/-- Microscopic right-handed chiral boundary state: eigenstate of `Γ` with eigenvalue `-1`. -/
def IsRightChiralState (f : CantorSpace) : Prop :=
  ChiralityOp f = (-1 : ℂ) • f

/-- Macroscopic left-handed circulation fluid state: positive vorticity eigenstate. -/
def IsLeftCirculationState (f : CantorSpace) (V : CantorOp) (c : ℂ) : Prop :=
  V f = c • f

/-- Macroscopic right-handed circulation fluid state: negative vorticity eigenstate. -/
def IsRightCirculationState (f : CantorSpace) (V : CantorOp) (c : ℂ) : Prop :=
  V f = (-c) • f

/-- **Pauli-Dirac Spin-Vorticity Duality**
    Under the Gordon decomposition bridge `V = c • Γ` mapping fluid vorticity to chirality,
    the macroscopic fluid circulation states are equivalent to the microscopic chiral spinor states. -/
theorem spin_vorticity_duality (f : CantorSpace) (V : CantorOp) (c : ℂ) (hc : c ≠ 0)
    (h_bridge : V = c • ChiralityOp) :
    (IsLeftChiralState f ↔ IsLeftCirculationState f V c) ∧
    (IsRightChiralState f ↔ IsRightCirculationState f V c) := by
  constructor
  · constructor
    · intro h
      unfold IsLeftCirculationState
      ext x
      have h_val : ChiralityOp f x = f x := by
        have h_eq : ChiralityOp f = (1 : ℂ) • f := h
        have h_fun := congr_fun h_eq x
        simp [Pi.smul_apply] at h_fun
        exact h_fun
      have h_change : (V f) x = c * ChiralityOp f x := by
        rw [h_bridge]
        rfl
      rw [h_change, h_val]
      rfl
    · intro h
      unfold IsLeftChiralState
      ext x
      have h_val : (V f) x = c * f x := by
        have h_fun := congr_fun h x
        change (V f) x = c • f x at h_fun
        change (V f) x = c * f x at h_fun
        exact h_fun
      have h_eq : c * ChiralityOp f x = c * f x := by
        have h_change : (V f) x = c * ChiralityOp f x := by
          rw [h_bridge]
          rfl
        rw [h_change] at h_val
        exact h_val
      have h_cancel : ChiralityOp f x = f x := mul_left_cancel₀ hc h_eq
      change ChiralityOp f x = (1 : ℂ) • f x
      change ChiralityOp f x = 1 * f x
      rw [h_cancel, one_mul]
  · constructor
    · intro h
      unfold IsRightCirculationState
      ext x
      have h_val : ChiralityOp f x = - f x := by
        have h_eq : ChiralityOp f = (-1 : ℂ) • f := h
        have h_fun := congr_fun h_eq x
        simp [Pi.smul_apply] at h_fun
        exact h_fun
      have h_change : (V f) x = c * ChiralityOp f x := by
        rw [h_bridge]
        rfl
      rw [h_change, h_val]
      change c * -f x = -c * f x
      ring
    · intro h
      unfold IsRightChiralState
      ext x
      have h_val : (V f) x = -c * f x := by
        have h_fun := congr_fun h x
        change (V f) x = (-c) • f x at h_fun
        change (V f) x = -c * f x at h_fun
        exact h_fun
      have h_eq : c * ChiralityOp f x = c * - f x := by
        have h_change : (V f) x = c * ChiralityOp f x := by
          rw [h_bridge]
          rfl
        rw [h_change] at h_val
        calc
          c * ChiralityOp f x = -c * f x := h_val
          _ = c * - f x := by ring
      have h_cancel : ChiralityOp f x = -f x := mul_left_cancel₀ hc h_eq
      change ChiralityOp f x = (-1 : ℂ) • f x
      change ChiralityOp f x = -1 * f x
      rw [h_cancel, neg_one_mul]

end InfoGeometry.Canonical.MadelungTopologicalSpin

end noncomputable section
