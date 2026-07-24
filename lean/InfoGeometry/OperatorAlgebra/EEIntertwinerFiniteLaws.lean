import Mathlib.Tactic

/-!
# Finite `32`-slot block-swap intertwiner laws

This module is the Lean twin of `tools/sympy/ee_intertwiner_finite_laws.py`.

It proves explicit finite laws for the two-quadrant `2 × 16` integer carrier:
* the block swap `W` is an involution;
* `W` conjugates the upper-left projector to the lower-right projector;
* `W` conjugates the lower-right projector back to the upper-left projector;
* `W` anti-commutes with the diagonal grading core.

Honesty boundary: this does **not** prove Tomita--Takesaki modular conjugation,
CPT, anomaly shielding, particle classification, or a `Pin(5,5)` representation
theorem.  It is the kernel-checked finite block identity layer.
-/

namespace InfoGeometry.OperatorAlgebra.EEIntertwinerFiniteLaws

abbrev Sector := Fin 2
abbrev Slot16 := Fin 16
abbrev Spin32 := Sector × Slot16
abbrev Spinor32 := Spin32 → ℤ

/-- Cross-quadrant block swap. -/
def W (v : Spinor32) : Spinor32 := fun p =>
  match p.1 with
  | 0 => v (1, p.2)
  | 1 => v (0, p.2)

/-- Upper-left 16-slot projector. -/
def UL (v : Spinor32) : Spinor32 := fun p =>
  match p.1 with
  | 0 => v p
  | 1 => 0

/-- Lower-right 16-slot projector. -/
def LR (v : Spinor32) : Spinor32 := fun p =>
  match p.1 with
  | 0 => 0
  | 1 => v p

/-- Diagonal grading core: negative on the first block and positive on the second block. -/
def g0 (v : Spinor32) : Spinor32 := fun p =>
  match p.1 with
  | 0 => -v p
  | 1 => v p

/-- The cross-quadrant block swap is an involution. -/
theorem W_involutive (v : Spinor32) : W (W v) = v := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [W]

/-- The upper-left projector is idempotent. -/
theorem UL_idempotent (v : Spinor32) : UL (UL v) = UL v := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [UL]

/-- The lower-right projector is idempotent. -/
theorem LR_idempotent (v : Spinor32) : LR (LR v) = LR v := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [LR]

/-- The upper-left and lower-right projectors are orthogonal in the `UL ∘ LR` order. -/
theorem UL_after_LR_zero (v : Spinor32) : UL (LR v) = 0 := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [UL, LR]

/-- The lower-right and upper-left projectors are orthogonal in the `LR ∘ UL` order. -/
theorem LR_after_UL_zero (v : Spinor32) : LR (UL v) = 0 := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [UL, LR]

/-- `W` conjugates the upper-left sector onto the lower-right sector. -/
theorem W_UL_W_eq_LR (v : Spinor32) : W (UL (W v)) = LR v := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [W, UL, LR]

/-- `W` conjugates the lower-right sector back onto the upper-left sector. -/
theorem W_LR_W_eq_UL (v : Spinor32) : W (LR (W v)) = UL v := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [W, UL, LR]

/-- `W` anti-commutes with the diagonal grading core. -/
theorem W_g0_anticommutes (v : Spinor32) : W (g0 v) = -g0 (W v) := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [W, g0]

/-- Closed finite packet for the block-swap intertwiner identities. -/
theorem ee_intertwiner_finite_laws_packet :
    (∀ v : Spinor32, W (W v) = v) ∧
      (∀ v : Spinor32, W (UL (W v)) = LR v) ∧
      (∀ v : Spinor32, W (LR (W v)) = UL v) ∧
      (∀ v : Spinor32, W (g0 v) = -g0 (W v)) ∧
      (∀ v : Spinor32, UL (UL v) = UL v) ∧
      (∀ v : Spinor32, LR (LR v) = LR v) ∧
      (∀ v : Spinor32, UL (LR v) = 0) ∧
      (∀ v : Spinor32, LR (UL v) = 0) := by
  exact ⟨W_involutive, W_UL_W_eq_LR, W_LR_W_eq_UL, W_g0_anticommutes,
    UL_idempotent, LR_idempotent, UL_after_LR_zero, LR_after_UL_zero⟩

end InfoGeometry.OperatorAlgebra.EEIntertwinerFiniteLaws
