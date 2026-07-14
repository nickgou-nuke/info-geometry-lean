import Mathlib.Tactic

namespace Omega.Zeta

namespace xi_time_only_conserved_quantity_system

/-- Morphisms in the seeded quotient are represented by their elapsed time. -/
abbrev Mor : Type := ℕ

/-- The null move is the reversible basic generator after quotienting cycles. -/
def BasicReversible (e : ℕ) : Prop :=
  e = 0

/-- In the time quotient, every pair of elapsed-time morphisms composes. -/
def Composable (_u _v : ℕ) : Prop :=
  True

/-- Composition adds elapsed lengths. -/
def comp (u v : ℕ) : ℕ :=
  u + v

/-- The conserved time length of a morphism. -/
def length (w : ℕ) : ℝ :=
  (w : ℝ)

end xi_time_only_conserved_quantity_system

/-- Paper label: `thm:xi-time-only-conserved-quantity`. In the seeded time quotient, any real
additive invariant that vanishes on the reversible null generator is a scalar multiple of
elapsed length. -/
theorem paper_xi_time_only_conserved_quantity
    (I : xi_time_only_conserved_quantity_system.Mor -> ℝ)
    (hbasic : ∀ e, xi_time_only_conserved_quantity_system.BasicReversible e -> I e = 0)
    (hadd : ∀ {u v}, xi_time_only_conserved_quantity_system.Composable u v ->
      I (xi_time_only_conserved_quantity_system.comp u v) = I u + I v) :
    ∃ lambda : ℝ, ∀ w, I w = lambda * xi_time_only_conserved_quantity_system.length w := by
  refine ⟨I 1, ?_⟩
  intro w
  dsimp [xi_time_only_conserved_quantity_system.length]
  induction w with
  | zero =>
      have hzero : I 0 = 0 := hbasic 0 rfl
      simp [hzero]
  | succ n ih =>
      have hstep : I (n + 1) = I n + I 1 := by
        simpa [xi_time_only_conserved_quantity_system.comp,
          xi_time_only_conserved_quantity_system.Composable] using
          (hadd (u := n) (v := 1) trivial)
      calc
        I (Nat.succ n) = I (n + 1) := by rw [Nat.succ_eq_add_one]
        _ = I n + I 1 := hstep
        _ = I 1 * (n : ℝ) + I 1 := by rw [ih]
        _ = I 1 * (Nat.succ n : ℝ) := by
          rw [Nat.cast_succ]
          ring

end Omega.Zeta
