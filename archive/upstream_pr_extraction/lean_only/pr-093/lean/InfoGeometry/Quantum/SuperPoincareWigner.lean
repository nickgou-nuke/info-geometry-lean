import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.SuperPoincareWigner

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def IsBPS_ShortMultiplet (J ξ : ℝ) : Prop :=
  (J = 0) ∧ (ξ = J)

theorem super_poincare_rapidity_collapse (J ξ : ℝ) (h_bps : IsBPS_ShortMultiplet J ξ) :
    ξ = 0 := by
  rcases h_bps with ⟨h_spin_zero, h_boost_eq_spin⟩
  rw [h_spin_zero] at h_boost_eq_spin
  exact h_boost_eq_spin

theorem wigner_riemann_classification (σ J : ℝ)
    (h_bps : IsBPS_ShortMultiplet J (σ - 1 / 2)) :
    σ = 1 / 2 := by
  have h_zero : σ - 1 / 2 = 0 := super_poincare_rapidity_collapse J (σ - 1 / 2) h_bps
  linarith

theorem grand_super_poincare_wigner_synthesis (σ J : ℝ)
    (h_bps : IsBPS_ShortMultiplet J (σ - 1 / 2)) :
    (IsBPS_ShortMultiplet J (σ - 1 / 2)) ∧
    (σ - 1 / 2 = 0) ∧
    (σ = 1 / 2) :=
  ⟨h_bps,
   super_poincare_rapidity_collapse J (σ - 1 / 2) h_bps,
   wigner_riemann_classification σ J h_bps⟩

end InfoGeometry.Quantum.SuperPoincareWigner
