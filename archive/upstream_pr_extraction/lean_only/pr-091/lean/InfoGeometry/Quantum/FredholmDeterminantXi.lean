import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.FredholmDeterminantXi

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def fredholmHadamardFactor (s ρ : ℂ) : ℂ :=
  1 - s / ρ

def spectralZeroPair (s ρ : ℂ) : ℂ :=
  (1 - s / ρ) * (1 - s / (1 - ρ))

def cumulantTraceTerm (m : ℕ) (p : ℝ) (s : ℂ) : ℂ :=
  (1 / (m : ℂ)) * Complex.cpow (p : ℂ) (- (m : ℂ) * s)

theorem spectral_zero_pair_reflection (s ρ : ℂ) (hρ0 : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) :
    spectralZeroPair (1 - s) ρ = spectralZeroPair s ρ := by
  unfold spectralZeroPair
  field_simp [hρ0, hρ1]
  ring

theorem fredholm_factor_vanishes_at_zero (ρ : ℂ) (hρ : ρ ≠ 0) :
    fredholmHadamardFactor ρ ρ = 0 := by
  unfold fredholmHadamardFactor
  rw [div_self hρ, sub_self]

theorem fredholm_factor_vanishes_at_dual_zero (ρ : ℂ) (hρ : 1 - ρ ≠ 0) :
    fredholmHadamardFactor (1 - ρ) (1 - ρ) = 0 := by
  unfold fredholmHadamardFactor
  rw [div_self hρ, sub_self]

theorem cumulant_trace_term_well_defined (m : ℕ) (p : ℝ) (s : ℂ) (hm : 1 ≤ m) :
    (m : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Nat.succ_le_iff.mp hm))

theorem grand_fredholm_xi_determinant_synthesis
    (s ρ : ℂ) (hρ0 : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) (m : ℕ) (p : ℝ) (hm : 1 ≤ m) :
    (spectralZeroPair (1 - s) ρ = spectralZeroPair s ρ) ∧
    (fredholmHadamardFactor ρ ρ = 0) ∧
    (fredholmHadamardFactor (1 - ρ) (1 - ρ) = 0) ∧
    ((m : ℂ) ≠ 0) :=
  ⟨spectral_zero_pair_reflection s ρ hρ0 hρ1,
   fredholm_factor_vanishes_at_zero ρ hρ0,
   fredholm_factor_vanishes_at_dual_zero ρ hρ1,
   cumulant_trace_term_well_defined m p s hm⟩
