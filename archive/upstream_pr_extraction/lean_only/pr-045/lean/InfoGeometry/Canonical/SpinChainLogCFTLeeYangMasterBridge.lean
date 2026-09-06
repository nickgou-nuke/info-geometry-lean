import Mathlib.Tactic
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Finite coupling, nilpotent, and Cayley readouts

This module records three independent finite algebraic readouts:

1. A symmetric nonnegative logarithmic coupling for positive integer inputs.

2. The square-zero law for the stored rank-two nilpotent matrix.

3. The existing Cayley unit-circle to critical-line implication.

No spin-chain model, LogCFT construction, direct-limit theorem, or Lee--Yang
zero theorem is inferred from these declarations.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinChainLogCFTLeeYangMasterBridge

open Complex
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/--
**Finite logarithmic coupling properties.**
For positive integer inputs and nonnegative coupling, the displayed coupling
is symmetric and nonnegative.
-/
theorem prime_spin_chain_coupling_properties (pi pj : ℕ) (hpi : 1 ≤ pi) (hpj : 1 ≤ pj) (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    let J := fun i j => kappa * Real.log (i : ℝ) * Real.log (j : ℝ)
    (J pi pj = J pj pi) ∧ (0 ≤ J pi pj) := by
  intro J
  have hpi_log : 0 ≤ Real.log (pi : ℝ) := Real.log_nonneg (by exact_mod_cast hpi)
  have hpj_log : 0 ≤ Real.log (pj : ℝ) := Real.log_nonneg (by exact_mod_cast hpj)
  have h_symm : J pi pj = J pj pi := by dsimp [J]; ring
  have h_pos : 0 ≤ J pi pj := by
    dsimp [J]
    exact mul_nonneg (mul_nonneg hkappa hpi_log) hpj_log
  exact ⟨h_symm, h_pos⟩

/--
**Stored matrix nilpotency.**
The rank-two nilpotent matrix squares to zero.
-/
theorem logcft_jordan_nilpotent_sq_law :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) * jordanNilpotent = 0 :=
  jordanNilpotent_sq (K := ℂ)

/--
**Cayley unit-circle alignment.**
A unit-circle point away from the pole maps to the critical line.
-/
theorem cayley_leeyang_circle_to_critical_line {z : ℂ} (hz : OnLeeYangCircle z) (hpole : z.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z) :=
  cayleyToTemperature_mem_criticalLine_of_unitCircle z hz hpole

end InfoGeometry.Canonical.SpinChainLogCFTLeeYangMasterBridge
