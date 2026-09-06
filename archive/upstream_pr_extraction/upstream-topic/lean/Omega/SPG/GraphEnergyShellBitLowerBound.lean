import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.SPG.GraphEnergyShellLatticeCounting

namespace Omega.SPG

/-- Combining the cycle-lattice energy-shell normal form with the standard injective binary-code
cardinality bound yields a lower bound on the required bit budget.
    cor:graph-energy-shell-bit-lower-bound -/
theorem paper_graph_energy_shell_bit_lower_bound
    (countingData : GraphEnergyShellLatticeCountingData)
    (requiredBits logMicrostateCount : ℝ)
    (codeBound : Real.exp logMicrostateCount ≤ (2 : ℝ) ^ requiredBits) :
    requiredBits ≥ logMicrostateCount / Real.log 2 := by
  have _ := paper_graph_energy_shell_lattice_counting countingData
  have hlog :
      logMicrostateCount ≤ Real.log ((2 : ℝ) ^ requiredBits) := by
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos logMicrostateCount) codeBound
  have hbits :
      logMicrostateCount ≤ requiredBits * Real.log 2 := by
    calc
      logMicrostateCount ≤ Real.log ((2 : ℝ) ^ requiredBits) := hlog
      _ = requiredBits * Real.log 2 := by
        rw [Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  exact (div_le_iff₀ hlog2).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbits)

end Omega.SPG
