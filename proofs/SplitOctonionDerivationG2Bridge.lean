import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import proofs.SplitOctonionDerivationSL2
import proofs.SplitOctonionSL2MatrixBridge
import proofs.SplitOctonionNilpotentExp

set_option maxHeartbeats 10000000
set_option maxRecDepth 2000000

open Quaternion
open SplitOctonion
open SplitOctonionDerivation
open SplitOctonionSL2MatrixBridge

namespace SplitOctonionG2Bridge

/-- The Root sl_2(R) Derivation Generators inside g_{2(2)} -/
noncomputable def op_H (z : SplitOct) : SplitOct := 
  innerDeriv E F z

noncomputable def op_E (z : SplitOct) : SplitOct := 
  (1/2 : ℝ) • innerDeriv H E z

noncomputable def op_F (z : SplitOct) : SplitOct := 
  -(1/2 : ℝ) • innerDeriv H F z

/-- THE CAPSTONE THEOREMS: 
    The operator brackets perfectly match the sl_2 commutation relations 
    when acting on ANY arbitrary element z in the split octonions. -/

theorem g2_root_HE (z : SplitOct) : 
    derivBracket op_H op_E z = (2 : ℝ) • op_E z := by
  ext <;> simp [derivBracket, op_H, op_E, innerDeriv, bracket, associator, E, F, H, u, ell, smul_def, add_def, sub_def, mul_def, star, zero_def, neg_def] <;> ring

theorem g2_root_HF (z : SplitOct) : 
    derivBracket op_H op_F z = (-2 : ℝ) • op_F z := by
  ext <;> simp [derivBracket, op_H, op_F, innerDeriv, bracket, associator, E, F, H, u, ell, smul_def, add_def, sub_def, mul_def, star, zero_def, neg_def] <;> ring

theorem g2_root_EF (z : SplitOct) : 
    derivBracket op_E op_F z = op_H z := by
  ext <;> simp [derivBracket, op_H, op_E, op_F, innerDeriv, bracket, associator, E, F, H, u, ell, smul_def, add_def, sub_def, mul_def, star, zero_def, neg_def] <;> ring

end SplitOctonionG2Bridge
