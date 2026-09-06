import Mathlib.Algebra.Module.Submodule.Basic
import proofs.SplitOctonionNilpotentExp

open SplitOctonion
open SplitOctonionSL2MatrixBridge
open SplitOctonionNilpotentExp

namespace SplitOctonionSL2NonNilpotent

theorem H_in_commutator : H = bracket E F := by
  rw [bracket_E_F]

theorem E_in_commutator : E = bracket ((1/2 : ℝ) • H) E := by
  ext1 <;> ext1 <;> simp [bracket, H, E, u, ell, smul_def, add_def, sub_def, mul_def, star] <;> ring

theorem F_in_commutator : F = bracket (-(1/2 : ℝ) • H) F := by
  ext1 <;> ext1 <;> simp [bracket, H, F, u, ell, smul_def, add_def, sub_def, mul_def, star] <;> ring

/-- Every element in the basis {E, F, H} is in the span of commutators 
    of elements in g_sl2. Therefore [g, g] = g, so g is not nilpotent. -/
theorem E_F_H_perfect :
  H = bracket E F ∧ 
  E = bracket ((1/2:ℝ) • H) E ∧ 
  F = bracket (-(1/2:ℝ) • H) F := by
  exact ⟨H_in_commutator, E_in_commutator, F_in_commutator⟩

end SplitOctonionSL2NonNilpotent
