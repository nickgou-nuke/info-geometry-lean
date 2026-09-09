import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Algebra.SuperTraceBerezinian

/-!
# Supertrace/Berezinian readout bridge

The repository already owns the parity/supertrace layer and the relative
modular Berezinian shadow.  This file adds only the logarithmic readback that
connects the existing Berezinian potential to its positive scalar shadow.
No second supertrace, Berezinian, or graded carrier is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.RelativeModularOperator

open InfoGeometry.Canonical.PositiveRayCore

variable {n : ℕ} [Nonempty (Fin n)]

/-- The existing Berezinian logarithmic potential reconstructs the positive
relative Berezinian shadow by exponentiation.

This is the scalar graded analogue of `exp (-K) = ρ`; the Berezinian shadow
and its positivity remain owned by `RelativeModularOperator`.
-/
theorem exp_neg_relativeModularBerezinianPotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    Real.exp
        (-relativeModularBerezinianPotential
          (n := n) qPlus q0Plus qMinus q0Minus) =
      relativeModularBerezinianShadow
        (n := n) qPlus q0Plus qMinus q0Minus := by
  unfold relativeModularBerezinianPotential
  simpa using Real.exp_log
    (relativeModularBerezinianShadow_pos
      (n := n) qPlus q0Plus qMinus q0Minus)

/-- The swapped graded sectors invert the Berezinian shadow. -/
theorem relativeModularBerezinianShadow_swap_readout
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularBerezinianShadow
        (n := n) qMinus q0Minus qPlus q0Plus =
      (relativeModularBerezinianShadow
        (n := n) qPlus q0Plus qMinus q0Minus)⁻¹ := by
  unfold relativeModularBerezinianShadow
  exact (inv_div _ _).symm

end InfoGeometry.Canonical.RelativeModularOperator

namespace Audit.SuperTraceBerezinian.SuperMatrix

/-! The existing diagonal exponential identity, written in negative-log
surprisal form. -/

theorem neg_log_berezinian_exp_diag_eq_neg_supertrace
    (M : SuperMatrix ℝ) :
    -Real.log (berezinian (exp_diag M)) =
      -supertrace M := by
  rw [berezinian_exp_diag]
  simp

end Audit.SuperTraceBerezinian.SuperMatrix
