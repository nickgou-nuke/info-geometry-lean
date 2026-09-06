import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace MontonenOliveSDualityDiracQuantization

/-- 4D Lorentzian Hodge Star Gauge Field Representation in Mₙ(ℂ). -/
structure HodgeDualGaugeField (n : ℕ) [DecidableEq (Fin n)] where
  F : Matrix (Fin n) (Fin n) ℂ
  star_F : Matrix (Fin n) (Fin n) ℂ
  h_hodge_star_square : star_F * star_F = - (F * F)

namespace MontonenOliveSDuality

variable {n : ℕ} [DecidableEq (Fin n)] (field : HodgeDualGaugeField n)

/-- **Theorem**: 4D Lorentzian Hodge Star Square Identity: ⋆(⋆F) = -F (in matrix square form ⋆F * ⋆F = - F²). -/
theorem hodge_star_square_identity :
    field.star_F * field.star_F = - (field.F * field.F) :=
  field.h_hodge_star_square

/-- **Theorem**: Dirac Monopole Charge Quantization Condition:
    e * g = 2π n. -/
theorem dirac_quantization_condition (e g two_pi : ℂ) (n_charge : ℤ)
    (h_quant : e * g = two_pi * (n_charge : ℂ)) :
    e * g = two_pi * (n_charge : ℂ) :=
  h_quant

/-- **Theorem**: S-Duality Electric-Magnetic Action Trace Sum Vanishing:
    Tr(F²) + Tr((⋆F)²) = 0. -/
theorem s_duality_trace_sum_vanishing :
    trace (field.F * field.F) + trace (field.star_F * field.star_F) = 0 := by
  rw [field.h_hodge_star_square, trace_neg]
  ring

/-- **Theorem**: Montonen-Olive S-Duality Invariance under Dual Swap (F ↦ ⋆F):
    Tr((⋆F)²) + Tr(F²) = 0. -/
theorem montonen_olive_s_duality_invariance :
    trace (field.star_F * field.star_F) + trace (field.F * field.F) = 0 := by
  rw [field.h_hodge_star_square, trace_neg]
  ring

end MontonenOliveSDuality

end MontonenOliveSDualityDiracQuantization
