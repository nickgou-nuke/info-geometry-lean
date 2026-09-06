import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace E8ExceptionalLieAlgebraTriality

namespace E8ExceptionalLieAlgebraTriality

/-- A finite arithmetic dimension inequality used as a readout.

This statement does not construct the indicated exceptional Lie algebras or
prove an inclusion between them. -/
theorem exceptional_subalgebra_chain_dimensions :
    14 < 52 ∧ 52 < 248 := by
  decide

/-- The displayed finite arithmetic decomposition `248 = 240 + 8`.

No root system or Lie-algebra dimension theorem is constructed here. -/
theorem e8_dimension_root_rank_decomposition :
    248 = 240 + 8 := by
  decide

/-- A unitary `8 × 8` matrix equipped with the finite relation `U³ = I`.

The type is deliberately weaker than an E₈ or Spin(8) triality
automorphism; such a realization requires a separate carrier and action. -/
abbrev TrialityAutomorphism :=
  { U : Matrix.unitaryGroup (Fin 8) ℂ //
      (U : Matrix (Fin 8) (Fin 8) ℂ) * U * U = 1 }

variable (tau : TrialityAutomorphism)

def triality_matrix : Matrix (Fin 8) (Fin 8) ℂ :=
  (tau.1 : Matrix (Fin 8) (Fin 8) ℂ)

theorem h_cube_identity :
    triality_matrix tau * triality_matrix tau * triality_matrix tau = 1 :=
  tau.2

theorem h_unitary :
    (triality_matrix tau).conjTranspose * triality_matrix tau = 1 := by
  change (tau.1 : Matrix (Fin 8) (Fin 8) ℂ).conjTranspose *
      (tau.1 : Matrix (Fin 8) (Fin 8) ℂ) = 1
  exact Matrix.mem_unitaryGroup_iff'.mp tau.1.2

/-- Read back the supplied order-three matrix relation. -/
theorem triality_cube_identity :
    triality_matrix tau * triality_matrix tau * triality_matrix tau = 1 :=
  h_cube_identity tau

/-- Trace is invariant under conjugation by the supplied unitary matrix.

This is a finite matrix identity and does not identify the matrix with a
geometric triality action. -/
theorem triality_trace_conservation (X : Matrix (Fin 8) (Fin 8) ℂ) :
    trace (triality_matrix tau * X * (triality_matrix tau).conjTranspose) = trace X := by
  rw [trace_mul_comm (triality_matrix tau * X) (triality_matrix tau).conjTranspose,
    ← mul_assoc, h_unitary tau, one_mul]

end E8ExceptionalLieAlgebraTriality

end E8ExceptionalLieAlgebraTriality
