import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.SpatialDerivativeLogarithmicVariation

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace ConnesCocycleLogarithm

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/--
Finite self-adjoint generator readout for a modular-cocycle witness.

This type does not construct a one-parameter group or prove differentiability
of an operator-valued cocycle. It stores the finite generator supplied by the
matrix owner; analytic differentiation belongs to a separate implementation.
-/
abbrev ModularCocycleGroup (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] :=
  selfAdjoint (Matrix (Fin n) (Fin n) ℂ)

namespace ModularCocycleGroup

variable (cocycle : ModularCocycleGroup n)

def L_gen : Matrix (Fin n) (Fin n) ℂ := cocycle

theorem h_self_adj : (L_gen cocycle).conjTranspose = L_gen cocycle := by
  simpa only [L_gen, Matrix.star_eq_conjTranspose] using cocycle.property

/-- Finite operatorial logarithmic-generator readout `d_ln_Q = L_gen`. -/
def d_ln_Q : Matrix (Fin n) (Fin n) ℂ :=
  L_gen cocycle

/-- **Theorem**: Logarithmic Differential Variation Self-Adjointness: (d ln Q)† = d ln Q. -/
theorem d_ln_Q_self_adj :
    (d_ln_Q cocycle).conjTranspose = d_ln_Q cocycle := by
  dsimp [d_ln_Q]
  exact h_self_adj cocycle

/-- Trace additivity for the finite matrix generator readout. -/
theorem cocycle_trace_additivity (L12 L23 : ModularCocycleGroup n) :
    trace (d_ln_Q L12 + d_ln_Q L23) = trace (d_ln_Q L12) + trace (d_ln_Q L23) := by
  rw [trace_add]

/-- The finite matrix trace annihilates the commutator with the generator. -/
theorem cocycle_commutator_trace_zero (A : Matrix (Fin n) (Fin n) ℂ) :
    trace (A * d_ln_Q cocycle - d_ln_Q cocycle * A) = 0 := by
  rw [trace_sub, trace_mul_comm A (d_ln_Q cocycle), sub_self]

end ModularCocycleGroup

/-! ## Genuine noncommutative logarithmic variation -/

namespace NoncommutativeVariation

open InfoGeometry.OperatorAlgebra.SpatialDerivativeLogarithmicVariation

variable {A : Type*}
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/--
The actual operatorial logarithmic derivative of an exponential RN path.
This consumes the native Banach-algebra/Duhamel derivative owner; unlike the
finite generator readout above, it is a genuine `HasDerivAt`-based statement.
-/
theorem leftLogDerivative_expNeg_eq_neg_generator
    {K : ℝ → A} {t : ℝ} {K' : A}
    (hK : HasDerivAt K K' t)
    (hcomm : Commute K' (K t)) :
    leftLogarithmicDerivative (expNegUnitsPath K) t = -K' :=
  leftLogarithmicDerivative_expNegUnitsPath hK hcomm

end NoncommutativeVariation

end ConnesCocycleLogarithm
