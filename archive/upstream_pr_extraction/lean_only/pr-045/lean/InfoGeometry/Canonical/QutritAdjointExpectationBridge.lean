import InfoGeometry.Canonical.QutritExpectationSeparation

/-!
# Adjoint equivariance of the qutrit expectation readout

The adjoint action on operators induces the contragredient action on the
testing observable in a trace pairing.  This is the finite algebraic form of
equivariance; it does not assert that the individual Gell--Mann channels are
fixed by conjugation.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritAdjointExpectationBridge

open Matrix
open InfoGeometry.Canonical.QutritGellMannOperatorBasis
open InfoGeometry.Canonical.QutritSU3AdjointDecomposition
open InfoGeometry.Canonical.QutritExpectationSeparation

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- The dual adjoint action on the test matrix of an expectation channel. -/
def dualAdjointTest (g : SU3) (r : Fin 9) : QutritMatrix :=
  star (g : QutritMatrix) * (gellMannFamily r)ᴴ * (g : QutritMatrix)

theorem dualAdjointTest_apply (g : SU3) (r : Fin 9) :
    dualAdjointTest g r =
      star (g : QutritMatrix) * (gellMannFamily r)ᴴ * (g : QutritMatrix) := rfl

theorem expectationReadout_adjoint_equivariant
    (g : SU3) (A : QutritMatrix) (r : Fin 9) :
    expectationReadout (adjoint g A) r =
      Matrix.trace (dualAdjointTest g r * A) := by
  rw [expectationReadout_apply, adjoint_apply, dualAdjointTest]
  calc
    Matrix.trace ((gellMannFamily r)ᴴ *
        ((g : QutritMatrix) * A * star (g : QutritMatrix))) =
        Matrix.trace (((gellMannFamily r)ᴴ * (g : QutritMatrix) * A) *
          star (g : QutritMatrix)) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (star (g : QutritMatrix) *
        ((gellMannFamily r)ᴴ * (g : QutritMatrix) * A)) := by
          exact Matrix.trace_mul_comm
            ((gellMannFamily r)ᴴ * (g : QutritMatrix) * A)
            (star (g : QutritMatrix))
    _ = Matrix.trace ((star (g : QutritMatrix) * (gellMannFamily r)ᴴ *
        (g : QutritMatrix)) * A) := by
          simp [Matrix.mul_assoc]

theorem expectationReadout_adjoint_equivariant_function
    (g : SU3) (A : QutritMatrix) :
    expectationReadout (adjoint g A) =
      fun r => Matrix.trace (dualAdjointTest g r * A) := by
  funext r
  exact expectationReadout_adjoint_equivariant g A r

end InfoGeometry.Canonical.QutritAdjointExpectationBridge

end noncomputable section
