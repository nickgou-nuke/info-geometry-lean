import InfoGeometry.Physics.MatrixTraceBimodulePairingNative

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace state associated with a (not necessarily normalized) density matrix. -/
def jaynesGibbsState (rho X : TraceOperatorSpace n) : ℝ :=
  tracePairingNative rho X

/-- Algebraic imaginary modular transport by a chosen inverse candidate. -/
def modularImaginaryFlow
    (rho rhoInv Y : TraceOperatorSpace n) : TraceOperatorSpace n :=
  rho * Y * rhoInv

/-- The finite-dimensional trace identity underlying the algebraic KMS relation.

This is deliberately conditional: no positivity, normalization, or analytic modular
group is asserted here.  The only required hypothesis is a left inverse for `rho`. -/
theorem jaynes_state_is_strictly_kms
    (rho rhoInv X Y : TraceOperatorSpace n)
    (hInv : rhoInv * rho = 1) :
    jaynesGibbsState (rho := rho)
        (X * modularImaginaryFlow rho rhoInv Y) =
      jaynesGibbsState (rho := rho) (Y * X) := by
  dsimp [jaynesGibbsState, tracePairingNative, modularImaginaryFlow]
  calc
    Matrix.trace (rho * (X * (rho * Y * rhoInv))) =
        Matrix.trace ((rho * X * rho * Y) * rhoInv) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (rhoInv * (rho * X * rho * Y)) := by
          simpa using (Matrix.trace_mul_comm (rho * X * rho * Y) rhoInv)
    _ = Matrix.trace ((X * rho) * Y) := by
          rw [show rhoInv * (rho * X * rho * Y) = (rhoInv * rho) * (X * (rho * Y)) by
            simp only [Matrix.mul_assoc]]
          rw [hInv, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Y * (X * rho)) := by
          simpa using (Matrix.trace_mul_comm (X * rho) Y)
    _ = Matrix.trace ((Y * X) * rho) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (rho * (Y * X)) := by
          simpa using (Matrix.trace_mul_comm (Y * X) rho)

theorem jaynesian_synthesis_kms
    (rho rhoInv X Y : TraceOperatorSpace n)
    (hInv : rhoInv * rho = 1) :
    jaynesGibbsState (rho := rho)
        (X * modularImaginaryFlow rho rhoInv Y) =
      jaynesGibbsState (rho := rho) (Y * X) :=
  jaynes_state_is_strictly_kms rho rhoInv X Y hInv

end InfoGeometry.Physics
