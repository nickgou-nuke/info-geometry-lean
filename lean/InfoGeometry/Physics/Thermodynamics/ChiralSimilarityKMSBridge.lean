import InfoGeometry.Physics.Thermodynamics.ChiralChemicalPotentialDeformation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.HorizonKMS

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.HorizonKMS
open Matrix
open Complex

noncomputable section

/-!
# Readout adapter for the chiral similarity flow

This packages the existing real-flow API as a `KMSReadoutDatum`.  The state is
the ordinary matrix trace, whose invariance follows from cyclicity and the
explicit two-sided inverse of the Gibbs factor.  No analytic continuation or
full KMS boundary condition is asserted.
-/

/-! ### Discrete triality parameter

This is an algebraic compatibility point for the previously proved Zorn
scaling obstruction.  It is not an analytic KMS boundary law. -/

noncomputable def modularParameter (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ))

theorem modular_time_triality_root :
    modularParameter (2 * Real.pi / 3) ^ 3 = 1 := by
  dsimp [modularParameter]
  rw [← Complex.exp_nat_mul]
  have h : ((3 : ℕ) : ℂ) * (Complex.I * ((2 * Real.pi / 3 : ℝ) : ℂ)) =
      Complex.I * (2 * (Real.pi : ℂ)) := by
    push_cast
    ring
  rw [h]
  rw [show Complex.I * (2 * (Real.pi : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

def chiralTrace (X : BdGBlock ℝ) : ℝ := Matrix.trace X

theorem chiralTrace_flow_invariant (mu : ℝ) (X : BdGBlock ℝ) :
    chiralTrace (chiralSimilarityFlow mu X) = chiralTrace X := by
  unfold chiralTrace chiralSimilarityFlow
  calc
    Matrix.trace (gibbsFactor mu * X * gibbsFactor (-mu)) =
        Matrix.trace (gibbsFactor (-mu) * (gibbsFactor mu * X)) := by
      simpa [Matrix.mul_assoc] using
        (Matrix.trace_mul_comm (gibbsFactor mu * X) (gibbsFactor (-mu)))
    _ = Matrix.trace ((gibbsFactor (-mu) * gibbsFactor mu) * X) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace X := by
      rw [gibbsFactor_neg_mul, one_mul]

/-- A readout invariant under the chiral similarity flow. -/
structure InvariantReadout where
  state : BdGBlock ℝ → ℝ
  invariant : ∀ mu X, state (chiralSimilarityFlow mu X) = state X

/-- Package an invariant readout as the repository's KMS readout datum. -/
def InvariantReadout.toKMSReadoutDatum
    (R : InvariantReadout) (beta : ℝ) (hbeta : 0 < beta) :
    InfoGeometry.OperatorAlgebra.HorizonKMS.KMSReadoutDatum (BdGBlock ℝ) where
  flow := chiralSimilarityFlow
  state := R.state
  beta := beta
  beta_pos := hbeta
  flow_zero := chiralSimilarityFlow_zero
  flow_add := chiralSimilarityFlow_add
  flow_invariant := R.invariant

def traceInvariantReadout : InvariantReadout where
  state := chiralTrace
  invariant := chiralTrace_flow_invariant

def chiralSimilarityKMSReadoutDatum
    (beta : ℝ) (hbeta : 0 < beta) :
    InfoGeometry.OperatorAlgebra.HorizonKMS.KMSReadoutDatum (BdGBlock ℝ) :=
  InvariantReadout.toKMSReadoutDatum traceInvariantReadout beta hbeta

end

end InfoGeometry.Physics.Thermodynamics
