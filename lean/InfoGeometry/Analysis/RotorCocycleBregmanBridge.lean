import InfoGeometry.Analysis.BregmanAnalyticBound
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebraic.MatrixAutomorphyFactor
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import DAG.AffineProjectiveClosure

noncomputable section

/-!
# Rotor cocycle / Bregman bridge: finite theorem packet

This file now exposes only kernel-checked finite identities already available
from the matrix-Bregman and modular-sign owner files. It does not prove any
particle/hole anomaly cancellation, β = 1 phase-transition theorem, or CPT
invariance of a residue functional.
-/

namespace InfoGeometry.Analysis.RotorCocycleBregmanBridge

open InfoGeometry.Analysis.BregmanAnalyticBound
open InfoGeometry.OperatorAlgebra.ModularSignCPT

/-- The matrix exponential remainder vanishes at time `0`. -/
@[simp] theorem exponentialRemainder_zero {n : ℕ} (K : MatrixEnd n) :
    exponentialRemainder K 0 = 0 :=
  InfoGeometry.Analysis.BregmanAnalyticBound.exponentialRemainder_zero K

/-- The packet readout of a modular Hamiltonian is the same matrix expression. -/
theorem packet_exponentialRemainder_eq {n : ℕ}
    (H : MatrixModularHamiltonian n) (ε : ℝ) :
    H.exponentialRemainder ε =
      (NormedSpace.exp (ε • H.K) : MatrixEnd n) - 1 - (ε • H.K : MatrixEnd n) :=
  MatrixModularHamiltonian.exponentialRemainder_eq H ε

/-- A self-concordant Dikin envelope forces nonnegativity of the Bregman term. -/
theorem matrix_bregman_nonneg_of_dikin_envelope {n : ℕ}
    {D : MatrixEnd n → MatrixEnd n → ℝ}
    {localRadius : MatrixEnd n → MatrixEnd n → ℝ}
    (hsc : HasMatrixSelfConcordantDikinEnvelope D localRadius)
    (x y : MatrixEnd n) :
    0 ≤ D x y :=
  InfoGeometry.Analysis.BregmanAnalyticBound.matrix_bregman_nonneg_of_dikin_envelope hsc x y

/-- The Dikin sandwich gives the lower/upper bounds on the Bregman term. -/
theorem matrix_dikin_sandwich_of_selfConcordant_envelope {n : ℕ}
    {D : MatrixEnd n → MatrixEnd n → ℝ}
    {localRadius : MatrixEnd n → MatrixEnd n → ℝ}
    (hsc : HasMatrixSelfConcordantDikinEnvelope D localRadius)
    (x y : MatrixEnd n)
    (hsmall : localRadius x y < 1) :
    dikinOmega (localRadius x y) ≤ D x y ∧
      D x y ≤ dikinOmegaStar (localRadius x y) :=
  InfoGeometry.Analysis.BregmanAnalyticBound.matrix_dikin_sandwich_of_selfConcordant_envelope hsc x y hsmall

/-- The generated modular phase axis squares to `-1`. -/
theorem Kmod_square {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ModularSignCPTRelations H) :
    R.Kmod.comp R.Kmod = -(1 : EndR H) :=
  R.Kmod_square

/-- The datum-level complex structure also squares to `-1`. -/
theorem complexStructure_square {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : ModularSignCPTDatum H) :
    M.complexStructure.comp M.complexStructure = -(1 : EndR H) :=
  M.complexStructure_square

/--
Open theorem debt for this bridge.

Any statement about anomaly cancellation, particle/hole cancellation, or CPT
transport of a trace/residue must be added later with explicit operator,
functional, and conjugation hypotheses.
-/
def rotor_cocycle_bregman_debt : String :=
  "Open: add residue/trace-level CPT and anomaly statements only as theorem-shaped claims with explicit hypotheses."

end InfoGeometry.Analysis.RotorCocycleBregmanBridge
