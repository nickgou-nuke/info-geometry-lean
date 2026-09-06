import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-!
# Finite CFC / Banach-exponential Gibbs reconciliation

The repository has two finite Gibbs constructions on different theorem lanes:

* `FiniteMatrixGibbsFunctional.gibbsDensity`, defined by the Hermitian
  continuous functional calculus with the scalar weight `r ↦ exp (-β r)`;
* the Banach-algebra exponential used by the Fréchet/Duhamel Gibbs calculus.

For a Hermitian finite matrix these are the same unnormalised weight.  This
owner proves that equality using Mathlib's native CFC composition/scaling API
and `CFC.real_exp_eq_normedSpace_exp`, then propagates it to the normalized
matrix density and through the repository's canonical `matrixOp` coordinate
transport.

No diagonalisation, spectral witness, or second density carrier is introduced.
The final operator statement is deliberately transport of the proved matrix
equality; it does not silently assert an additional theorem identifying the
matrix exponential transport with an independently constructed operator
exponential.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge

open Matrix
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-- The CFC Gibbs weight is exactly the Banach-algebra exponential of the
scaled Hermitian generator. -/
theorem cfcGibbsDensity_eq_normedSpace_exp
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensity H hH β =
      NormedSpace.exp ((-β : ℝ) • H) := by
  rw [gibbsDensity, ← hH.cfc_eq]
  rw [← CFC.real_exp_eq_normedSpace_exp
    (a := ((-β : ℝ) • H))]
  rw [← cfc_smul_id (R := ℝ) (-β) H]
  rw [← cfc_comp Real.exp ((-β) • ·) H]
  apply cfc_congr
  intro r hr
  simp [expWeight, Function.comp_def, smul_eq_mul]

/-- Trace partition functions of the CFC and Banach-exponential weights agree. -/
theorem cfcPartition_eq_normedSpaceExpPartition
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix.trace (gibbsDensity H hH β) =
      Matrix.trace (NormedSpace.exp ((-β : ℝ) • H)) := by
  rw [cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- The normalized density associated with the existing CFC Gibbs functional. -/
noncomputable def cfcNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix n n ℂ :=
  (Matrix.trace (gibbsDensity H hH β))⁻¹ • gibbsDensity H hH β

/-- The same normalized density written with the Banach-algebra exponential. -/
noncomputable def normedExpNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (β : ℝ) : Matrix n n ℂ :=
  (Matrix.trace (NormedSpace.exp ((-β : ℝ) • H)))⁻¹ •
    NormedSpace.exp ((-β : ℝ) • H)

/-- Normalization does not introduce a second state: both constructions are
definitionally the same after the CFC/exponential reconciliation theorem. -/
theorem cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    cfcNormalizedGibbsDensity H hH β =
      normedExpNormalizedGibbsDensity H β := by
  unfold cfcNormalizedGibbsDensity normedExpNormalizedGibbsDensity
  rw [cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- Canonical bounded-operator transport of the unnormalised Gibbs equality. -/
theorem matrixOp_cfcGibbsDensity_eq_normedSpaceExpWeight
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOp (gibbsDensity H hH β) =
      matrixOp (NormedSpace.exp ((-β : ℝ) • H)) := by
  exact congrArg matrixOp
    (cfcGibbsDensity_eq_normedSpace_exp H hH β)

/-- Canonical bounded-operator transport of the normalized Gibbs state. -/
theorem matrixOp_cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOp (cfcNormalizedGibbsDensity H hH β) =
      matrixOp (normedExpNormalizedGibbsDensity H β) := by
  exact congrArg matrixOp
    (cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity
      H hH β)

/-- Reading the transported CFC weight back to matrix coordinates recovers the
same Banach-exponential weight exactly. -/
theorem matrixOfOp_matrixOp_cfcGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOfOp (matrixOp (gibbsDensity H hH β)) =
      NormedSpace.exp ((-β : ℝ) • H) := by
  rw [matrixOfOp_matrixOp,
    cfcGibbsDensity_eq_normedSpace_exp H hH β]

end InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge
