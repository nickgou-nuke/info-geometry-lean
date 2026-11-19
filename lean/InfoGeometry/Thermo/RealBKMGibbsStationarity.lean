/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.RealBKMConstrainedForce
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Actual real Gibbs normalization at constrained stationarity

The spectral surprisal exponentiates to the supplied faithful density. If this
surprisal is affine in the identity and an arbitrary real matrix energy, the
matrix exponential and trace derive the normalized Gibbs formula. The affine
identity coefficient is then the logarithm of the actual matrix partition
function.

A zero constrained surprisal supplies this affine relation. The normalization
claim is conditional on that stationary equation; the Gram coefficient need
not equal a Gibbs log-partition function away from stationarity. These are
identities in the full real matrix algebra and do not supply a state evolution
or a convergence theorem.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealBKMGibbsStationarity

open KuboMoriBogoliubov ConstrainedBilinearProjection RealBKMConstrainedForce

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exponentiating the actual negative surprisal recovers the spectral density. -/
theorem exp_neg_spectralSurprisal (rho : FaithfulDensityState n) :
    NormedSpace.exp (-spectralSurprisal rho) = Matrix.diagonal rho.eigenvalues := by
  rw [spectralSurprisal, Matrix.diagonal_neg, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, neg_neg, ← Real.exp_eq_exp_ℝ, Real.exp_log (rho.p_pos i)]

private theorem exp_scalar_identity (a : ℝ) :
    NormedSpace.exp (a • (1 : Matrix n n ℝ)) =
      Real.exp a • (1 : Matrix n n ℝ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal,
    Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]

/-- An actual affine surprisal relation determines both the real matrix Gibbs
density and its normalization coefficient. No commutativity of the ambient
matrix algebra is assumed. -/
theorem gibbs_normalization_of_affine_surprisal
    (rho : FaithfulDensityState n) (H : Matrix n n ℝ) (α β : ℝ)
    (haff : spectralSurprisal rho = α • 1 + β • H) :
    let Z := Matrix.trace (NormedSpace.exp ((-β) • H))
    0 < Z ∧ α = Real.log Z ∧
      Matrix.diagonal rho.eigenvalues = Z⁻¹ • NormedSpace.exp ((-β) • H) := by
  dsimp only
  have hcomm : Commute ((-α) • (1 : Matrix n n ℝ)) ((-β) • H) :=
    (Commute.one_left ((-β) • H)).smul_left (-α)
  have hneg : -(α • (1 : Matrix n n ℝ) + β • H) =
      (-α) • (1 : Matrix n n ℝ) + (-β) • H := by
    simp only [neg_add, neg_smul]
  have hexp : Matrix.diagonal rho.eigenvalues =
      Real.exp (-α) • NormedSpace.exp ((-β) • H) := by
    rw [← exp_neg_spectralSurprisal rho, haff, hneg,
      Matrix.exp_add_of_commute _ _ hcomm, exp_scalar_identity,
      smul_mul_assoc, one_mul]
  have htrace : 1 = Real.exp (-α) * Matrix.trace (NormedSpace.exp ((-β) • H)) := by
    simpa only [Matrix.trace_diagonal, rho.p_sum, Matrix.trace_smul, smul_eq_mul] using
      congrArg Matrix.trace hexp
  have hZ : Matrix.trace (NormedSpace.exp ((-β) • H)) = Real.exp α := by
    have ht := congrArg (fun z : ℝ => Real.exp α * z) htrace
    rw [mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, one_mul] at ht
    exact ht.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ]
    exact Real.exp_pos α
  · rw [hZ, Real.log_exp]
  · rw [hZ, ← Real.exp_neg]
    exact hexp

/-- Zero constrained surprisal gives a normalized Gibbs density with the
actual Gram coefficients. Nonscalar energy is not needed for this implication:
the zero residual itself already supplies the full affine identity. -/
theorem normalized_gibbs_of_constrainedSurprisal_eq_zero
    (rho : FaithfulDensityState n) (H : Matrix n n ℝ)
    (hstationary : constrainedSurprisal rho H = 0) :
    let α := identityCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho)
    let β := energyCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho)
    let Z := Matrix.trace (NormedSpace.exp ((-β) • H))
    0 < Z ∧ α = Real.log Z ∧
      Matrix.diagonal rho.eigenvalues = Z⁻¹ • NormedSpace.exp ((-β) • H) := by
  let α := identityCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho)
  let β := energyCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho)
  have hres : spectralSurprisal rho - α • 1 - β • H = 0 := by
    change spectralSurprisal rho -
        identityCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho) • 1 -
        energyCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho) • H = 0
    rw [← projection_eq_sub]
    exact hstationary
  have haff : spectralSurprisal rho = α • 1 + β • H :=
    (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hres)).trans (add_comm _ _)
  exact gibbs_normalization_of_affine_surprisal rho H α β haff

end InfoGeometry.Thermo.RealBKMGibbsStationarity
