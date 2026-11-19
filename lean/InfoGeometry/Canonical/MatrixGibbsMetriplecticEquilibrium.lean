/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixGibbsEntropy
import InfoGeometry.Canonical.MatrixUnitarySpectralOrthogonality

/-!
# Actual Gibbs stationarity for the existing matrix metriplectic expression

The trace-normalized Gibbs density commutes with its own Hamiltonian. Its
logarithmic free-energy score at temperature `β⁻¹` is a central matrix, rather
than a matrix that must vanish. A complex-linear mobility that annihilates the
identity therefore annihilates this actual score, and the existing full state
evolution expression vanishes at the Gibbs state.

The mobility condition `M 1 = 0` is explicit. It is not inferred from positivity
and does not by itself assert positivity or trace preservation of an integrated
flow. The theorem is algebraic stationarity of the existing vector-field
expression; uniqueness, convergence, a free-energy minimization theorem, and
identification of the score with a Frechet derivative remain separate results.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixGibbsMetriplecticEquilibrium

open FiniteMatrixGibbsFunctional PolarFrameTraceDensity MatrixGibbsEntropy
open MatrixUnitarySpectralOrthogonality MetriplecticDissipation
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- Trace normalization preserves the native CFC centralizer relation. -/
theorem normalizedGibbsDensity_commutes
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    Commute (normalizedGibbsDensity H hH β) H := by
  have hcomm : Commute (gibbsDensity H hH β) H := by
    rw [gibbsDensity, ← hH.cfc_eq]
    have hsa : IsSelfAdjoint H := hH
    exact hsa.commute_cfc (Commute.refl H) (expWeight β)
  change Commute
    ((traceMass (gibbsDensity H hH β))⁻¹ • gibbsDensity H hH β) H
  exact hcomm.smul_left _

/-- The Gibbs state is stationary under the reversible flow of its own
Hamiltonian, for every real inverse-temperature parameter. -/
theorem unitaryFlow_normalizedGibbsDensity_eq_zero
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    unitaryFlow H (normalizedGibbsDensity H hH β) = 0 := by
  have hcomm := normalizedGibbsDensity_commutes H hH β
  dsimp only [unitaryFlow, MetriplecticDissipation.commutator]
  rw [← hcomm.eq, sub_self, smul_zero]

variable [Nonempty n]

/-- At the actual normalized Gibbs state, the score is the central
trace-constraint multiplier. It is not generally the zero matrix. -/
theorem freeEnergyScore_normalizedGibbsDensity
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0) :
    freeEnergyScore H (normalizedGibbsDensity H hH β) β⁻¹ =
      (β⁻¹ * (1 - Real.log (gibbsPartition H hH β))) • (1 : Mat) := by
  have hinv : β⁻¹ * (-β) = -1 := by
    rw [mul_neg, inv_mul_cancel₀ hβ]
  rw [freeEnergyScore, log_normalizedGibbsDensity H hH β]
  simp only [smul_add, smul_sub, smul_smul, hinv, neg_one_smul]
  rw [mul_sub, mul_one, sub_smul]
  abel

/-- The mobility's response to the Gibbs score is determined exactly by its
response to the identity, using native scalar restriction of the linear map. -/
theorem map_freeEnergyScore_normalizedGibbsDensity
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0)
    (M : Mat →ₗ[ℂ] Mat) :
    M (freeEnergyScore H (normalizedGibbsDensity H hH β) β⁻¹) =
      (β⁻¹ * (1 - Real.log (gibbsPartition H hH β))) • M (1 : Mat) := by
  rw [freeEnergyScore_normalizedGibbsDensity H hH β hβ,
    M.map_smul_of_tower]

theorem map_freeEnergyScore_normalizedGibbsDensity_eq_zero
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0)
    (M : Mat →ₗ[ℂ] Mat) (hM : M (1 : Mat) = 0) :
    M (freeEnergyScore H (normalizedGibbsDensity H hH β) β⁻¹) = 0 := by
  rw [map_freeEnergyScore_normalizedGibbsDensity H hH β hβ M,
    hM, smul_zero]

/-- The exact Gibbs-state readout of the existing full evolution expression.
No sign or symmetry hypothesis on the mobility is needed for this identity. -/
theorem stateEvolution_normalizedGibbsDensity
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0)
    (M : Mat →ₗ[ℂ] Mat) :
    stateEvolution
        ⟨normalizedGibbsDensity H hH β, H,
          freeEnergyScore H (normalizedGibbsDensity H hH β) β⁻¹, M⟩ =
      -((β⁻¹ * (1 - Real.log (gibbsPartition H hH β))) • M (1 : Mat)) := by
  change unitaryFlow H (normalizedGibbsDensity H hH β) -
    M (freeEnergyScore H (normalizedGibbsDensity H hH β) β⁻¹) = _
  rw [unitaryFlow_normalizedGibbsDensity_eq_zero,
    map_freeEnergyScore_normalizedGibbsDensity H hH β hβ M, zero_sub]

/-- An identity-annihilating mobility makes the actual Gibbs density a
stationary point of the existing matrix metriplectic vector-field expression. -/
theorem stateEvolution_normalizedGibbsDensity_eq_zero_of_map_one
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0)
    (M : Mat →ₗ[ℂ] Mat) (hM : M (1 : Mat) = 0) :
    stateEvolution
        ⟨normalizedGibbsDensity H hH β, H,
          freeEnergyScore H (normalizedGibbsDensity H hH β) β⁻¹, M⟩ = 0 := by
  rw [stateEvolution_normalizedGibbsDensity H hH β hβ M,
    hM, smul_zero, neg_zero]

end InfoGeometry.Canonical.MatrixGibbsMetriplecticEquilibrium
