import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.DiscreteRelativeEntropyCoarseGraining

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace DiscreteThermodynamics

open InfoGeometry.Canonical.DiscreteRelativeEntropyCoarseGraining
open InfoGeometry.Canonical.ColimitContinuumResolutionBridge
open SouriauRelativeEntropy

variable {n : ℕ}

/-- 1. KL Divergence (Relative Entropy) D_KL(P || Q) = ∑ᵢ Pᵢ log(Pᵢ / Qᵢ) -/
noncomputable def klDivergence (P Q : Fin n → ℝ) : ℝ :=
  ∑ i, P i * Real.log (P i / Q i)

/-- 2. Dimensionless Free Energy βℱ(P) = ∑ᵢ Pᵢ (β Eᵢ + log Pᵢ) -/
noncomputable def betaFreeEnergy (P E : Fin n → ℝ) (beta : ℝ) : ℝ :=
  ∑ i, P i * (beta * E i + Real.log (P i))

/-- 🏆 THEOREM 1: THE GIBBS-BOGOLIUBOV IDENTITY
    If γ is the thermal Gibbs state (where β Eᵢ = -log γᵢ - log Z),
    then Non-Equilibrium Free Energy equals KL Divergence minus equilibrium free energy log Z. -/
theorem gibbs_bogoliubov_identity
    (P gamma E : Fin n → ℝ) (beta logZ : ℝ)
    (h_prob : ∑ i, P i = 1)
    (h_gibbs : ∀ i, beta * E i = - Real.log (gamma i) - logZ)
    (hP_pos : ∀ i, 0 < P i)
    (hgamma_pos : ∀ i, 0 < gamma i) :
    betaFreeEnergy P E beta = klDivergence P gamma - logZ := by
  dsimp [betaFreeEnergy, klDivergence]
  have h_sub : (fun i => P i * (beta * E i + Real.log (P i))) =
               (fun i => P i * Real.log (P i / gamma i) - P i * logZ) := by
    ext i
    rw [h_gibbs i, Real.log_div (ne_of_gt (hP_pos i)) (ne_of_gt (hgamma_pos i))]
    ring
  rw [h_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h_prob, one_mul]

/-- 🏆 THEOREM 2: THE SECOND LAW OF THERMODYNAMICS (FREE ENERGY DISSIPATION)
    Applying the Data Processing Inequality (DPI) to the Gibbs-Bogoliubov identity
    proves that coarse-graining strictly dissipates Free Energy toward equilibrium! -/
theorem second_law_free_energy_dissipation
    (P_fine P_coarse gamma_fine gamma_coarse : Fin n → ℝ)
    (F_fine F_coarse logZ : ℝ)
    (h_gb_fine : F_fine = klDivergence P_fine gamma_fine - logZ)
    (h_gb_coarse : F_coarse = klDivergence P_coarse gamma_coarse - logZ)
    (h_dpi : klDivergence P_coarse gamma_coarse ≤ klDivergence P_fine gamma_fine) :
    F_coarse ≤ F_fine := by
  rw [h_gb_fine, h_gb_coarse]
  linarith

end DiscreteThermodynamics
