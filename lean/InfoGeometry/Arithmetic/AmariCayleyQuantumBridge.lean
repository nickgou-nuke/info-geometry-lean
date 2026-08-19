import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
import InfoGeometry.Arithmetic.AmariZetaDuallyFlatGeometry
import InfoGeometry.Canonical.AmariBinarySimplexBridge
import InfoGeometry.Clifford.ThermodynamicZetaGeometry
import InfoGeometry.Krein.FiniteCovarianceMajoranaBlock
import InfoGeometry.TraceFormula.ColimitTrace
import InfoGeometry.Clifford.CliffordBitWordEquivalence

/-!
# Amari--Cayley quantum bridge

This file is a theorem-safe integration layer for the native arithmetic,
thermal, and colimit-trace owners.  It records finite algebraic readouts only;
it does not assert a Weil-positivity theorem or an unconditional spectral
confinement result.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.AmariCayleyQuantumBridge

open Complex
open InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
open InfoGeometry.Arithmetic.AmariZeta
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
open InfoGeometry.Clifford.ThermodynamicZetaGeometry
open InfoGeometry.Krein.FiniteCovarianceMajoranaBlock
open InfoGeometry.TraceFormula.ColimitTrace
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open BostConnesThermofield

theorem lanes_eq_fermi_particle_hole (θ : ℝ) :
    homogeneousLanes (occupation .FD θ : ℂ) =
      ((occupation .FD θ : ℂ), (1 - (occupation .FD θ : ℂ))) := by
  rfl

@[simp] theorem lanes_sum_one (s : ℂ) :
    (homogeneousLanes s).1 + (homogeneousLanes s).2 = 1 := by
  simp [homogeneousLanes]

theorem tau_eq_maxwell_boltzmann_fugacity (θ : ℝ) :
    homogeneousTau (homogeneousLanes (occupation .FD θ : ℂ)) =
      (occupation .MB θ : ℂ) := by
  dsimp [homogeneousTau, homogeneousLanes]
  rw [occupation_FD, occupation_MB]
  push_cast
  exact_mod_cast fermiSimplexCoordinate_crossRatio θ

def boseOccupationOfLanes (z : HomogeneousLane) : ℂ :=
  z.1 / (z.2 - z.1)

theorem bose_occupation_from_lanes (s : ℂ) :
    boseOccupationOfLanes (homogeneousLanes s) = s / (1 - 2 * s) := by
  simp [boseOccupationOfLanes, homogeneousLanes]
  congr 1
  ring

@[simp] theorem bose_denominator_vanishes_at_seam :
    (homogeneousLanes (1 / 2 : ℂ)).2 -
        (homogeneousLanes (1 / 2 : ℂ)).1 = 0 := by
  norm_num [homogeneousLanes]

theorem fisher_metric_eq_fermi_variance (θ : ℝ) :
    fisherRaoMetric (occupation .FD θ : ℂ) =
      ((occupation .FD θ * (1 - occupation .FD θ) : ℝ) : ℂ) := by
  simp [fisherRaoMetric]

/-! The covariance block exposes the same Fisher variance at the genuine
finite matrix level: its coherence entry is a square root factorization of
the Bernoulli variance. -/

theorem covarianceProjection_offDiag_sq_eq_fermi_variance (θ : ℝ) :
    (covarianceProjection (occupation .FD θ) 0 1) ^ 2 =
      occupation .FD θ * (1 - occupation .FD θ) := by
  change
    (Real.sqrt (occupation .FD θ) *
        Real.sqrt (1 - occupation .FD θ)) ^ 2 =
      occupation .FD θ * (1 - occupation .FD θ)
  have h₀ : 0 ≤ occupation .FD θ :=
    (occupation_FD_pos θ).le
  have h₁ : 0 ≤ 1 - occupation .FD θ :=
    (sub_nonneg.mpr (occupation_FD_lt_one θ).le)
  calc
    (Real.sqrt (occupation .FD θ) *
        Real.sqrt (1 - occupation .FD θ)) ^ 2 =
        (Real.sqrt (occupation .FD θ) * Real.sqrt (occupation .FD θ)) *
          (Real.sqrt (1 - occupation .FD θ) *
            Real.sqrt (1 - occupation .FD θ)) := by ring
    _ = occupation .FD θ * (1 - occupation .FD θ) := by
      rw [Real.mul_self_sqrt h₀, Real.mul_self_sqrt h₁]

theorem covarianceProjection_offDiag_sq_eq_fisher_metric (θ : ℝ) :
    ((covarianceProjection (occupation .FD θ) 0 1) ^ 2 : ℂ) =
      fisherRaoMetric (occupation .FD θ : ℂ) := by
  rw [fisher_metric_eq_fermi_variance]
  rw [← Complex.ofReal_pow]
  exact congrArg (fun x : ℝ => (x : ℂ))
    (covarianceProjection_offDiag_sq_eq_fermi_variance θ)

theorem binary_fisherExp_eq_fermi_variance (θ : ℝ) :
    (InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp θ : ℂ) =
      fisherRaoMetric (occupation .FD θ : ℂ) := by
  simp [InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp,
    InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic,
    fisherRaoMetric, occupation_FD,
    InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry.fermiSimplexCoordinate,
    add_comm]

theorem covarianceProjection_offDiag_sq_eq_fisherExp (θ : ℝ) :
    ((covarianceProjection (occupation .FD θ) 0 1) ^ 2 : ℂ) =
      (InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp θ : ℂ) := by
  rw [covarianceProjection_offDiag_sq_eq_fisher_metric,
    binary_fisherExp_eq_fermi_variance]

theorem covarianceProjection_offDiag_sq_eq_fisherExp_real (θ : ℝ) :
    (covarianceProjection (occupation .FD θ) 0 1) ^ 2 =
      InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp θ := by
  exact_mod_cast covarianceProjection_offDiag_sq_eq_fisherExp θ

theorem tauInfinity_fermi_covarianceProjection (θ : ℝ) :
    InfoGeometry.TraceFormula.ColimitTrace.tauInfinity
        (toColimit 1
          ((bitWordStageEquivFin 1).symm
            (covarianceProjection (occupation .FD θ)))) =
      (1 / 2 : ℝ) := by
  rw [tauInfinity_bitWordStageEquivFin_symm]
  rw [covarianceProjection_trace]
  norm_num

theorem tauInfinity_fermi_fundamentalSymmetry (θ : ℝ) :
    InfoGeometry.TraceFormula.ColimitTrace.tauInfinity
        (toColimit 1
          ((bitWordStageEquivFin 1).symm
            (fundamentalSymmetry (occupation .FD θ)))) = 0 := by
  rw [tauInfinity_bitWordStageEquivFin_symm]
  rw [fundamentalSymmetry_trace]
  norm_num

theorem tauInfinity_commonCarrier_fermi_covarianceProjection (θ : ℝ) :
    InfoGeometry.TraceFormula.ColimitTrace.tauInfinity
        (cliffordBitWordColimitEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 1
            ((clStageEquiv 1).symm
              ((bitWordStageEquivFin 1).symm
                (covarianceProjection (occupation .FD θ)))))) =
      (1 / 2 : ℝ) := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  exact tauInfinity_fermi_covarianceProjection θ

theorem tauInfinity_commonCarrier_fermi_fundamentalSymmetry (θ : ℝ) :
    InfoGeometry.TraceFormula.ColimitTrace.tauInfinity
        (cliffordBitWordColimitEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 1
            ((clStageEquiv 1).symm
              ((bitWordStageEquivFin 1).symm
                (fundamentalSymmetry (occupation .FD θ)))))) = 0 := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  exact tauInfinity_fermi_fundamentalSymmetry θ

theorem fermi_covariance_projection_idempotent (θ : ℝ) :
    covarianceProjection (occupation .FD θ) *
        covarianceProjection (occupation .FD θ) =
      covarianceProjection (occupation .FD θ) := by
  apply covarianceProjection_sq
  · exact (occupation_FD_pos θ).le
  · exact (occupation_FD_lt_one θ).le

theorem tauInfinity_fermi_covarianceProjection_quadratic (θ : ℝ) :
    InfoGeometry.TraceFormula.ColimitTrace.tauInfinity
        (toColimit 1
          ((bitWordStageEquivFin 1).symm
            (covarianceProjection (occupation .FD θ) *
              covarianceProjection (occupation .FD θ)))) =
      (1 / 2 : ℝ) := by
  rw [fermi_covariance_projection_idempotent]
  exact tauInfinity_fermi_covarianceProjection θ

theorem tauInfinity_commonCarrier_fermi_covarianceProjection_quadratic
    (θ : ℝ) :
    InfoGeometry.TraceFormula.ColimitTrace.tauInfinity
        (cliffordBitWordColimitEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage 1
            ((clStageEquiv 1).symm
              ((bitWordStageEquivFin 1).symm
                (covarianceProjection (occupation .FD θ) *
                  covarianceProjection (occupation .FD θ)))))) =
      (1 / 2 : ℝ) := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  exact tauInfinity_fermi_covarianceProjection_quadratic θ

theorem fermi_fundamental_symmetry_involution (θ : ℝ) :
    fundamentalSymmetry (occupation .FD θ) *
        fundamentalSymmetry (occupation .FD θ) = 1 := by
  apply fundamentalSymmetry_sq
  · exact (occupation_FD_pos θ).le
  · exact (occupation_FD_lt_one θ).le

theorem fisher_variance_on_critical_line (t : ℝ) :
    fisherRaoMetric ((1 / 2 : ℂ) + I * (t : ℂ)) =
      ((1 / 4 : ℝ) + t ^ 2 : ℂ) :=
  fisherRaoMetric_on_critical_line t

theorem primon_susy_bridge (β : ℝ) (hβ : β > 1) :
    (riemannZeta (β : ℂ)) *
        (moebiusLSeriesReadout β : ℂ) = 1 := by
  rw [moebius_readout_eq_reciprocal_riemannZeta β hβ]
  apply mul_inv_cancel₀
  apply riemannZeta_ne_zero_of_one_lt_re
  simpa using hβ

theorem tauInfinity_bridge (n : ℕ) (M : MatrixStage n) :
    InfoGeometry.TraceFormula.ColimitTrace.tauInfinity (toColimit n M) =
      normalizedTrace n M :=
  tauInfinity_evaluate_ringhom n M

end InfoGeometry.Arithmetic.AmariCayleyQuantumBridge
