import proofs.PrimonBosonFermionDuality
import proofs.PrimonHilbertPolyaSeparation
import proofs.UHFInductiveColimit

noncomputable section

namespace PrimonCoarseGraining

open PrimonBosonFermionDuality
open PrimonHilbertPolyaSeparation
open UHFInductiveColimit

/-! Finite cutoff error for the Boson--Möbius identity. -/
def truncationError (p : ℕ) (β : ℝ) (K : ℕ) : ℝ :=
  (primeBoltzmannWeight p β) ^ (K + 1)

/-- The finite duality restated with truncation error:
  Z_K^boson · Z_mobius = 1 - ε_K -/
theorem duality_with_truncation (p : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β K * singlePrimeMobiusPartition p β =
    1 - truncationError p β K :=
  finite_boson_mobius_duality p β K

/-! Definitional readout of the finite cutoff error. -/
theorem truncationError_formula (p : ℕ) (β : ℝ) (K : ℕ) :
    truncationError p β K = (primeBoltzmannWeight p β) ^ (K + 1) := rfl

theorem truncationError_tendsto_zero_of_abs_lt_one
    (p : ℕ) (β : ℝ)
    (h : |primeBoltzmannWeight p β| < 1) :
    Filter.Tendsto (fun K : ℕ => truncationError p β K)
      Filter.atTop (nhds 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one h
  have hshift := hp.comp (Filter.tendsto_add_atTop_nat 1)
  simpa [truncationError, Function.comp_def] using hshift

theorem singlePrimeBosonPartition_tendsto_geometric
    (p : ℕ) (β : ℝ)
    (h : |primeBoltzmannWeight p β| < 1) :
    Filter.Tendsto
      (fun K : ℕ => singlePrimeBosonPartition p β K)
      Filter.atTop
      (nhds ((1 - primeBoltzmannWeight p β)⁻¹)) := by
  have hsum : HasSum
      (fun k : ℕ => (primeBoltzmannWeight p β) ^ k)
      ((1 - primeBoltzmannWeight p β)⁻¹) := by
    simpa [Real.norm_eq_abs] using
      (hasSum_geometric_of_norm_lt_one (K := ℝ) h)
  have hlim := hsum.tendsto_sum_nat
  have hshift := hlim.comp (Filter.tendsto_add_atTop_nat 1)
  simpa [singlePrimeBosonPartition, bosonOccupationWeight, Function.comp_def] using hshift

/-! At zero inverse temperature the finite cutoff error is constant. -/
theorem truncationError_at_hagedorn (p : ℕ) (K : ℕ) :
    truncationError p 0 K = 1 := by
  simp [truncationError, primeBoltzmannWeight]

/-! ## Finite cutoff recurrences -/

/-! Finite cutoff metadata. -/
structure CoarseGrainingScale where
  K : ℕ
  bosonicPartition : ℝ  -- Z_K^boson(p,β) at this scale
  truncationError : ℝ   -- ε_K = p^{-(K+1)β}
  hagedornDivergence : truncationError = 1 → K = 0 ∨ β = 0
  resolutionParameter : Prop  -- K as UV cutoff: higher K = finer resolution

/-! The zero-cutoff readout. -/
theorem vacuum_scale_coarse_graining (p : ℕ) (β : ℝ) :
    singlePrimeBosonPartition p β 0 = 1 ∧
    truncationError p β 0 = primeBoltzmannWeight p β := by
  simp [singlePrimeBosonPartition, bosonOccupationWeight,
    truncationError, primeBoltzmannWeight]

/-! The finite cutoff recurrence. -/
theorem rg_step_adds_occupation (p : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β (K + 1) =
    singlePrimeBosonPartition p β K + (primeBoltzmannWeight p β) ^ (K + 1) := by
  simp [singlePrimeBosonPartition, bosonOccupationWeight,
    Finset.sum_range_succ]

/-! ## Optional Lee--Yang data -/

/-! Optional fields for a future limiting Lee--Yang construction. -/
structure LeeYangRGFlow where
  partitionAtScale : ℕ → ℝ → ℝ       -- K ↦ Z_K(β)
  finiteScaleNoZeros : Prop          -- ∀ K β, Z_K(β) > 0
  zerosInLimitOnly : Prop            -- zeros of Z_∞(s) are Lee-Yang condensation
  cptCriticalLine : Prop             -- zeros condense on Re(s)=1/2
  coarseGrainingScale : CoarseGrainingScale

/-! Optional metadata for relating a finite cutoff to a Cantor stage. -/

structure PrimonRGToCantorWeld where
  coarseGrainingScale : CoarseGrainingScale
  cantorStage : ℕ                  -- DiagAlg n stage
  cutIsFractal : Prop              -- DiagAlg n ≅ self-similar cut of Cantor
  primonPartitionAtFiniteStage : ℝ  -- Z_K(p,β) evaluated at finite stage
  renormalizationFlowStable : Prop  -- symmetries preserved under RG

end PrimonCoarseGraining

end noncomputable section
