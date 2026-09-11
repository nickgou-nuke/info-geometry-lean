import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

namespace InfoGeometry.Canonical.IBMeasure

variable {T : Type*} [MeasurableSpace T]

/--
Unnormalized exponential tilt `dν = exp (-f) dμ`.

We avoid the name `Measure.tilted` here because mathlib already reserves it for
the normalized Esscher transform.
-/
noncomputable def tiltedMeasure (μ : Measure T) (f : T → ℝ) : Measure T :=
  μ.withDensity (fun t => ENNReal.ofReal (Real.exp (-f t)))

lemma tiltedMeasure_apply {μ : Measure T} {f : T → ℝ} {s : Set T}
    (hs : MeasurableSet s) :
    tiltedMeasure μ f s = ∫⁻ t in s, ENNReal.ofReal (Real.exp (-f t)) ∂μ := by
  unfold tiltedMeasure
  rw [withDensity_apply _ hs]

lemma rnDeriv_tiltedMeasure {μ : Measure T} {f : T → ℝ}
    (hf : Measurable f) [SigmaFinite μ] :
    (tiltedMeasure μ f).rnDeriv μ =ᵐ[μ]
      fun t => ENNReal.ofReal (Real.exp (-f t)) := by
  unfold tiltedMeasure
  exact Measure.rnDeriv_withDensity μ
    (ENNReal.measurable_ofReal.comp (hf.neg.exp))

/-- Partition function of the unnormalized exponential tilt. -/
noncomputable def partitionFunction (μ : Measure T) (f : T → ℝ) : ℝ≥0∞ :=
  tiltedMeasure μ f Set.univ

lemma partitionFunction_eq_lintegral {μ : Measure T} {f : T → ℝ} :
    partitionFunction μ f = ∫⁻ t, ENNReal.ofReal (Real.exp (-f t)) ∂μ := by
  simp [partitionFunction, tiltedMeasure_apply]

section IB

variable {X : Type*} [Nonempty T]

/-- The unnormalized Gibbs slice for fixed `x`. -/
noncomputable def IBUnnormalized
    (qT : Measure T) (β : ℝ) (D : X → T → ℝ) (x : X) : Measure T :=
  tiltedMeasure qT (fun t => β * D x t)

/-- The corresponding partition function. -/
noncomputable def IBPartitionFunction
    (qT : Measure T) (β : ℝ) (D : X → T → ℝ) (x : X) : ℝ≥0∞ :=
  partitionFunction qT (fun t => β * D x t)

lemma IBPartitionFunction_eq_lintegral
    (qT : Measure T) (β : ℝ) (D : X → T → ℝ) (x : X) :
    IBPartitionFunction qT β D x
      =
    ∫⁻ t, ENNReal.ofReal (Real.exp (-(β * D x t))) ∂qT := by
  simpa [IBPartitionFunction, IBUnnormalized] using
    (partitionFunction_eq_lintegral (μ := qT) (f := fun t => β * D x t))

theorem rnDeriv_IBUnnormalized_eq
    (qT : Measure T) (β : ℝ) (D : X → T → ℝ) (x : X)
    (hβD : Measurable (fun t => β * D x t)) [SigmaFinite qT] :
    (IBUnnormalized qT β D x).rnDeriv qT =ᵐ[qT]
      fun t => ENNReal.ofReal (Real.exp (-(β * D x t))) := by
  simpa [IBUnnormalized] using
    (rnDeriv_tiltedMeasure (μ := qT) (f := fun t => β * D x t) hβD)

/-- Normalization of a finite measure into a probability measure. -/
noncomputable def IBNormalize (μ : FiniteMeasure T) : ProbabilityMeasure T :=
  μ.normalize

theorem IBNormalize_toMeasure_eq_inv_mass_smul_of_nonzero
    (μ : FiniteMeasure T) (hμ : μ ≠ 0) :
    ((IBNormalize μ : ProbabilityMeasure T) : Measure T) = μ.mass⁻¹ • (μ : Measure T) := by
  simpa [IBNormalize] using μ.toMeasure_normalize_eq_of_nonzero hμ

/-- Distortion observable in the sign convention compatible with `Measure.tilted`. -/
noncomputable def distortionRV
    (D : X → T → ℝ) (x : X) : T → ℝ :=
  fun t => -D x t

/-- Mathlib-native normalized Gibbs/Esscher measure. -/
noncomputable def IBGibbsMeasure
    (qT : Measure T) (β : ℝ) (D : X → T → ℝ) (x : X) : Measure T :=
  qT.tilted (fun t => β * distortionRV D x t)

/--
Bundled Gibbs probability measure, assuming the exponential tilt is genuinely
integrable and the base measure is nonzero.
-/
noncomputable def IBGibbsProb
    (qT : Measure T) [NeZero qT]
    (β : ℝ) (D : X → T → ℝ) (x : X)
    (hInt : Integrable (fun t => Real.exp (β * distortionRV D x t)) qT) :
    ProbabilityMeasure T := by
  let _ : IsProbabilityMeasure (IBGibbsMeasure qT β D x) := by
    simpa [IBGibbsMeasure, distortionRV] using
      (MeasureTheory.isProbabilityMeasure_tilted
        (μ := qT) (f := fun t => β * distortionRV D x t) hInt)
  exact ⟨IBGibbsMeasure qT β D x, inferInstance⟩

section Gibbs

variable (qT : Measure T) [IsProbabilityMeasure qT]
variable (β : ℝ) (D : X → T → ℝ) (x : X)
variable [IsFiniteMeasure (IBUnnormalized qT β D x)]

/-- Normalized Gibbs update for the fixed slice `x`. -/
noncomputable def IBGibbs : ProbabilityMeasure T :=
  IBNormalize ⟨IBUnnormalized qT β D x, inferInstance⟩

omit [IsProbabilityMeasure qT] in
theorem IBGibbs_eq_unnormalized_smul_partition
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    (IBGibbs qT β D x : Measure T)
      = (IBPartitionFunction qT β D x)⁻¹ • IBUnnormalized qT β D x := by
  let μf : FiniteMeasure T := ⟨IBUnnormalized qT β D x, inferInstance⟩
  have hμf : μf ≠ 0 := by
    intro h
    apply h_nz
    simpa [μf] using congrArg (fun ν : FiniteMeasure T => ((ν : Measure T))) h
  have hnorm_mass :
      (μf.normalize : Measure T) = μf.mass⁻¹ • (μf : Measure T) := by
    simpa using μf.toMeasure_normalize_eq_of_nonzero hμf
  have hnorm :
      (μf.normalize : Measure T) = (((μf : Measure T) Set.univ)⁻¹) • (μf : Measure T) := by
    calc
      (μf.normalize : Measure T) = μf.mass⁻¹ • (μf : Measure T) := by
        exact hnorm_mass
      _ = (((μf : Measure T) Set.univ)⁻¹) • (μf : Measure T) := by
        ext s hs
        rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul,
          ENNReal.coe_inv (μf.mass_nonzero_iff.mpr hμf), FiniteMeasure.ennreal_mass]
  have hmass :
      ((μf : Measure T) Set.univ) = IBPartitionFunction qT β D x := by
    simp [μf, IBPartitionFunction, IBUnnormalized, partitionFunction, tiltedMeasure]
  calc
    (IBGibbs qT β D x : Measure T) = (μf.normalize : Measure T) := by
      rfl
    _ = (((μf : Measure T) Set.univ)⁻¹) • (μf : Measure T) := by
      exact hnorm
    _ = (IBPartitionFunction qT β D x)⁻¹ • IBUnnormalized qT β D x := by
      rw [hmass]
      simp [μf]

theorem rnDeriv_IBGibbs_eq
    (hD : Measurable (fun t => β * D x t))
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    ((IBGibbs qT β D x : Measure T).rnDeriv qT) =ᵐ[qT]
      fun t => (IBPartitionFunction qT β D x)⁻¹
        * ENNReal.ofReal (Real.exp (-(β * D x t))) := by
  rw [IBGibbs_eq_unnormalized_smul_partition (qT := qT) (β := β) (D := D) (x := x) h_nz]
  let μf : FiniteMeasure T := ⟨IBUnnormalized qT β D x, inferInstance⟩
  have hμf : μf ≠ 0 := by
    intro h
    apply h_nz
    simpa [μf] using congrArg (fun ν : FiniteMeasure T => ((ν : Measure T))) h
  have hmass_nonzero : ((μf.mass : ℝ≥0∞)) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (μf.mass_nonzero_iff.mpr hμf)
  have hpart_nonzero : IBPartitionFunction qT β D x ≠ 0 := by
    simpa [μf, IBPartitionFunction, IBUnnormalized, partitionFunction, tiltedMeasure,
      FiniteMeasure.ennreal_mass] using hmass_nonzero
  have htop : (IBPartitionFunction qT β D x)⁻¹ ≠ ⊤ := by
    exact ENNReal.inv_ne_top.mpr hpart_nonzero
  have hsmul :
      (((IBPartitionFunction qT β D x)⁻¹ • IBUnnormalized qT β D x).rnDeriv qT) =ᵐ[qT]
        (IBPartitionFunction qT β D x)⁻¹ • (IBUnnormalized qT β D x).rnDeriv qT :=
    Measure.rnDeriv_smul_left_of_ne_top
      (ν := IBUnnormalized qT β D x)
      (μ := qT)
      (r := (IBPartitionFunction qT β D x)⁻¹)
      htop
  have htilt :
      (IBUnnormalized qT β D x).rnDeriv qT =ᵐ[qT]
        fun t => ENNReal.ofReal (Real.exp (-(β * D x t))) := by
    simpa [IBUnnormalized] using
      rnDeriv_tiltedMeasure (μ := qT) (f := fun t => β * D x t) hD
  have hmul :
      (fun t =>
        (IBPartitionFunction qT β D x)⁻¹ • ((IBUnnormalized qT β D x).rnDeriv qT t))
        =ᵐ[qT]
      fun t =>
        (IBPartitionFunction qT β D x)⁻¹
          * ENNReal.ofReal (Real.exp (-(β * D x t))) := by
    filter_upwards [htilt] with t ht
    simp [smul_eq_mul, ht]
  exact hsmul.trans hmul

end Gibbs

end IB

end InfoGeometry.Canonical.IBMeasure
