import InfoGeometry.Canonical.IBMeasure
import InfoGeometry.MeasureProjective
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

namespace IBGaugeBridge

open InfoGeometry.Canonical.IBMeasure
open InfoGeometry.MeasureProjective
open InfoGeometry.MeasureProjective.ProjectiveState

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]

/-- Additive gauge shift of the distortion observable. -/
def distortionShift (D : X → T → ℝ) (c : ℝ) : X → T → ℝ :=
  fun x t => D x t + c

/-- The raw IB slice viewed as a nonzero unnormalized projective state. -/
noncomputable def ibNonzeroUState
    (qT : Measure T) (β : ℝ) (D : X → T → ℝ) (x : X)
    [IsFiniteMeasure (IBUnnormalized qT β D x)]
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    NonzeroUState T := by
  let μf : UState T := ⟨IBUnnormalized qT β D x, inferInstance⟩
  have hμf : μf ≠ 0 := by
    intro h
    apply h_nz
    simpa [μf] using congrArg (fun ν : FiniteMeasure T => ((ν : Measure T))) h
  exact ⟨μf, hμf⟩

/-- The raw IB slice modulo positive projective rescaling. -/
noncomputable def ibProjectiveState
    (qT : Measure T) (β : ℝ) (D : X → T → ℝ) (x : X)
    [IsFiniteMeasure (IBUnnormalized qT β D x)]
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    ProjectiveState T :=
  Quotient.mk (sameRaySetoid (α := T)) (ibNonzeroUState qT β D x h_nz)

@[simp] theorem ibProjectiveState_normalize_eq_IBGibbs
    (qT : Measure T) [IsProbabilityMeasure qT]
    (β : ℝ) (D : X → T → ℝ) (x : X)
    [IsFiniteMeasure (IBUnnormalized qT β D x)]
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    ProjectiveState.normalize (ibProjectiveState qT β D x h_nz) = IBGibbs qT β D x := by
  simp [ibProjectiveState, ibNonzeroUState, IBGibbs, IBNormalize]

/-- Additive distortion shifts rescale the raw unnormalized Gibbs slice by a positive constant. -/
theorem IBUnnormalized_shift_eq_smul
    (qT : Measure T) (β c : ℝ) (D : X → T → ℝ) (x : X)
    (hβD : Measurable (fun t => β * D x t)) :
    IBUnnormalized qT β (distortionShift D c) x
      =
    ENNReal.ofReal (Real.exp (-β * c)) • IBUnnormalized qT β D x := by
  unfold IBUnnormalized tiltedMeasure distortionShift
  have h_density :
      (fun t => ENNReal.ofReal (Real.exp (-(β * (D x t + c)))))
        =
      ENNReal.ofReal (Real.exp (-β * c)) •
        fun t => ENNReal.ofReal (Real.exp (-(β * D x t))) := by
    funext t
    have h_arg : -(β * (D x t + c)) = -β * c + -(β * D x t) := by ring
    have hnonneg : 0 ≤ Real.exp (-β * c) := by positivity
    calc
      ENNReal.ofReal (Real.exp (-(β * (D x t + c))))
          = ENNReal.ofReal (Real.exp (-β * c) * Real.exp (-(β * D x t))) := by
              rw [h_arg, Real.exp_add]
      _ = ENNReal.ofReal (Real.exp (-β * c)) * ENNReal.ofReal (Real.exp (-(β * D x t))) := by
              simpa using
                (ENNReal.ofReal_mul
                  (p := Real.exp (-β * c))
                  (q := Real.exp (-(β * D x t)))
                  hnonneg)
      _ = (ENNReal.ofReal (Real.exp (-β * c)) •
            fun t => ENNReal.ofReal (Real.exp (-(β * D x t)))) t := by
              simp [Pi.smul_apply, smul_eq_mul]
  rw [h_density]
  simpa using
    (withDensity_smul
      (μ := qT)
      (r := ENNReal.ofReal (Real.exp (-β * c)))
      (f := fun t => ENNReal.ofReal (Real.exp (-(β * D x t))))
      (ENNReal.measurable_ofReal.comp (hβD.neg.exp)))

/-- The partition function transforms radially under additive distortion shifts. -/
theorem IBPartitionFunction_shift_eq_smul
    (qT : Measure T) (β c : ℝ) (D : X → T → ℝ) (x : X)
    (hβD : Measurable (fun t => β * D x t)) :
    IBPartitionFunction qT β (distortionShift D c) x
      =
    ENNReal.ofReal (Real.exp (-β * c)) * IBPartitionFunction qT β D x := by
  have hUniv :
      IBUnnormalized qT β (distortionShift D c) x Set.univ
        =
      (ENNReal.ofReal (Real.exp (-β * c)) • IBUnnormalized qT β D x) Set.univ := by
    exact congrArg
      (fun μ : Measure T => μ Set.univ)
      (IBUnnormalized_shift_eq_smul (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD)
  simpa [IBPartitionFunction, partitionFunction, Measure.smul_apply, smul_eq_mul] using hUniv

/-- Nonzero raw slices stay nonzero under additive gauge shifts. -/
theorem IBUnnormalized_shift_ne_zero
    (qT : Measure T) (β c : ℝ) (D : X → T → ℝ) (x : X)
    (hβD : Measurable (fun t => β * D x t))
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    IBUnnormalized qT β (distortionShift D c) x ≠ 0 := by
  rw [IBUnnormalized_shift_eq_smul (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD]
  intro hzero
  apply h_nz
  apply Measure.measure_univ_eq_zero.mp
  have huniv :
      ENNReal.ofReal (Real.exp (-β * c)) * IBUnnormalized qT β D x Set.univ = 0 := by
    simpa [Measure.smul_apply, smul_eq_mul] using congrArg (fun μ : Measure T => μ Set.univ) hzero
  rcases mul_eq_zero.mp huniv with hconst | hmass
  · have hc0 : ENNReal.ofReal (Real.exp (-β * c)) ≠ 0 := by
        positivity
    exact False.elim (hc0 hconst)
  · simpa [IBPartitionFunction, partitionFunction] using hmass

/-- The normalized Gibbs slice is invariant under additive gauge shifts of the distortion. -/
theorem IBGibbs_shift_eq
    (qT : Measure T) [IsProbabilityMeasure qT]
    (β c : ℝ) (D : X → T → ℝ) (x : X)
    [IsFiniteMeasure (IBUnnormalized qT β D x)]
    [IsFiniteMeasure (IBUnnormalized qT β (distortionShift D c) x)]
    (hβD : Measurable (fun t => β * D x t))
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    IBGibbs qT β (distortionShift D c) x = IBGibbs qT β D x := by
  let r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-β * c))
  have hr0 : r ≠ 0 := by
    positivity
  have hrTop : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_shift_nz :
      IBUnnormalized qT β (distortionShift D c) x ≠ 0 :=
    IBUnnormalized_shift_ne_zero (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD h_nz
  have hpart0 : IBPartitionFunction qT β D x ≠ 0 := by
    intro hpart
    apply h_nz
    exact Measure.measure_univ_eq_zero.mp <| by simpa [IBPartitionFunction, partitionFunction] using hpart
  ext s hs
  rw [IBGibbs_eq_unnormalized_smul_partition (qT := qT) (β := β)
      (D := distortionShift D c) (x := x) h_shift_nz]
  rw [IBGibbs_eq_unnormalized_smul_partition (qT := qT) (β := β) (D := D) (x := x) h_nz]
  rw [IBPartitionFunction_shift_eq_smul (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD]
  rw [IBUnnormalized_shift_eq_smul (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD]
  rw [Measure.smul_apply, Measure.smul_apply, Measure.smul_apply]
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have hscalar :
      (r * IBPartitionFunction qT β D x)⁻¹ * r = (IBPartitionFunction qT β D x)⁻¹ := by
    calc
      (r * IBPartitionFunction qT β D x)⁻¹ * r
          = r / (r * IBPartitionFunction qT β D x) := by
              rw [← ENNReal.div_eq_inv_mul]
      _ = 1 / IBPartitionFunction qT β D x := by
            simpa using
              (ENNReal.mul_div_mul_left
                (a := 1)
                (b := IBPartitionFunction qT β D x)
                (c := r)
                hr0 hrTop)
      _ = (IBPartitionFunction qT β D x)⁻¹ := by simp [div_eq_mul_inv]
  rw [← mul_assoc, hscalar]

/-- The mathlib-native normalized tilt is invariant under additive gauge shifts. -/
theorem IBGibbsMeasure_shift_eq
    (qT : Measure T) [NeZero qT]
    (β c : ℝ) (D : X → T → ℝ) (x : X)
    (hInt : Integrable (fun t => Real.exp (β * distortionRV D x t)) qT) :
    IBGibbsMeasure qT β (distortionShift D c) x = IBGibbsMeasure qT β D x := by
  have h_fun :
      (fun t => β * distortionRV (distortionShift D c) x t)
        =
      fun t => β * distortionRV D x t + (-β * c) := by
    funext t
    simp [distortionShift, distortionRV]
    ring
  rw [IBGibbsMeasure, h_fun]
  calc
    qT.tilted (fun t => β * distortionRV D x t + -β * c)
      = (qT.tilted (fun t => β * distortionRV D x t)).tilted (fun _ => -β * c) := by
          simpa using
            (MeasureTheory.tilted_tilted
              (μ := qT)
              (f := fun t => β * distortionRV D x t)
              (hf := hInt)
              (g := fun _ => -β * c)).symm
    _ = qT.tilted (fun t => β * distortionRV D x t) := by
          let _ : IsProbabilityMeasure (qT.tilted (fun t => β * distortionRV D x t)) :=
            MeasureTheory.isProbabilityMeasure_tilted
              (μ := qT) (f := fun t => β * distortionRV D x t) hInt
          simpa using
            (MeasureTheory.tilted_const
              (μ := qT.tilted (fun t => β * distortionRV D x t))
              (-β * c))

/-- Additive distortion shifts do not move the raw IB slice in projective state space. -/
theorem ibProjectiveState_eq_of_shift
    (qT : Measure T) [IsProbabilityMeasure qT]
    (β c : ℝ) (D : X → T → ℝ) (x : X)
    [IsFiniteMeasure (IBUnnormalized qT β D x)]
    [IsFiniteMeasure (IBUnnormalized qT β (distortionShift D c) x)]
    (hβD : Measurable (fun t => β * D x t))
    (h_nz : IBUnnormalized qT β D x ≠ 0) :
    ibProjectiveState qT β (distortionShift D c) x
      (IBUnnormalized_shift_ne_zero
        (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD h_nz)
      =
    ibProjectiveState qT β D x h_nz := by
  apply Quotient.sound
  change
    (ibNonzeroUState qT β (distortionShift D c) x
      (IBUnnormalized_shift_ne_zero
        (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD h_nz)).1.normalize
      =
    (ibNonzeroUState qT β D x h_nz).1.normalize
  simpa [ibNonzeroUState, IBGibbs, IBNormalize] using
    (IBGibbs_shift_eq
      (qT := qT) (β := β) (c := c) (D := D) (x := x) hβD h_nz)

end IBGaugeBridge
