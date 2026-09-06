import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

namespace InfoGeometry.LLM.SphericalVMF

open MeasureTheory ProbabilityTheory Metric Set
open scoped RealInnerProductSpace

noncomputable section

/-- The unit sphere in a real normed vector space. -/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Metric.sphere (0 : E) 1

section SphereObservable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Linear spin observable associated with a natural-parameter direction. -/
def spinObservable (v : E) (s : UnitSphere E) : ℝ :=
  ⟪v, (s : E)⟫_ℝ

@[simp] theorem norm_coe_unitSphere (s : UnitSphere E) : ‖(s : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp s.property

theorem continuous_spinObservable (v : E) : Continuous (spinObservable v) := by
  unfold spinObservable
  fun_prop

theorem abs_spinObservable_le_norm (v : E) (s : UnitSphere E) :
    |spinObservable v s| ≤ ‖v‖ := by
  calc
    |spinObservable v s| ≤ ‖v‖ * ‖(s : E)‖ := by
      simpa [spinObservable] using (abs_real_inner_le_norm v (s : E))
    _ = ‖v‖ := by rw [norm_coe_unitSphere, mul_one]

theorem spinObservable_mem_Icc (v : E) (s : UnitSphere E) :
    spinObservable v s ∈ Set.Icc (-‖v‖) ‖v‖ := by
  have h := abs_spinObservable_le_norm v s
  exact ⟨neg_le_of_abs_le h, le_of_abs_le h⟩

/-- Every exponential moment of a spherical linear observable is finite. -/
theorem integrable_exp_mul_spinObservable
    (σ : Measure (UnitSphere E)) [IsFiniteMeasure σ]
    (t : ℝ) (v : E) :
    Integrable (fun s => Real.exp (t * spinObservable v s)) σ := by
  exact ProbabilityTheory.integrable_exp_mul_of_mem_Icc
    (a := -‖v‖) (b := ‖v‖)
    (continuous_spinObservable v).aemeasurable
    (Filter.Eventually.of_forall (spinObservable_mem_Icc v))

/-- The exponential-integrability domain of a spherical linear observable is all of `ℝ`. -/
theorem integrableExpSet_spinObservable_eq_univ
    (σ : Measure (UnitSphere E)) [IsFiniteMeasure σ] (v : E) :
    ProbabilityTheory.integrableExpSet (spinObservable v) σ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  change Integrable (fun s => Real.exp (t * spinObservable v s)) σ
  exact integrable_exp_mul_spinObservable σ t v

/-- Every real parameter lies in the analytic interior of the spherical CGF domain. -/
theorem mem_interior_integrableExpSet_spinObservable
    (σ : Measure (UnitSphere E)) [IsFiniteMeasure σ] (v : E) (t : ℝ) :
    t ∈ interior (ProbabilityTheory.integrableExpSet (spinObservable v) σ) := by
  rw [integrableExpSet_spinObservable_eq_univ]
  simp

/-- The integral of the ambient spin vector exists for every finite measure on the unit sphere. -/
theorem integrable_coe_unitSphere
    [CompleteSpace E] (σ : Measure (UnitSphere E)) [IsFiniteMeasure σ] :
    Integrable (fun s : UnitSphere E => (s : E)) σ := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards with s
  simp

end SphereObservable

section HaarProbability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Finite rotation-invariant measure induced on the unit sphere by an additive Haar measure. -/
noncomputable def sphereHaarFinite
    (μ : Measure E) [μ.IsAddHaarMeasure] : FiniteMeasure (UnitSphere E) :=
  ⟨μ.toSphere, inferInstance⟩

/-- Canonical probability normalization of the Haar-induced unit-sphere measure. -/
noncomputable def sphereHaarProbability
    (μ : Measure E) [μ.IsAddHaarMeasure] : ProbabilityMeasure (UnitSphere E) := by
  letI : Nonempty (UnitSphere E) :=
    Set.nonempty_coe_sort.mpr (NormedSpace.sphere_nonempty.mpr zero_le_one)
  exact (sphereHaarFinite μ).normalize

@[simp] theorem sphereHaarProbability_apply_univ
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (sphereHaarProbability μ : Measure (UnitSphere E)) Set.univ = 1 := by
  exact measure_univ

end HaarProbability

section ExponentialFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

variable (σ : Measure (UnitSphere E)) [IsProbabilityMeasure σ]

/-- Integral partition function of the spherical exponential family in natural parameter `θ`. -/
noncomputable def partition (θ : E) : ℝ :=
  ∫ s, Real.exp (spinObservable θ s) ∂σ

/-- Log-partition (Massieu) potential of the spherical exponential family. -/
noncomputable def logPartition (θ : E) : ℝ :=
  Real.log (partition σ θ)

/-- The von Mises--Fisher law as Mathlib's normalized exponential (Esscher) tilt. -/
noncomputable def law (θ : E) : Measure (UnitSphere E) :=
  σ.tilted (spinObservable θ)

instance instIsProbabilityMeasureLaw (θ : E) : IsProbabilityMeasure (law σ θ) := by
  apply MeasureTheory.isProbabilityMeasure_tilted
  simpa using integrable_exp_mul_spinObservable σ 1 θ

/-- The spherical partition is the MGF of the linear observable at parameter `1`. -/
theorem partition_eq_mgf_one (θ : E) :
    partition σ θ = ProbabilityTheory.mgf (spinObservable θ) σ 1 := by
  simp [partition, ProbabilityTheory.mgf]

/-- Strict positivity of the spherical partition function. -/
theorem partition_pos (θ : E) : 0 < partition σ θ := by
  rw [partition_eq_mgf_one]
  exact ProbabilityTheory.mgf_pos (integrable_exp_mul_spinObservable σ 1 θ)

/-- Mean spin (magnetization response) under the tilted spherical law. -/
noncomputable def response (θ : E) : E :=
  ∫ s, (s : E) ∂(law σ θ)

/-- A projected response is the expectation of the corresponding spin observable. -/
theorem integral_spinObservable_eq_inner_response (θ v : E) :
    (∫ s, spinObservable v s ∂(law σ θ)) = ⟪v, response σ θ⟫_ℝ := by
  simpa [spinObservable, response] using
    (integral_inner (μ := law σ θ) (integrable_coe_unitSphere (law σ θ)) v)

/-- Exact line increment of the log-partition potential. -/
noncomputable def directionalPotential (θ v : E) (t : ℝ) : ℝ :=
  logPartition σ (θ + t • v) - logPartition σ θ

/-- Tilting first by `θ` and then in direction `v` gives the ratio of spherical partitions. -/
theorem mgf_under_law_eq_partition_ratio (θ v : E) (t : ℝ) :
    ProbabilityTheory.mgf (spinObservable v) (law σ θ) t =
      partition σ (θ + t • v) / partition σ θ := by
  have htilt := MeasureTheory.integral_exp_tilted
    (μ := σ) (f := spinObservable θ)
    (g := fun s : UnitSphere E => t * spinObservable v s)
  calc
    ProbabilityTheory.mgf (spinObservable v) (law σ θ) t =
        (∫ s, Real.exp (spinObservable θ s + t * spinObservable v s) ∂σ) /
          (∫ s, Real.exp (spinObservable θ s) ∂σ) := by
            simpa [ProbabilityTheory.mgf, law] using htilt
    _ = partition σ (θ + t • v) / partition σ θ := by
          unfold partition
          congr 1
          apply integral_congr_ae
          filter_upwards with s
          congr 1
          simp [spinObservable, real_inner_add_left, real_inner_smul_left]

/-- The directional log-partition increment is exactly the CGF under the base tilted law. -/
theorem directionalPotential_eq_cgf (θ v : E) (t : ℝ) :
    directionalPotential σ θ v t =
      ProbabilityTheory.cgf (spinObservable v) (law σ θ) t := by
  unfold directionalPotential logPartition ProbabilityTheory.cgf
  rw [mgf_under_law_eq_partition_ratio]
  exact (Real.log_div (partition_pos σ (θ + t • v)).ne'
    (partition_pos σ θ).ne').symm

/-- First directional derivative of the log partition equals projected mean spin. -/
theorem deriv_directionalPotential_zero_eq_inner_response (θ v : E) :
    deriv (directionalPotential σ θ v) 0 = ⟪v, response σ θ⟫_ℝ := by
  have hfun : directionalPotential σ θ v =
      ProbabilityTheory.cgf (spinObservable v) (law σ θ) := by
    funext t
    exact directionalPotential_eq_cgf σ θ v t
  rw [hfun]
  have h0 : 0 ∈ interior
      (ProbabilityTheory.integrableExpSet (spinObservable v) (law σ θ)) :=
    mem_interior_integrableExpSet_spinObservable (law σ θ) v 0
  have hder := ProbabilityTheory.integral_tilted_mul_self
    (μ := law σ θ) (X := spinObservable v) (t := 0) h0
  calc
    deriv (ProbabilityTheory.cgf (spinObservable v) (law σ θ)) 0 =
        ∫ s, spinObservable v s ∂(law σ θ) := by
          simpa using hder.symm
    _ = ⟪v, response σ θ⟫_ℝ :=
      integral_spinObservable_eq_inner_response σ θ v

/-- Covariance bilinear form of the spherical sufficient statistic. -/
noncomputable def covarianceHessian (θ u v : E) : ℝ :=
  ProbabilityTheory.covariance (spinObservable u) (spinObservable v) (law σ θ)

/-- Symmetry of the covariance Hessian. -/
theorem covarianceHessian_symm (θ u v : E) :
    covarianceHessian σ θ u v = covarianceHessian σ θ v u := by
  exact ProbabilityTheory.covariance_comm _ _

/-- Positive semidefiniteness of the covariance Hessian. -/
theorem covarianceHessian_nonneg (θ v : E) :
    0 ≤ covarianceHessian σ θ v v := by
  rw [covarianceHessian, ProbabilityTheory.covariance_self
    (continuous_spinObservable v).aemeasurable]
  exact ProbabilityTheory.variance_nonneg _ _

/-- Second directional derivative of the log partition equals the covariance Hessian. -/
theorem iteratedDeriv_two_directionalPotential_zero_eq_covarianceHessian
    (θ v : E) :
    iteratedDeriv 2 (directionalPotential σ θ v) 0 =
      covarianceHessian σ θ v v := by
  have hfun : directionalPotential σ θ v =
      ProbabilityTheory.cgf (spinObservable v) (law σ θ) := by
    funext t
    exact directionalPotential_eq_cgf σ θ v t
  rw [hfun]
  have h0 : 0 ∈ interior
      (ProbabilityTheory.integrableExpSet (spinObservable v) (law σ θ)) :=
    mem_interior_integrableExpSet_spinObservable (law σ θ) v 0
  have hvar := ProbabilityTheory.variance_tilted_mul
    (μ := law σ θ) (X := spinObservable v) (t := 0) h0
  calc
    iteratedDeriv 2 (ProbabilityTheory.cgf (spinObservable v) (law σ θ)) 0 =
        ProbabilityTheory.variance (spinObservable v) (law σ θ) := by
          simpa using hvar.symm
    _ = covarianceHessian σ θ v v := by
      rw [covarianceHessian, ProbabilityTheory.covariance_self
        (continuous_spinObservable v).aemeasurable]

end ExponentialFamily

end
end InfoGeometry.LLM.SphericalVMF
