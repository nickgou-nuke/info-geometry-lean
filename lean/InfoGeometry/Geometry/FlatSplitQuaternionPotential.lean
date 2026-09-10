import InfoGeometry.Geometry.FlatSplitQuaternionGeometry
import InfoGeometry.Geometry.QuadraticPotentialCalculus
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

/-!
# The determinant potential on the existing split-quaternion regular module

This extends the repository's `M₂(ℝ)` metric and `Cl(1,1)` action. The metric
has signature `(2,2)`, whereas the two-dimensional spinor module alone is too
small for a para-hyperkähler tangent space. Native derivatives recover the
metric and the three exact alternating forms. All constructions are flat.
-/

noncomputable section

namespace InfoGeometry.Geometry.FlatSplitQuaternion

open InfoGeometry.Clifford.SplitAtom
open QuadraticPotentialCalculus
open scoped Matrix.Norms.Elementwise

/-- The existing bilinear metric, bundled continuously in finite dimension. -/
def metricCLM : Mat2 →L[ℝ] Mat2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Mat2 →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (Mat2 →L[ℝ] ℝ)).toLinearMap.comp metric)

@[simp] theorem metricCLM_apply (u v : Mat2) : metricCLM u v = metric u v := rfl

def determinantPotential : Mat2 → ℝ := potential metricCLM

theorem determinantPotential_eq (x : Mat2) :
    determinantPotential x = x.det / 2 := by
  change metric x x / 2 = _
  rw [metric_self]

theorem determinantPotential_fderiv (x u : Mat2) :
    fderiv ℝ determinantPotential x u = metric x u := by
  rw [determinantPotential, fderiv_potential metricCLM metric_symm]
  rfl

theorem determinantPotential_hessian (x u v : Mat2) :
    fderiv ℝ (fderiv ℝ determinantPotential) x u v = metric u v := by
  rw [determinantPotential, hessian_potential metricCLM metric_symm]
  rfl

theorem metric_nondegenerate (u : Mat2) (hu : ∀ v, metric u v = 0) : u = 0 := by
  have h00 := hu !![0, 0; 0, 1]
  have h11 := hu !![1, 0; 0, 0]
  have h01 := hu !![0, 0; 1, 0]
  have h10 := hu !![0, 1; 0, 0]
  norm_num [metric_apply] at h00 h11 h01 h10
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem metric_left_infinitesimal (a u v : Mat2) :
    metric (a * u) v + metric u (a * v) = a.trace * metric u v := by
  simp [metric_apply, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]
  ring

theorem metric_left_skew (a : Mat2) (ha : a.trace = 0) (u v : Mat2) :
    metric (a * u) v = -metric u (a * v) := by
  have h := metric_left_infinitesimal a u v
  rw [ha, zero_mul] at h
  linarith

def leftCLM (a : Mat2) : Mat2 →L[ℝ] Mat2 :=
  LinearMap.toContinuousLinearMap (leftAction a)

@[simp] theorem leftCLM_apply (a u : Mat2) : leftCLM a u = a * u := rfl

theorem split_generators_traceless : I.trace = 0 ∧ J.trace = 0 ∧ K.trace = 0 := by
  norm_num [I, J, K, InfoGeometry.Clifford.Cl11Matrix.Eminus,
    InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.J1,
    Matrix.trace, Fin.sum_univ_two]

/-- All three fundamental forms arise from the same quadratic potential. -/
theorem split_triad_exact (x u v : Mat2) :
    extDeriv (potentialOneForm metricCLM (leftCLM I)) x ![u, v] = metric (I * u) v ∧
    extDeriv (potentialOneForm metricCLM (leftCLM J)) x ![u, v] = metric (J * u) v ∧
    extDeriv (potentialOneForm metricCLM (leftCLM K)) x ![u, v] = metric (K * u) v := by
  have h (a : Mat2) (ha : a.trace = 0) :=
    extDeriv_potentialOneForm metricCLM metric_symm (leftCLM a)
      (metric_left_skew a ha) x u v
  exact ⟨h I split_generators_traceless.1,
    h J split_generators_traceless.2.1, h K split_generators_traceless.2.2⟩

theorem fundamental_form_alternating (a : Mat2) (ha : a.trace = 0) (u : Mat2) :
    metric (a * u) u = 0 := by
  have h := metric_left_skew a ha u u
  rw [metric_symm u (a * u)] at h
  linarith

theorem fundamental_form_nondegenerate (a : Mat2) (ha : a.det ≠ 0)
    (u : Mat2) (hu : ∀ v, metric (a * u) v = 0) : u = 0 := by
  have h := metric_nondegenerate (a * u) hu
  have hh := congrArg (fun z : Mat2 => a⁻¹ * z) h
  simpa [← mul_assoc, Matrix.nonsing_inv_mul a (isUnit_iff_ne_zero.mpr ha)] using hh

theorem determinantPotential_smul (r : ℝ) (x : Mat2) :
    determinantPotential (r • x) = r ^ 2 * determinantPotential x :=
  potential_smul metricCLM r x

/-- Every determinant-one left action preserves the potential, including K, A and N in SL₂. -/
theorem determinantPotential_left_SL (a : Mat2) (ha : a.det = 1) (x : Mat2) :
    determinantPotential (a * x) = determinantPotential x := by
  simp only [determinantPotential_eq, Matrix.det_mul, ha, one_mul]

theorem traceless_flow_tangent_to_potential (a : Mat2) (ha : a.trace = 0) (x : Mat2) :
    fderiv ℝ determinantPotential x (a * x) = 0 := by
  rw [determinantPotential_fderiv, metric_symm]
  exact fundamental_form_alternating a ha x

/-- Euler scaling is transverse to nonzero levels, unlike the SL₂ split torus. -/
theorem euler_not_tangent_at_nonzero (x : Mat2) (hx : determinantPotential x ≠ 0) :
    fderiv ℝ determinantPotential x x ≠ 0 := by
  change fderiv ℝ (potential metricCLM) x x ≠ 0
  rw [euler_identity metricCLM metric_symm]
  exact mul_ne_zero (by norm_num) hx

/-- A nonzero null point has the same nondegenerate ambient Hessian as every point. -/
theorem null_point_regular_ambient_hessian :
    (Pplus : Mat2) ≠ 0 ∧ determinantPotential Pplus = 0 ∧
      (∀ u, (∀ v, fderiv ℝ (fderiv ℝ determinantPotential) Pplus u v = 0) → u = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun a : Mat2 => a 0 0) h
    norm_num [Pplus, InfoGeometry.Algebra.HypercomplexTriad.Pplus,
      InfoGeometry.Algebra.HypercomplexTriad.E] at h00
  · norm_num [determinantPotential_eq, Pplus,
      InfoGeometry.Algebra.HypercomplexTriad.Pplus,
      InfoGeometry.Algebra.HypercomplexTriad.E, Matrix.det_fin_two]
  · intro u hu
    apply metric_nondegenerate u
    simpa only [determinantPotential_hessian] using hu

end InfoGeometry.Geometry.FlatSplitQuaternion
