import InfoGeometry.Geometry.FlatSplitQuaternionPotential

/-!
# The flat `(2n,2n)` family

Finite products of the existing split-quaternion regular module. The scalar
potential is the sum of half-determinants. The explicit signature formula,
nondegeneracy, split-quaternion relations, Hessian, and three exact closed
forms all refer to this same carrier. There is no curvature or manifold
classification claim.
-/

noncomputable section

namespace InfoGeometry.Geometry.FlatSplitQuaternion

open InfoGeometry.Clifford.SplitAtom
open QuadraticPotentialCalculus
open scoped Matrix.Norms.Elementwise

abbrev Family (n : ℕ) := Fin n → Mat2

def familyMetric (n : ℕ) : Family n →L[ℝ] Family n →L[ℝ] ℝ :=
  ∑ i : Fin n,
    ((metricCLM.precompR (Family n)).flip (ContinuousLinearMap.proj i)).comp
      (ContinuousLinearMap.proj i)

@[simp] theorem familyMetric_apply {n : ℕ} (u v : Family n) :
    familyMetric n u v = ∑ i, metric (u i) (v i) := by
  simp [familyMetric, ContinuousLinearMap.precompR]

theorem familyMetric_symm {n : ℕ} (u v : Family n) :
    familyMetric n u v = familyMetric n v u := by
  simp only [familyMetric_apply, metric_symm]

theorem familyMetric_nondegenerate {n : ℕ} (u : Family n)
    (hu : ∀ v, familyMetric n u v = 0) : u = 0 := by
  funext i
  apply metric_nondegenerate (u i)
  intro v
  have h := hu (Pi.single i v)
  simpa only [familyMetric_apply, Pi.single_apply, apply_ite, map_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

def familyPotential (n : ℕ) : Family n → ℝ := potential (familyMetric n)

theorem familyPotential_eq_sum {n : ℕ} (x : Family n) :
    familyPotential n x = ∑ i, determinantPotential (x i) := by
  simp only [familyPotential, potential, familyMetric_apply, determinantPotential_eq,
    metric_self, Finset.sum_div]

theorem familyPotential_hessian {n : ℕ} (x u v : Family n) :
    fderiv ℝ (fderiv ℝ (familyPotential n)) x u v = familyMetric n u v := by
  rw [familyPotential, hessian_potential (familyMetric n) familyMetric_symm]

theorem family_signature {n : ℕ} (a b c d : Fin n → ℝ) :
    familyMetric n (fun i => a i • 1 + b i • I + c i • J + d i • K)
      (fun i => a i • 1 + b i • I + c i • J + d i • K) =
        ∑ i, ((a i) ^ 2 + (b i) ^ 2 - (c i) ^ 2 - (d i) ^ 2) := by
  simp only [familyMetric_apply, metric_signature_formula]

def familyAction (n : ℕ) (a : Mat2) : Family n →L[ℝ] Family n :=
  ContinuousLinearMap.pi fun i => (leftCLM a).comp (ContinuousLinearMap.proj i)

@[simp] theorem familyAction_apply {n : ℕ} (a : Mat2) (x : Family n) (i : Fin n) :
    familyAction n a x i = a * x i := rfl

theorem family_I_sq (n : ℕ) :
    (familyAction n I).comp (familyAction n I) = -ContinuousLinearMap.id ℝ (Family n) := by
  ext x i
  simp [← mul_assoc]

theorem family_J_sq (n : ℕ) :
    (familyAction n J).comp (familyAction n J) = ContinuousLinearMap.id ℝ (Family n) := by
  ext x i
  simp [← mul_assoc]

theorem family_K_sq (n : ℕ) :
    (familyAction n K).comp (familyAction n K) = ContinuousLinearMap.id ℝ (Family n) := by
  apply ContinuousLinearMap.ext
  intro x
  funext i
  change K * (K * x i) = x i
  rw [← mul_assoc, K_sq, one_mul]

theorem family_IJ (n : ℕ) :
    (familyAction n I).comp (familyAction n J) = familyAction n K := by
  ext x i
  simp [← mul_assoc]

theorem family_JI (n : ℕ) :
    (familyAction n J).comp (familyAction n I) = -familyAction n K := by
  ext x i
  simp [← mul_assoc]

theorem family_metric_skew {n : ℕ} (a : Mat2) (ha : a.trace = 0) (u v : Family n) :
    familyMetric n (familyAction n a u) v = -familyMetric n u (familyAction n a v) := by
  simp only [familyMetric_apply, familyAction_apply, metric_left_skew a ha,
    Finset.sum_neg_distrib]

theorem family_metric_I {n : ℕ} (u v : Family n) :
    familyMetric n (familyAction n I u) (familyAction n I v) = familyMetric n u v := by
  simp only [familyMetric_apply, familyAction_apply, metric_I]

theorem family_metric_J {n : ℕ} (u v : Family n) :
    familyMetric n (familyAction n J u) (familyAction n J v) = -familyMetric n u v := by
  simp only [familyMetric_apply, familyAction_apply, metric_J, Finset.sum_neg_distrib]

theorem family_metric_K {n : ℕ} (u v : Family n) :
    familyMetric n (familyAction n K u) (familyAction n K v) = -familyMetric n u v := by
  simp only [familyMetric_apply, familyAction_apply, metric_K, Finset.sum_neg_distrib]

theorem family_form_nondegenerate {n : ℕ} (a : Mat2) (ha : a.det ≠ 0)
    (u : Family n) (hu : ∀ v, familyMetric n (familyAction n a u) v = 0) : u = 0 := by
  have h := familyMetric_nondegenerate (familyAction n a u) hu
  funext i
  have hi := congrArg (fun z : Family n => a⁻¹ * z i) h
  simpa [← mul_assoc, Matrix.nonsing_inv_mul a (isUnit_iff_ne_zero.mpr ha)] using hi

theorem family_triad_exact {n : ℕ} (x u v : Family n) :
    extDeriv (potentialOneForm (familyMetric n) (familyAction n I)) x ![u, v] =
      familyMetric n (familyAction n I u) v ∧
    extDeriv (potentialOneForm (familyMetric n) (familyAction n J)) x ![u, v] =
      familyMetric n (familyAction n J u) v ∧
    extDeriv (potentialOneForm (familyMetric n) (familyAction n K)) x ![u, v] =
      familyMetric n (familyAction n K u) v := by
  have h (a : Mat2) (ha : a.trace = 0) :=
    extDeriv_potentialOneForm (familyMetric n) familyMetric_symm (familyAction n a)
      (family_metric_skew a ha) x u v
  exact ⟨h I split_generators_traceless.1,
    h J split_generators_traceless.2.1, h K split_generators_traceless.2.2⟩

end InfoGeometry.Geometry.FlatSplitQuaternion
