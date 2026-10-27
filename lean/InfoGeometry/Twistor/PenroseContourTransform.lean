import InfoGeometry.Twistor.HomogeneousTwistorCech
import InfoGeometry.Twistor.PerjesConventions
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Actual contour moments, Cech descent and a nonconstant Maxwell field

Mathlib circle integrals on finite Laurent sections equal the principal-part
coordinates and descend to the computed quotient. An explicit degree -4
rational twistor representative gives a nonconstant Maxwell spinor satisfying
the differential field equation with actual complex derivatives. This is not
the full analytic Penrose isomorphism or the positive-frequency theorem.
-/

noncomputable section
namespace InfoGeometry.Twistor.PenroseContourTransform

open scoped BigOperators
open Complex Matrix
open PenroseIncidence HomogeneousTwistorCech

def contourNormalization : ℂ := 2 * Real.pi * Complex.I

theorem contourNormalization_ne_zero : contourNormalization ≠ 0 := by
  simp [contourNormalization, Real.pi_ne_zero]

theorem zpow_circleIntegrable (k : ℤ) :
    CircleIntegrable (fun z : ℂ => z ^ k) 0 1 := by
  simpa using (circleIntegrable_sub_zpow_iff (c := 0) (w := 0) (R := 1) (n := k)).2
    (Or.inr (Or.inr (by simp)))

theorem zpow_circleIntegral (k : ℤ) :
    (∮ z in C(0, 1), z ^ k) = if k = -1 then contourNormalization else 0 := by
  by_cases hk : k = -1
  · subst k
    simpa [contourNormalization] using
      circleIntegral.integral_sub_center_inv (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)
  · simpa [hk] using circleIntegral.integral_sub_zpow_of_ne hk (0 : ℂ) 0 1

theorem monomial_circleIntegrable (a : ℂ) (k : ℤ) :
    CircleIntegrable (fun z : ℂ => a * z ^ k) 0 1 := by
  simpa [smul_eq_mul] using (zpow_circleIntegrable k).const_smul a

def normalizedMoment (r : ℕ) (p : Laurent) : ℂ :=
  contourNormalization⁻¹ * ∮ z in C(0, 1), z ^ (r : ℤ) * evaluate z p

/-- Exact residue calculation on every finite Laurent section. -/
theorem normalizedMoment_eq_coefficient (r : ℕ) (p : Laurent) :
    normalizedMoment r p = p.coeff (-(r : ℤ) - 1) := by
  have hi : (∮ z in C(0, 1), z ^ (r : ℤ) * evaluate z p) =
      ∮ z in C(0, 1), ∑ k ∈ p.coeff.support, p.coeff k * z ^ (k + (r : ℤ)) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hn : z ≠ 0 := by
      intro h
      simp [h] at hz
    simp [evaluate, coefficients, LinearMap.comp_apply, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.mul_sum, zpow_add₀ hn, mul_comm, mul_left_comm, mul_assoc]
  rw [normalizedMoment, hi, circleIntegral.integral_fun_sum
    (fun k _ => monomial_circleIntegrable (p.coeff k) (k + (r : ℤ)))]
  simp only [circleIntegral.integral_const_mul, zpow_circleIntegral]
  have hc (k : ℤ) : (k + (r : ℤ) = -1) ↔ k = -(r : ℤ) - 1 := by omega
  simp only [hc, mul_ite, mul_zero]
  by_cases hm : -(r : ℤ) - 1 ∈ p.coeff.support
  · simp [hm, contourNormalization_ne_zero, mul_comm, mul_left_comm]
  · have hz : p.coeff (-(r : ℤ) - 1) = 0 := Finsupp.notMem_support_iff.mp hm
    simp [hm, hz]

theorem contour_eq_principalPart (n : ℕ) (p : Laurent) (i : Fin (n + 1)) :
    normalizedMoment i.val p = principalPart n p i := by
  rw [normalizedMoment_eq_coefficient]
  rfl

theorem contour_coboundary_invariant (n : ℕ) (p q : Laurent)
    (hpq : p - q ∈ boundaries n) (i : Fin (n + 1)) :
    normalizedMoment i.val p = normalizedMoment i.val q := by
  rw [contour_eq_principalPart n p i, contour_eq_principalPart n q i]
  rw [boundaries_eq_kernel] at hpq
  have h := congrFun hpq i
  exact sub_eq_zero.mp (by simpa only [map_sub, Pi.sub_apply, Pi.zero_apply] using h)

/-- Genuine quotient descent, using the computed kernel. -/
def contourOnCohomology (n : ℕ) : CechH1 n →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  (boundaries n).liftQ (principalPart n) (le_of_eq (boundaries_eq_kernel n))

theorem contourOnCohomology_mk (n : ℕ) (p : Laurent) (i : Fin (n + 1)) :
    contourOnCohomology n ((boundaries n).mkQ p) i = normalizedMoment i.val p := by
  rw [contour_eq_principalPart n p i]
  rfl

theorem nonzero_residue : normalizedMoment 0 (AddMonoidAlgebra.single (-1) (1 : ℂ)) = 1 := by
  simp [normalizedMoment_eq_coefficient]

/-- A degree -4 rational representative with poles on both spinor chart axes. -/
def maxwellRepresentative (Z : Twistor4) : ℂ :=
  (Z.1 0) ^ 2 / ((Z.2 0) ^ 3 * (Z.2 1) ^ 3)

theorem maxwellRepresentative_homogeneous :
    IsHomogeneous (weight 2) maxwellRepresentative := by
  intro c hc Z
  change (c * Z.1 0) ^ 2 / ((c * Z.2 0) ^ 3 * (c * Z.2 1) ^ 3) =
    c ^ (-4 : ℤ) * (Z.1 0 ^ 2 / (Z.2 0 ^ 3 * Z.2 1 ^ 3))
  rw [mul_pow, mul_pow, mul_pow]
  have hden : (c ^ 3 * Z.2 0 ^ 3) * (c ^ 3 * Z.2 1 ^ 3) =
      c ^ 6 * (Z.2 0 ^ 3 * Z.2 1 ^ 3) := by ring
  rw [hden, mul_div_mul_comm]
  congr 1
  simp only [zpow_neg, zpow_ofNat]
  field_simp [hc]
  ring

def maxwellKernel (X : ComplexSpacetime) : Laurent :=
  AddMonoidAlgebra.single (-3) ((-1 : ℂ) * (X 0 0 * X 0 0)) +
  AddMonoidAlgebra.single (-2) ((-2 : ℂ) * (X 0 0 * X 0 1)) +
  AddMonoidAlgebra.single (-1) ((-1 : ℂ) * (X 0 1 * X 0 1))

/-- The Laurent kernel is obtained by the actual incidence substitution. -/
theorem maxwellKernel_incidence (X : ComplexSpacetime) (z : ℂ) (hz : z ≠ 0) :
    evaluate z (maxwellKernel X) =
      maxwellRepresentative (PerjesConventions.perjesIncidence X (firstChart z)) := by
  simp [maxwellKernel, evaluate_single, maxwellRepresentative,
    PerjesConventions.perjesIncidence, firstChart, omegaLinearMap,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  field_simp [hz] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def maxwellField (X : ComplexSpacetime) : ComplexSpacetime :=
  !![(-1) * (X 0 1 * X 0 1), (-2) * (X 0 0 * X 0 1);
     (-2) * (X 0 0 * X 0 1), (-1) * (X 0 0 * X 0 0)]

/-- Two lower-spinor factors give the monomial weight i+j. -/
def contourMaxwell (X : ComplexSpacetime) : ComplexSpacetime :=
  fun i j => normalizedMoment (i.val + j.val) (maxwellKernel X)

theorem contourMaxwell_eq_field (X : ComplexSpacetime) :
    contourMaxwell X = maxwellField X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contourMaxwell, normalizedMoment_eq_coefficient, maxwellKernel, maxwellField]

theorem maxwellField_symmetric (X : ComplexSpacetime) :
    (maxwellField X)ᵀ = maxwellField X := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Actual complex derivative along a spacetime matrix unit. -/
def spacetimePartial (A B : Fin 2) (f : ComplexSpacetime → ℂ) (X : ComplexSpacetime) : ℂ :=
  deriv (fun t : ℂ => f (X + t • Matrix.stdBasisMatrix A B 1)) 0

private theorem deriv_affine_product (c u v a b : ℂ) :
    deriv (fun t : ℂ => c * ((u + t * a) * (v + t * b))) 0 =
      c * (a * v + u * b) := by
  have hU : HasDerivAt (fun t : ℂ => u + t * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const a).const_add u
  have hV : HasDerivAt (fun t : ℂ => v + t * b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const b).const_add v
  simpa using ((hU.mul hV).const_mul c).deriv

/-- Source-free spin-one equation for the actual nonconstant contour field. -/
theorem maxwell_zero_rest_mass (X : ComplexSpacetime) (A C : Fin 2) :
    spacetimePartial A 0 (fun Y => maxwellField Y 1 C) X -
      spacetimePartial A 1 (fun Y => maxwellField Y 0 C) X = 0 := by
  fin_cases A <;> fin_cases C
  · change deriv (fun t : ℂ => (-2) * ((X 0 0 + t * 1) * (X 0 1 + t * 0))) 0 -
      deriv (fun t : ℂ => (-1) * ((X 0 1 + t * 1) * (X 0 1 + t * 1))) 0 = 0
    rw [deriv_affine_product, deriv_affine_product]
    ring
  · change deriv (fun t : ℂ => (-1) * ((X 0 0 + t * 1) * (X 0 0 + t * 1))) 0 -
      deriv (fun t : ℂ => (-2) * ((X 0 0 + t * 0) * (X 0 1 + t * 1))) 0 = 0
    rw [deriv_affine_product, deriv_affine_product]
    ring
  · change deriv (fun t : ℂ => (-2) * ((X 0 0 + t * 0) * (X 0 1 + t * 0))) 0 -
      deriv (fun t : ℂ => (-1) * ((X 0 1 + t * 0) * (X 0 1 + t * 0))) 0 = 0
    rw [deriv_affine_product, deriv_affine_product]
    ring
  · change deriv (fun t : ℂ => (-1) * ((X 0 0 + t * 0) * (X 0 0 + t * 0))) 0 -
      deriv (fun t : ℂ => (-2) * ((X 0 0 + t * 0) * (X 0 1 + t * 0))) 0 = 0
    rw [deriv_affine_product, deriv_affine_product]
    ring

theorem contourMaxwell_zero_rest_mass (X : ComplexSpacetime) (A C : Fin 2) :
    spacetimePartial A 0 (fun Y => contourMaxwell Y 1 C) X -
      spacetimePartial A 1 (fun Y => contourMaxwell Y 0 C) X = 0 := by
  simp only [contourMaxwell_eq_field]
  exact maxwell_zero_rest_mass X A C

theorem contourMaxwell_nonconstant :
    contourMaxwell (0 : ComplexSpacetime) ≠ contourMaxwell (1 : ComplexSpacetime) := by
  intro h
  have hh := congrArg (fun M : ComplexSpacetime => M 1 1) h
  norm_num [contourMaxwell_eq_field, maxwellField] at hh

end InfoGeometry.Twistor.PenroseContourTransform
