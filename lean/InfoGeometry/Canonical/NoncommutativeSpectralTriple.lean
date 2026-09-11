import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.NCG

/-!
=============================================================================
SECTION 1: Non-Commutative Differential Calculus over a Dirac Operator
=============================================================================
-/

variable {A : Type*} [Ring A]

/-- The non-commutative Dirac differential: d_D(a) = D * a - a * D = [D, a] -/
def ncDiff (D a : A) : A :=
  D * a - a * D

@[simp]
theorem ncDiff_apply (D a : A) : ncDiff D a = D * a - a * D := rfl

/-- Linearity / Additivity of the non-commutative differential -/
theorem ncDiff_add (D a b : A) : ncDiff D (a + b) = ncDiff D a + ncDiff D b := by
  dsimp [ncDiff]
  simp only [mul_add, add_mul]
  abel

@[simp]
theorem ncDiff_zero (D : A) : ncDiff D 0 = 0 := by
  dsimp [ncDiff]
  simp

theorem ncDiff_neg (D a : A) : ncDiff D (-a) = -ncDiff D a := by
  dsimp [ncDiff]
  simp only [mul_neg, neg_mul]
  abel

theorem ncDiff_sub (D a b : A) : ncDiff D (a - b) = ncDiff D a - ncDiff D b := by
  rw [sub_eq_add_neg, ncDiff_add, ncDiff_neg]
  rw [sub_eq_add_neg]

/-- 🏆 THEOREM 1: The Non-Commutative Leibniz Rule (NC Product Rule):
    d_D(a * b) = (d_D a) * b + a * (d_D b) -/
theorem ncDiff_mul (D a b : A) :
    ncDiff D (a * b) = ncDiff D a * b + a * ncDiff D b := by
  dsimp [ncDiff]
  calc
    D * (a * b) - (a * b) * D
      = (D * a * b - a * D * b) + (a * D * b - a * b * D) := by
        simp only [mul_assoc]
        abel
    _ = (D * a - a * D) * b + a * (D * b - b * D) := by
        simp only [sub_mul, mul_sub, mul_assoc]

/-- Annihilation of the Identity: d_D(1) = 0 -/
@[simp]
theorem ncDiff_one (D : A) : ncDiff D 1 = 0 := by
  dsimp [ncDiff]
  simp only [mul_one, one_mul, sub_self]

/-- The commutator of two inner noncommutative differentials is inner again.
    This is the pointwise Jacobi identity for the associative commutator. -/
theorem ncDiff_commutator (D E a : A) :
    ncDiff D (ncDiff E a) - ncDiff E (ncDiff D a) =
      ncDiff (ncDiff D E) a := by
  dsimp [ncDiff]
  simp only [mul_assoc, mul_sub, sub_mul]
  abel

/-- Anticommutation with Star Involution when D is self-adjoint: (d_D a)* = - d_D(a*) -/
theorem ncDiff_star [StarRing A] (D a : A) (hD : star D = D) :
    star (ncDiff D a) = - ncDiff D (star a) := by
  dsimp [ncDiff]
  rw [star_sub, star_mul, star_mul, hD]
  abel

/-!
=============================================================================
SECTION 2: Gauge Fluctuations of the Dirac Operator (Inner Fluctuations)
=============================================================================
-/

/-- The fluctuating Dirac operator: D_A = D + A -/
def fluctuatedDirac (D A_gauge : A) : A :=
  D + A_gauge

/-- Fluctuating the Dirac operator adds the inner commutator with the gauge
    potential to the original noncommutative differential. -/
theorem ncDiff_fluctuatedDirac (D A_gauge a : A) :
    ncDiff (fluctuatedDirac D A_gauge) a =
      ncDiff D a + (A_gauge * a - a * A_gauge) := by
  dsimp [fluctuatedDirac, ncDiff]
  simp only [add_mul, mul_add]
  abel

/-- The Unitary Gauge Transformation of a gauge field A:
    A^u = u * A * u_inv + u * d_D(u_inv) -/
def gaugeTransform (D A_gauge u u_inv : A) : A :=
  u * A_gauge * u_inv + u * ncDiff D u_inv

/-- Gauge transformation with the inverse supplied by the native unit group. -/
def gaugeTransformUnit (D A_gauge : A) (u : Aˣ) : A :=
  gaugeTransform D A_gauge (u : A) (↑(u⁻¹) : A)

/-- 🏆 THEOREM 2: Exact Gauge Covariance of the Fluctuated Dirac Operator:
    u * (D + A) * u_inv = D + A^u
    whenever u * u_inv = 1 and u_inv * u = 1. -/
theorem fluctuatedDirac_gauge_covariance
    (D A_gauge u u_inv : A)
    (h_right_inv : u * u_inv = 1) :
    u * fluctuatedDirac D A_gauge * u_inv =
      fluctuatedDirac D (gaugeTransform D A_gauge u u_inv) := by
  dsimp [fluctuatedDirac, gaugeTransform, ncDiff]
  calc
    u * (D + A_gauge) * u_inv
      = u * D * u_inv + u * A_gauge * u_inv := by
        simp only [mul_add, add_mul, mul_assoc]
    _ = D + (u * A_gauge * u_inv + (u * D * u_inv - D)) := by
        abel
    _ = D + (u * A_gauge * u_inv + (u * (D * u_inv) - (u * u_inv) * D)) := by
        rw [h_right_inv, one_mul]
        simp only [mul_assoc]
    _ = D + (u * A_gauge * u_inv + u * (D * u_inv - u_inv * D)) := by
        simp only [mul_sub, mul_assoc]

theorem fluctuatedDirac_gauge_covariance_unit
    (D A_gauge : A) (u : Aˣ) :
    (u : A) * fluctuatedDirac D A_gauge * (↑(u⁻¹) : A) =
      fluctuatedDirac D (gaugeTransformUnit D A_gauge u) := by
  exact fluctuatedDirac_gauge_covariance D A_gauge (u : A) (↑(u⁻¹) : A) u.val_inv

/-- 🏆 THEOREM 3: Gauge Transformation Transitivity (Group Action):
    (A^u)^v = A^(v * u) -/
theorem gaugeTransform_transitive
    (D A_gauge u u_inv v v_inv : A)
    (hu_right : u * u_inv = 1)
    (hv_right : v * v_inv = 1)
    (hv_left : v_inv * v = 1) :
    gaugeTransform D (gaugeTransform D A_gauge u u_inv) v v_inv =
      gaugeTransform D A_gauge (v * u) (u_inv * v_inv) := by
  have h1 : v * (u * fluctuatedDirac D A_gauge * u_inv) * v_inv =
      (v * u) * fluctuatedDirac D A_gauge * (u_inv * v_inv) := by
    simp only [mul_assoc]
  have h2 : v * fluctuatedDirac D (gaugeTransform D A_gauge u u_inv) * v_inv =
      fluctuatedDirac D (gaugeTransform D (gaugeTransform D A_gauge u u_inv) v v_inv) := by
    exact fluctuatedDirac_gauge_covariance D (gaugeTransform D A_gauge u u_inv) v v_inv hv_right
  have h_prod_right : (v * u) * (u_inv * v_inv) = 1 := by
    calc
      (v * u) * (u_inv * v_inv) = v * (u * u_inv) * v_inv := by simp only [mul_assoc]
      _ = v * 1 * v_inv := by rw [hu_right]
      _ = v * v_inv := by rw [mul_one]
      _ = 1 := hv_right
  have h3 : (v * u) * fluctuatedDirac D A_gauge * (u_inv * v_inv) =
      fluctuatedDirac D (gaugeTransform D A_gauge (v * u) (u_inv * v_inv)) := by
    exact fluctuatedDirac_gauge_covariance D A_gauge (v * u) (u_inv * v_inv) h_prod_right
  have h_cov_u := fluctuatedDirac_gauge_covariance D A_gauge u u_inv hu_right
  rw [← h_cov_u] at h2
  rw [h1] at h2
  rw [h3] at h2
  dsimp [fluctuatedDirac] at h2
  exact add_left_cancel h2.symm

/-- The identity unit acts trivially on gauge potentials. -/
@[simp]
theorem gaugeTransform_one (D A_gauge : A) :
    gaugeTransform D A_gauge 1 1 = A_gauge := by
  dsimp [gaugeTransform]
  simp

/-- A two-sided unitary gauge element has the expected inverse action. -/
theorem gaugeTransform_inverse
    (D A_gauge u u_inv : A)
    (h_right : u * u_inv = 1)
    (h_left : u_inv * u = 1) :
    gaugeTransform D (gaugeTransform D A_gauge u u_inv) u_inv u = A_gauge := by
  have h := gaugeTransform_transitive D A_gauge u u_inv u_inv u
      h_right h_left h_right
  simpa [h_left, h_right] using h

theorem gaugeTransformUnit_inverse (D A_gauge : A) (u : Aˣ) :
    gaugeTransformUnit D (gaugeTransformUnit D A_gauge u) (u⁻¹) = A_gauge := by
  unfold gaugeTransformUnit
  exact gaugeTransform_inverse D A_gauge (u : A) (↑(u⁻¹) : A)
    u.val_inv u.inv_val

@[simp]
theorem gaugeTransformUnit_one (D A_gauge : A) :
    gaugeTransformUnit D A_gauge 1 = A_gauge := by
  unfold gaugeTransformUnit
  simp [gaugeTransform_one]

theorem gaugeTransformUnit_transitive (D A_gauge : A) (u v : Aˣ) :
    gaugeTransformUnit D (gaugeTransformUnit D A_gauge u) v =
      gaugeTransformUnit D A_gauge (v * u) := by
  unfold gaugeTransformUnit
  simpa [Units.val_mul] using
    (gaugeTransform_transitive D A_gauge (u : A) (↑(u⁻¹) : A)
      (v : A) (↑(v⁻¹) : A) u.val_inv v.val_inv v.inv_val)

/-!
=============================================================================
SECTION 3: The Non-Commutative Differential 1-Form & Self-Adjoint Gauge Potential
=============================================================================
-/

/-- A single-generator 1-form: a * [D, b] -/
def oneFormTerm (D a b : A) : A :=
  a * ncDiff D b

/-- Self-adjointness condition for the fluctuating 1-form -/
def IsSelfAdjointOneForm [StarRing A] (A_gauge : A) : Prop :=
  star A_gauge = A_gauge

/-- 🏆 THEOREM 4: If D is self-adjoint, the fluctuated Dirac operator is self-adjoint:
    (D + A)* = D + A -/
theorem fluctuatedDirac_self_adjoint [StarRing A]
    (D A_gauge : A)
    (hD : star D = D)
    (hA : IsSelfAdjointOneForm A_gauge) :
    star (fluctuatedDirac D A_gauge) = fluctuatedDirac D A_gauge := by
  dsimp [fluctuatedDirac, IsSelfAdjointOneForm] at *
  rw [star_add, hD, hA]

end InfoGeometry.Canonical.NCG

end noncomputable section
