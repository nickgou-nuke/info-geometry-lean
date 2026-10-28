import Mathlib
import InfoGeometry.Core.JordanAssociatorRing

/-!
# Lie--Jordan dual superoperators

These are linear endomorphisms of an arbitrary associative algebra, in particular
of the full matrix algebra. They are not declared to be affine connections.
The mixed commutator is retained in both ordered products. No pair of inputs
is assumed to commute, and no division by two is used.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanDuality

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- The inner derivation, on the actual regular module. -/
def ad (H : A) : Module.End R A :=
  LinearMap.mulLeft R H - LinearMap.mulRight R H

/-- Unnormalized Jordan multiplication, on the actual regular module. -/
def jordan (S : A) : Module.End R A :=
  LinearMap.mulLeft R S + LinearMap.mulRight R S

/-- Positive Jordan perturbation of the inner derivation. -/
def dualPlus (H S : A) : Module.End R A := ad R H + jordan R S

/-- Negative Jordan perturbation of the same inner derivation. -/
def dualMinus (H S : A) : Module.End R A := ad R H - jordan R S

@[simp] theorem ad_apply (H X : A) : ad R H X = H * X - X * H := rfl
@[simp] theorem jordan_apply (S X : A) : jordan R S X = S * X + X * S := rfl
@[simp] theorem dualPlus_apply (H S X : A) :
    dualPlus R H S X = (H * X - X * H) + (S * X + X * S) := rfl
@[simp] theorem dualMinus_apply (H S X : A) :
    dualMinus R H S X = (H * X - X * H) - (S * X + X * S) := rfl

/-- This part really is a derivation. -/
theorem ad_leibniz (H X Y : A) :
    ad R H (X * Y) = ad R H X * Y + X * ad R H Y := by
  simp only [ad_apply]
  noncomm_ring

/-- The Jordan perturbation is generally not a derivation. -/
theorem dualPlus_leibniz_defect (H S X Y : A) :
    dualPlus R H S (X * Y) -
      (dualPlus R H S X * Y + X * dualPlus R H S Y) = -(2 • (X * S * Y)) := by
  simp only [dualPlus_apply, two_nsmul]
  noncomm_ring

theorem dual_sum (H S : A) :
    dualPlus R H S + dualMinus R H S = 2 • ad R H := by
  simp only [dualPlus, dualMinus, two_nsmul]
  abel

theorem dual_difference (H S : A) :
    dualPlus R H S - dualMinus R H S = 2 • jordan R S := by
  simp only [dualPlus, dualMinus, two_nsmul]
  abel

/-- Calibrates the factor two and the sign of the right multiplication. -/
theorem dualPlus_self (H : A) : dualPlus R H H = 2 • LinearMap.mulLeft R H := by
  ext X
  simp only [dualPlus_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, two_nsmul]
  abel

theorem dualMinus_self (H : A) : dualMinus R H H = -(2 • LinearMap.mulRight R H) := by
  ext X
  simp only [dualMinus_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.mulRight_apply, two_nsmul]
  abel

/-- Reuses the repository's associative-envelope Lie identity. -/
theorem ad_bracket (H K : A) :
    ad R H * ad R K - ad R K * ad R H = ad R (H * K - K * H) := by
  ext X
  exact InfoGeometry.Core.JordanAssociator.commutator_operator_commutator H K X

/-- Reuses the existing mixed Lie--Jordan identity, at the endomorphism level. -/
theorem ad_jordan_bracket (H S : A) :
    ad R H * jordan R S - jordan R S * ad R H = jordan R (H * S - S * H) := by
  ext X
  exact InfoGeometry.Core.JordanAssociator.commutator_symm_operator H S X

/-- Two Jordan actions close into an inner derivation, with this order of signs. -/
theorem jordan_bracket (S T : A) :
    jordan R S * jordan R T - jordan R T * jordan R S = ad R (S * T - T * S) := by
  ext X
  exact InfoGeometry.Core.JordanAssociator.symm_operator_commutator S T X

/-- The correction in the minus-after-plus composition has a positive sign. -/
theorem minus_mul_plus (H S : A) :
    dualMinus R H S * dualPlus R H S =
      ad R H * ad R H - jordan R S * jordan R S + jordan R (H * S - S * H) := by
  rw [← ad_jordan_bracket]
  simp only [dualMinus, dualPlus]
  noncomm_ring

/-- Reversing composition changes the mixed term's sign. -/
theorem plus_mul_minus (H S : A) :
    dualPlus R H S * dualMinus R H S =
      ad R H * ad R H - jordan R S * jordan R S - jordan R (H * S - S * H) := by
  rw [← ad_jordan_bracket]
  simp only [dualMinus, dualPlus]
  noncomm_ring

/-- The symmetric product removes cross terms without any commuting hypothesis. -/
theorem dual_symmetric_product (H S : A) :
    dualMinus R H S * dualPlus R H S + dualPlus R H S * dualMinus R H S =
      2 • (ad R H * ad R H - jordan R S * jordan R S) := by
  rw [minus_mul_plus, plus_mul_minus]
  simp only [two_nsmul]
  abel

/-- Exact obstruction to commuting primal and dual superoperators. -/
theorem dual_bracket (H S : A) :
    dualPlus R H S * dualMinus R H S - dualMinus R H S * dualPlus R H S =
      -(2 • jordan R (H * S - S * H)) := by
  rw [minus_mul_plus, plus_mul_minus]
  simp only [two_nsmul]
  abel

/-- Two-direction coefficient curvature, not a manifold curvature assertion. -/
theorem plus_directional_bracket (H K S T : A) :
    dualPlus R H S * dualPlus R K T - dualPlus R K T * dualPlus R H S =
      ad R ((H * K - K * H) + (S * T - T * S)) +
        jordan R ((H * T - T * H) + (S * K - K * S)) := by
  ext X
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    dualPlus_apply, ad_apply, jordan_apply]
  noncomm_ring

/-- Covariance under an actual algebra homomorphism; the products keep their order. -/
theorem map_dualPlus {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (H S X : A) :
    f (dualPlus R H S X) = dualPlus R (f H) (f S) (f X) := by
  simp only [dualPlus_apply, map_add, map_sub, map_mul]

theorem map_dualMinus {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (H S X : A) :
    f (dualMinus R H S X) = dualMinus R (f H) (f S) (f X) := by
  simp only [dualMinus_apply, map_add, map_sub, map_mul]

end InfoGeometry.OperatorAlgebra.LieJordanDuality
