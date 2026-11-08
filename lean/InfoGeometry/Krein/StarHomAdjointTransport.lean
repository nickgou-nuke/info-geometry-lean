/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.TwoSheetKreinIdealBridge
import InfoGeometry.Krein.KreinSpace
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.RingTheory.Nilpotent.Basic

namespace InfoGeometry.Krein.StarHomAdjointTransport

section Algebraic

variable {Carrier : Type*} [Ring Carrier] [StarRing Carrier]

/-- A square-minus-one isometry is skew-adjoint. This is an algebraic
quaternionic structure, not an assertion of complex anti-linearity. -/
theorem star_eq_neg_of_isometry_square_neg_one {T : Carrier}
    (hiso : star T * T = 1) (hsq : T * T = -1) : star T = -T := by
  have h := congrArg (fun a : Carrier => a * T) hiso
  rw [mul_assoc, hsq, mul_neg, mul_one, one_mul] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Skew-adjointness cancels the symmetrized pairing. Individual terms
need not vanish in an arbitrary star ring. -/
theorem skew_pairing_sum_zero {T : Carrier} (hT : star T = -T) (X : Carrier) :
    star X * (T * X) + star (T * X) * X = 0 := by
  rw [star_mul, hT]
  simp [mul_assoc]

/-- Anticommuting isometries reverse the metric. No square-minus-one or
self-adjointness hypothesis is needed for this algebraic transport law. -/
theorem metric_transport_eq_neg {T J : Carrier} (hiso : star T * T = 1)
    (hanti : J * T = -(T * J)) : star T * J * T = -J := by
  rw [mul_assoc, hanti, mul_neg, ← mul_assoc, hiso, one_mul]

/-- The whole metric pairing reverses sign, including mixed arguments.
For self-adjoint `J`, setting `Y = X` gives the Krein quadratic-form law;
strict opposite signs additionally require a nonzero ordered scalar readout. -/
theorem metric_pairing_transport_eq_neg {T J : Carrier}
    (hiso : star T * T = 1) (hanti : J * T = -(T * J)) (X Y : Carrier) :
    star (T * X) * J * (T * Y) = -(star X * J * Y) := by
  rw [star_mul]
  calc
    star X * star T * J * (T * Y) = star X * (star T * J * T) * Y := by
      simp only [mul_assoc]
    _ = -(star X * J * Y) := by
      rw [metric_transport_eq_neg hiso hanti, mul_neg, neg_mul]

theorem conjugate_star_mul (metric : Carrier) (hmetric : metric * metric = 1)
    (first second : Carrier) :
    kreinConjugate metric (star (first * second)) =
      kreinConjugate metric (star second) * kreinConjugate metric (star first) := by
  rw [star_mul, kreinConjugate_mul metric hmetric]

theorem conjugate_star_involutive (metric : Carrier)
    (hstar : star metric = metric) (hmetric : metric * metric = 1)
    (operator : Carrier) :
    kreinConjugate metric (star (kreinConjugate metric (star operator))) = operator := by
  have hintertwine : star (kreinConjugate metric (star operator)) =
      kreinConjugate metric operator := by
    simp [kreinConjugate, star_mul, hstar, mul_assoc]
  rw [hintertwine, kreinConjugate_involutive metric hmetric]

theorem conjugate_neg_metric (metric operator : Carrier) :
    kreinConjugate (-metric) operator = kreinConjugate metric operator := by
  simp [kreinConjugate]

end Algebraic

theorem square_zero_not_isUnit {Carrier : Type*} [Ring Carrier] [Nontrivial Carrier]
    (operator : Carrier) (hoperator : operator ^ 2 = 0) : ¬IsUnit operator := by
  exact IsNilpotent.not_isUnit (show IsNilpotent operator from ⟨2, hoperator⟩)

section Transport

variable {Scalar Source Target : Type*} [CommSemiring Scalar]
variable [Ring Source] [StarRing Source] [Algebra Scalar Source]
variable [Ring Target] [StarRing Target] [Algebra Scalar Target]

theorem map_conjugate_star (representation : Source →⋆ₐ[Scalar] Target)
    (metric operator : Source) :
    representation (kreinConjugate metric (star operator)) =
      kreinConjugate (representation metric) (star (representation operator)) := by
  simp only [kreinConjugate, map_mul, map_star]

theorem map_conjugate_star_of_metric_sign
    (representation : Source →⋆ₐ[Scalar] Target)
    (sourceMetric : Source) (targetMetric : Target)
    (hmetric : representation sourceMetric = targetMetric ∨
      representation sourceMetric = -targetMetric) (operator : Source) :
    representation (kreinConjugate sourceMetric (star operator)) =
      kreinConjugate targetMetric (star (representation operator)) := by
  rw [map_conjugate_star]
  rcases hmetric with hpositive | hnegative
  · rw [hpositive]
  · rw [hnegative, conjugate_neg_metric]

theorem self_adjoint_transport_iff (equivalence : Source ≃⋆ₐ[Scalar] Target)
    (sourceMetric : Source) (targetMetric : Target)
    (hmetric : equivalence sourceMetric = targetMetric ∨
      equivalence sourceMetric = -targetMetric) (operator : Source) :
    kreinConjugate targetMetric (star (equivalence operator)) = equivalence operator ↔
      kreinConjugate sourceMetric (star operator) = operator := by
  have hmap := map_conjugate_star_of_metric_sign
    equivalence.toStarAlgHom sourceMetric targetMetric hmetric operator
  change kreinConjugate targetMetric (star (equivalence.toStarAlgHom operator)) =
      equivalence.toStarAlgHom operator ↔
    kreinConjugate sourceMetric (star operator) = operator
  rw [← hmap]
  exact equivalence.injective.eq_iff

def selfAdjointEquiv (equivalence : Source ≃⋆ₐ[Scalar] Target)
    (sourceMetric : Source) (targetMetric : Target)
    (hmetric : equivalence sourceMetric = targetMetric ∨
      equivalence sourceMetric = -targetMetric) :
    {operator : Source // kreinConjugate sourceMetric (star operator) = operator} ≃
      {operator : Target // kreinConjugate targetMetric (star operator) = operator} :=
  equivalence.toEquiv.subtypeEquiv fun operator =>
    (self_adjoint_transport_iff equivalence sourceMetric targetMetric hmetric operator).symm

@[simp] theorem selfAdjointEquiv_apply (equivalence : Source ≃⋆ₐ[Scalar] Target)
    (sourceMetric : Source) (targetMetric : Target)
    (hmetric : equivalence sourceMetric = targetMetric ∨
      equivalence sourceMetric = -targetMetric)
    (operator : {operator : Source //
      kreinConjugate sourceMetric (star operator) = operator}) :
    (selfAdjointEquiv equivalence sourceMetric targetMetric hmetric operator : Target) =
      equivalence operator := rfl

end Transport

section BoundedOperators

variable {SourceHilbert TargetHilbert : Type*}
variable [NormedAddCommGroup SourceHilbert] [InnerProductSpace ℝ SourceHilbert]
variable [CompleteSpace SourceHilbert] [KreinSpace SourceHilbert]
variable [NormedAddCommGroup TargetHilbert] [InnerProductSpace ℝ TargetHilbert]
variable [CompleteSpace TargetHilbert] [KreinSpace TargetHilbert]

theorem bounded_adjoint_eq_conjugate_star (operator : SourceHilbert →L[ℝ] SourceHilbert) :
    KreinSpace.kreinAdjoint operator =
      kreinConjugate (KreinSpace.jCLM (H := SourceHilbert)) (star operator) := by
  ext vector
  rfl

theorem map_bounded_kreinAdjoint
    (representation : (SourceHilbert →L[ℝ] SourceHilbert) →⋆ₐ[ℝ]
      (TargetHilbert →L[ℝ] TargetHilbert))
    (hmetric : representation (KreinSpace.jCLM (H := SourceHilbert)) =
        KreinSpace.jCLM (H := TargetHilbert) ∨
      representation (KreinSpace.jCLM (H := SourceHilbert)) =
        -KreinSpace.jCLM (H := TargetHilbert))
    (operator : SourceHilbert →L[ℝ] SourceHilbert) :
    representation (KreinSpace.kreinAdjoint operator) =
      KreinSpace.kreinAdjoint (representation operator) := by
  rw [bounded_adjoint_eq_conjugate_star, bounded_adjoint_eq_conjugate_star]
  exact map_conjugate_star_of_metric_sign representation _ _ hmetric operator

theorem map_bounded_krein_selfAdjoint
    (representation : (SourceHilbert →L[ℝ] SourceHilbert) →⋆ₐ[ℝ]
      (TargetHilbert →L[ℝ] TargetHilbert))
    (hmetric : representation (KreinSpace.jCLM (H := SourceHilbert)) =
        KreinSpace.jCLM (H := TargetHilbert) ∨
      representation (KreinSpace.jCLM (H := SourceHilbert)) =
        -KreinSpace.jCLM (H := TargetHilbert))
    (operator : SourceHilbert →L[ℝ] SourceHilbert)
    (hoperator : KreinSpace.IsKreinSelfAdjoint operator) :
    KreinSpace.IsKreinSelfAdjoint (representation operator) := by
  change KreinSpace.kreinAdjoint (representation operator) = representation operator
  rw [← map_bounded_kreinAdjoint representation hmetric operator]
  exact congrArg representation hoperator

end BoundedOperators

end InfoGeometry.Krein.StarHomAdjointTransport
