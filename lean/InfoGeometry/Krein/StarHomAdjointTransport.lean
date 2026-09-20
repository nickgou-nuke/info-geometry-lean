import InfoGeometry.Krein.TwoSheetKreinIdealBridge
import InfoGeometry.Krein.KreinSpace
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.RingTheory.Nilpotent.Basic

namespace InfoGeometry.Krein.StarHomAdjointTransport

section Algebraic

variable {Carrier : Type*} [Ring Carrier] [StarRing Carrier]

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
    (equivalence : Source →⋆ₐ[Scalar] Target) sourceMetric targetMetric hmetric operator
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
