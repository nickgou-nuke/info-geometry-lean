import InfoGeometry.Krein.StarHomAdjointTransport
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.Algebra.Star.UnitaryStarAlgAut

noncomputable section

namespace InfoGeometry.Krein.StarHomAdjointTransportTests

open StarHomAdjointTransport
open InfoGeometry.Clifford.Cl11Matrix

theorem flip_star : star J1 = J1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [J1, Matrix.star_apply]

def flipUnitary : unitary Mat2 :=
  ⟨J1, by
    change star J1 * J1 = 1 ∧ J1 * star J1 = 1
    rw [flip_star]
    exact ⟨J1_sq, J1_sq⟩⟩

def flipEquivalence : Mat2 ≃⋆ₐ[ℝ] Mat2 :=
  Unitary.conjStarAlgAut ℝ Mat2 flipUnitary

theorem flip_metric : flipEquivalence Eplus = -Eplus := by
  change J1 * Eplus * star J1 = -Eplus
  rw [flip_star]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

example (operator : Mat2) :
    flipEquivalence (kreinConjugate Eplus (star operator)) =
      kreinConjugate Eplus (star (flipEquivalence operator)) :=
  map_conjugate_star_of_metric_sign (flipEquivalence : Mat2 →⋆ₐ[ℝ] Mat2)
    Eplus Eplus (Or.inr flip_metric) operator

example (operator : {operator : Mat2 // kreinConjugate Eplus (star operator) = operator}) :
    (selfAdjointEquiv flipEquivalence Eplus Eplus (Or.inr flip_metric)).symm
      (selfAdjointEquiv flipEquivalence Eplus Eplus (Or.inr flip_metric) operator) = operator :=
  (selfAdjointEquiv flipEquivalence Eplus Eplus (Or.inr flip_metric)).symm_apply_apply operator

example (metric operator : InfoGeometry.Algebra.FiniteSpin.Mat2C) :
    kreinConjugate (-metric) (star operator) = kreinConjugate metric (star operator) :=
  conjugate_neg_metric metric (star operator)

example {Carrier : Type*} [Ring Carrier] [StarRing Carrier]
    (metric operator : Carrier) (hstar : star metric = metric)
    (hmetric : metric * metric = 1) :
    kreinConjugate metric (star (kreinConjugate metric (star operator))) = operator :=
  conjugate_star_involutive metric hstar hmetric operator

example : ¬IsUnit InfoGeometry.Algebra.FiniteSpin.J_plus := by
  apply square_zero_not_isUnit
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [InfoGeometry.Algebra.FiniteSpin.J_plus, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms map_bounded_kreinAdjoint
#print axioms self_adjoint_transport_iff
#print axioms selfAdjointEquiv
#print axioms flip_metric

end InfoGeometry.Krein.StarHomAdjointTransportTests
