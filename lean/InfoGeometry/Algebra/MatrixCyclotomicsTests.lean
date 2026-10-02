import InfoGeometry.Algebra.MatrixCyclotomics
import InfoGeometry.Algebra.IwasawaCyclotomics

namespace InfoGeometry.Algebra.MatrixCyclotomics

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain

example : Polynomial.cyclotomic 4 ℤ = (Polynomial.X : Polynomial ℤ) ^ 2 + 1 :=
  cyclotomic_four ℤ

example : Polynomial.aeval (shearRoot 2) (Polynomial.cyclotomic 4 ℝ) = 0 :=
  shearRoot_cyclotomic_four 2

example : ¬ Commute (shearRoot 0) (shearRoot 1) := by
  rw [shearRoot_commute_iff]
  norm_num

example : Set.Infinite (Set.range shearRoot) := infinite_shearRoot_range

example : (NPart 3 - 1) ^ 2 = 0 := shear_unipotent 3

example : NPart 0 = (1 : Mat2) := (NPart_eq_one_iff 0).mpr rfl

example : NPart 3 ≠ 1 := by
  rw [NPart_eq_one_iff]
  norm_num

example (changeOfBasis : Mat2ˣ) :
    Polynomial.aeval
      ((changeOfBasis : Mat2) * Eminus * ((changeOfBasis⁻¹ : Mat2ˣ) : Mat2))
      (Polynomial.cyclotomic 4 ℝ) = 0 :=
  cyclotomic_four_conjugation changeOfBasis Eminus Eminus_cyclotomic_four

example : (1 : Mat2) ^ 4 = 1 ∧
    Polynomial.aeval (1 : Mat2) (Polynomial.cyclotomic 4 ℝ) ≠ 0 := by
  refine ⟨one_pow 4, ?_⟩
  intro hzero
  rw [aeval_cyclotomic_four] at hzero
  have hentry := congrArg (fun matrix : Mat2 => matrix 0 0) hzero
  norm_num at hentry

#print axioms Eminus_cyclotomic_four
#print axioms polynomial_root_transport
#print axioms shearRoot_commute_iff
#print axioms infinite_shearRoot_range
#print axioms cyclotomic_four_conjugation
#print axioms shear_unipotent

example : IwasawaCyclotomics.traceDiscriminant (NPart 0) = 0 ∧ NPart 0 = 1 :=
  ⟨IwasawaCyclotomics.NPart_discriminant 0, (NPart_eq_one_iff 0).mpr rfl⟩

example : 0 < IwasawaCyclotomics.traceDiscriminant (APart 1) := by
  exact (IwasawaCyclotomics.APart_discriminant_pos_iff 1).mpr (by norm_num)

example : IwasawaCyclotomics.traceDiscriminant (APart 0) = 0 := by
  rw [IwasawaCyclotomics.APart_discriminant]
  simp

#print axioms IwasawaCyclotomics.KPart_discriminant_neg_iff
#print axioms IwasawaCyclotomics.APart_discriminant_pos_iff

end InfoGeometry.Algebra.MatrixCyclotomics
