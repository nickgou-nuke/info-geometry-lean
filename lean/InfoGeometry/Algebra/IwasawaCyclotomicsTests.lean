import InfoGeometry.Algebra.IwasawaCyclotomics

namespace InfoGeometry.Algebra.IwasawaCyclotomics

open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open InfoGeometry.Algebra.MatrixCyclotomics

example : traceDiscriminant (KPart 0) = 0 := by
  rw [KPart_discriminant]
  norm_num

example : traceDiscriminant (KPart (Real.pi / 2)) = -4 := by
  rw [KPart_discriminant]
  norm_num

example : traceDiscriminant (NPart 0) = 0 ∧ NPart 0 = 1 :=
  ⟨NPart_discriminant 0, (NPart_eq_one_iff 0).mpr rfl⟩

example : (NPart 3 - 1) ^ 2 = 0 ∧ NPart 3 ≠ 1 :=
  ⟨shear_unipotent 3, by rw [NPart_eq_one_iff]; norm_num⟩

example : traceDiscriminant (APart 0) = 0 := by
  rw [APart_discriminant]
  norm_num

example : 0 < traceDiscriminant (APart 1) :=
  (APart_discriminant_pos_iff 1).mpr (by norm_num)

example : 0 < traceDiscriminant (APart (-1)) :=
  (APart_discriminant_pos_iff (-1)).mpr (by norm_num)

example : traceDiscriminant (shearRoot 2) = -4 :=
  shearRoot_discriminant 2

#print axioms shearRoot_discriminant
#print axioms KPart_discriminant_neg_iff
#print axioms shear_unipotent
#print axioms APart_discriminant_pos_iff

end InfoGeometry.Algebra.IwasawaCyclotomics
