import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation

namespace InfoGeometry.OperatorAlgebra.SplitOctonionGroundedCrossSection

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation

abbrev proj11 : SplitOct := ePlus
abbrev proj22 : SplitOct := eMinus
abbrev splitCenter : SplitOct := H
abbrev euclideanSquareDirection : SplitOct := J
abbrev hyperbolicSquareDirection : SplitOct := H

@[simp] theorem proj11_add_proj22 : addZ proj11 proj22 = oneZ := by
  simpa [proj11, proj22] using ePlus_add_eMinus_eq_oneZ

@[simp] theorem proj11_mul_proj11 : mulZ proj11 proj11 = proj11 := by
  simpa [proj11] using ePlus_idempotent

@[simp] theorem proj22_mul_proj22 : mulZ proj22 proj22 = proj22 := by
  simpa [proj22] using eMinus_idempotent

@[simp] theorem proj11_mul_proj22 : mulZ proj11 proj22 = zeroZ := by
  simpa [proj11, proj22] using ePlus_mul_eMinus

@[simp] theorem proj22_mul_proj11 : mulZ proj22 proj11 = zeroZ := by
  simpa [proj11, proj22] using eMinus_mul_ePlus

@[simp] theorem splitCenter_eq_proj_diff : splitCenter = subZ proj11 proj22 := by
  rfl

@[simp] theorem splitCenter_sq : mulZ splitCenter splitCenter = oneZ := by
  simpa [splitCenter] using H_sq

@[simp] theorem splitCenter_detZ : detZ splitCenter = -1 := by
  simpa [splitCenter] using detZ_H

@[simp] theorem proj11_detZ : detZ proj11 = 0 := by
  simpa [proj11] using detZ_ePlus

@[simp] theorem proj22_detZ : detZ proj22 = 0 := by
  simpa [proj22] using detZ_eMinus

@[simp] theorem oneZ_detZ : detZ oneZ = 1 := by
  simpa using detZ_oneZ

@[simp] theorem norm_proj11 : normZ proj11 = 0 := by
  simp [normZ, proj11]

@[simp] theorem norm_proj22 : normZ proj22 = 0 := by
  simp [normZ, proj22]

@[simp] theorem norm_splitCenter : normZ splitCenter = -1 := by
  simpa [normZ, splitCenter] using detZ_H

@[simp] theorem euclideanSquareDirection_sq :
    mulZ euclideanSquareDirection euclideanSquareDirection = negZ oneZ := by
  simpa [euclideanSquareDirection] using J_sq_neg_oneZ

@[simp] theorem euclideanSquareDirection_detZ : detZ euclideanSquareDirection = 1 := by
  simpa [euclideanSquareDirection] using detZ_J

@[simp] theorem hyperbolicSquareDirection_sq :
    mulZ hyperbolicSquareDirection hyperbolicSquareDirection = oneZ := by
  simpa [hyperbolicSquareDirection] using H_sq

@[simp] theorem hyperbolicSquareDirection_detZ :
    detZ hyperbolicSquareDirection = -1 := by
  simpa [hyperbolicSquareDirection] using detZ_H

end InfoGeometry.OperatorAlgebra.SplitOctonionGroundedCrossSection
