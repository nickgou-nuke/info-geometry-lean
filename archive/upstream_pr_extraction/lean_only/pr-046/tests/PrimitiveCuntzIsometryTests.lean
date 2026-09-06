import InfoGeometry.Canonical.PrimitiveCuntzIsometry

open InfoGeometry.Canonical.PrimitiveCuntzIsometry
open InfoGeometry.GrandUnification.UHF

noncomputable section

#check P_L
#check P_R
#check cuntz_partition_exactness
#check P_L_sq
#check P_R_sq
#check cuntz_orthogonality
#check P_L_mul_P_R_eq_zero

example {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
    [UHF : CuntzIsometryData A] :
    P_L (A := A) + P_R (A := A) = 1 :=
  cuntz_partition_exactness (A := A)

example {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
    [UHF : CuntzIsometryData A] :
    star (CuntzIsometryData.S_L (A := A)) * CuntzIsometryData.S_R (A := A) = 0 :=
  cuntz_orthogonality (A := A)

example {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
    [UHF : CuntzIsometryData A] :
    P_L (A := A) * P_R (A := A) = 0 :=
  P_L_mul_P_R_eq_zero (A := A)
