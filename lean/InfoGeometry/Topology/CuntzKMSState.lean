import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native Cuntz boundary owner

This namespace is retained for import compatibility.  The algebraic owner is
`InfoGeometry.Algebra.CuntzTensorQuotient`: no scalar phase model or fabricated
KMS temperature is introduced here.
-/

namespace InfoGeometry.Topology.CuntzKMSState

open InfoGeometry.Algebra.CuntzTensorQuotient

abbrev NativeCuntzTwo := CuntzAlg 2
abbrev NativeToeplitzCuntzTwo := CuntzToeplitzAlg 2

theorem native_cuntz_two_orthogonality (i j : Fin 2) :
    cuntzSdag 2 i * cuntzS 2 j = if i = j then 1 else 0 :=
  cuntz_orthogonality 2 i j

theorem native_toeplitz_cuntz_two_orthogonality (i j : Fin 2) :
    toeplitzSdag 2 i * toeplitzS 2 j = if i = j then 1 else 0 :=
  toeplitz_orthogonality 2 i j

theorem native_cuntz_two_partition_of_unity :
    (∑ i : Fin 2, cuntzS 2 i * cuntzSdag 2 i) =
      (1 : NativeCuntzTwo) :=
  cuntz_ranges_sum_one 2

end InfoGeometry.Topology.CuntzKMSState
