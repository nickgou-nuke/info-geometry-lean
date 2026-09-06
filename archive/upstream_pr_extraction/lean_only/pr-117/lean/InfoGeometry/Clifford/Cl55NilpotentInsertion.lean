import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.NilpotentBinomial
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv

/-!
# Isotropic Clifford insertions

The Clifford relation turns a null vector into a square-zero operator.  The
second theorem then applies the finite nilpotent binomial law.
-/

namespace InfoGeometry.Clifford.Cl55NilpotentInsertion

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep

theorem ι55_mul_self_eq_zero_of_isotropic
    (v : V55) (hv : Q55 v = 0) :
    ι55 v * ι55 v = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, hv, map_zero]

theorem one_add_ι55_pow_of_isotropic
    (v : V55) (hv : Q55 v = 0) (n : ℕ) :
    (1 + ι55 v) ^ n = 1 + n • ι55 v := by
  exact InfoGeometry.Clifford.NilpotentBinomial.one_add_pow_of_sq_zero
    (ι55 v) (ι55_mul_self_eq_zero_of_isotropic v hv) n

theorem spinorMatrix_ι55_mul_self_eq_zero_of_isotropic
    (v : V55) (hv : Q55 v = 0) :
    cl55SpinorAlgEquiv (ι55 v) * cl55SpinorAlgEquiv (ι55 v) = 0 := by
  rw [← map_mul]
  rw [ι55_mul_self_eq_zero_of_isotropic v hv]
  exact map_zero cl55SpinorAlgEquiv

theorem one_add_spinorMatrix_ι55_pow_of_isotropic
    (v : V55) (hv : Q55 v = 0) (n : ℕ) :
    (1 + cl55SpinorAlgEquiv (ι55 v)) ^ n =
      1 + n • cl55SpinorAlgEquiv (ι55 v) := by
  exact InfoGeometry.Clifford.NilpotentBinomial.one_add_pow_of_sq_zero
    (cl55SpinorAlgEquiv (ι55 v))
    (spinorMatrix_ι55_mul_self_eq_zero_of_isotropic v hv) n

theorem spinorMatrix_one_add_mul_one_sub_of_isotropic
    (v : V55) (hv : Q55 v = 0) :
    (1 + cl55SpinorAlgEquiv (ι55 v)) *
        (1 - cl55SpinorAlgEquiv (ι55 v)) = 1 := by
  exact InfoGeometry.Clifford.NilpotentBinomial.one_add_mul_one_sub_of_sq_zero
    (cl55SpinorAlgEquiv (ι55 v))
    (spinorMatrix_ι55_mul_self_eq_zero_of_isotropic v hv)

theorem spinorMatrix_one_sub_mul_one_add_of_isotropic
    (v : V55) (hv : Q55 v = 0) :
    (1 - cl55SpinorAlgEquiv (ι55 v)) *
        (1 + cl55SpinorAlgEquiv (ι55 v)) = 1 := by
  exact InfoGeometry.Clifford.NilpotentBinomial.one_sub_mul_one_add_of_sq_zero
    (cl55SpinorAlgEquiv (ι55 v))
    (spinorMatrix_ι55_mul_self_eq_zero_of_isotropic v hv)

end InfoGeometry.Clifford.Cl55NilpotentInsertion
