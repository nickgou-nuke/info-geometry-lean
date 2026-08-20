import Mathlib
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Raw split-octonion commutator obstruction

This owner records the native Akivis/Jacobiator readback.  It deliberately
does not install a Lie structure on the non-associative Zorn carrier.
-/

namespace InfoGeometry.Canonical.SplitOctonionMalcev

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

abbrev Carrier := ZornVectorMatrix ℝ

def rawCommutator (X Y : Carrier) : Carrier := commutator X Y

def rawJacobiator (X Y Z : Carrier) : Carrier :=
  commutatorJacobiator X Y Z

theorem rawJacobiator_akivis (X Y Z : Carrier) :
    rawJacobiator X Y Z =
      sub
        (add (add (associator X Z Y) (associator Y X Z))
          (associator Z Y X))
        (add (add (associator X Y Z) (associator Y Z X))
          (associator Z X Y)) :=
  commutatorJacobiator_eq_associator_alternating X Y Z

theorem rawJacobiator_upper_property :
    rawJacobiator (U 0 : Carrier) (U 1) (U 2) =
      diagonal (6 : ℝ) (-6 : ℝ) :=
  commutator_jacobi_U_zero_U_one_U_two

theorem rawJacobiator_upper_property_ne_zero :
    rawJacobiator (U 0 : Carrier) (U 1) (U 2) ≠ zero := by
  apply commutator_jacobi_U_zero_U_one_U_two_ne_zero
  norm_num

theorem raw_commutator_not_lie :
    rawJacobiator (U 0 : Carrier) (U 1) (U 2) ≠ zero :=
  rawJacobiator_upper_property_ne_zero

end InfoGeometry.Canonical.SplitOctonionMalcev
