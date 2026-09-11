import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.FreudenthalKantorTripleSystem

/-!
# Operator readout of the Freudenthal--Kantor identities

This owner does not construct a TKK Lie algebra.  It exposes the supplied
Freudenthal--Kantor identities as equalities of endomorphisms, which is the
form needed by a later bracket construction.
-/

namespace InfoGeometry.Algebra.FreudenthalKantorTripleSystem

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
variable (data : FreudenthalKantorTripleSystem (R := R) (U := U))

def kOperator (x y : U) : Module.End R U where
  toFun z := data.K x y z
  map_add' u v := by
    simp [K, fktsK, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' r z := by
    simp [K, fktsK, smul_sub]
    module

@[simp] theorem kOperator_apply (x y z : U) :
    kOperator data x y z = data.K x y z := rfl

def tripleOperator (x y : U) : Module.End R U where
  toFun z := data.triple x y z
  map_add' u v := by
    simp
  map_smul' r z := by
    simp

@[simp] theorem tripleOperator_apply (x y z : U) :
    tripleOperator data x y z = data.triple x y z := rfl

theorem tripleOperator_commutator (x y u v : U) :
    ⁅tripleOperator data x y, tripleOperator data u v⁆ =
      tripleOperator data (data.triple x y u) v +
        data.epsilon • tripleOperator data u (data.triple y x v) := by
  apply LinearMap.ext
  intro z
  change data.triple x y (data.triple u v z) -
      data.triple u v (data.triple x y z) = _
  simpa [tripleOperator, Ring.lie_def, Module.End.mul_apply] using
    data.left_identity x y u v z

theorem k_identity_operator (x y z w : U) (u : U) :
    kOperator data (data.triple x y z) w u +
        kOperator data z (data.triple x y w) u +
      data.delta • kOperator data x (kOperator data z w y) u = 0 := by
  exact data.k_identity x y z w u

theorem k_identity_operator_ext (x y z w : U) :
    kOperator data (data.triple x y z) w +
        kOperator data z (data.triple x y w) +
      data.delta • kOperator data x (kOperator data z w y) = 0 := by
  apply LinearMap.ext
  intro u
  exact k_identity_operator data x y z w u

end InfoGeometry.Algebra.FreudenthalKantorTripleSystem
