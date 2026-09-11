import InfoGeometry.Algebra.AkivisIdentity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# NC-Zorn-facing names for the generic Akivis owner

The underlying carrier is deliberately not reconstructed here.  Once a
concrete NC-Zorn representation supplies `NonUnitalNonAssocRing`, the generic
Akivis theorems apply by these names.  Alternativity and Malcev admissibility
remain separate audits.
-/

namespace InfoGeometry.Canonical.NCZorn

open InfoGeometry.Algebra

variable {A : Type*} [NonUnitalNonAssocRing A]

def zornCommutator (x y : A) : A := akivisBracket x y
def zornAssociator (x y z : A) : A := _root_.associator x y z
def zornJacobiator (x y z : A) : A := akivisJacobiator x y z

theorem zorn_akivis_identity (x y z : A) :
    zornJacobiator x y z =
      zornAssociator x y z + zornAssociator y z x +
        zornAssociator z x y - zornAssociator y x z -
          zornAssociator z y x - zornAssociator x z y := by
  exact akivis_identity x y z

theorem zorn_right_nested_jacobiator_eq_neg (x y z : A) :
    rightNestedJacobiator x y z = -zornJacobiator x y z := by
  exact rightNestedJacobiator_eq_neg x y z

theorem zorn_regular_representation_defect (x y z : A) :
    leftMultiplicationCommutatorDefect x y z =
      -zornAssociator x y z + zornAssociator y x z := by
  exact leftMultiplicationCommutatorDefect_eq_associator_difference x y z

theorem zorn_regular_representation_defect_eq_neg_two
    (hleft : ∀ x y z : A,
      zornAssociator y x z = -zornAssociator x y z)
    (x y z : A) :
    leftMultiplicationCommutatorDefect x y z =
      -(zornAssociator x y z + zornAssociator x y z) := by
  exact leftMultiplicationCommutatorDefect_eq_neg_two_associator hleft x y z

end InfoGeometry.Canonical.NCZorn
