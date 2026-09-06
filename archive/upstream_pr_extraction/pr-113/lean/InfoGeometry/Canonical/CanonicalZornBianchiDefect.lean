import InfoGeometry.Canonical.NCZornAkivisIdentity

/-!
# The purely algebraic right-nested Bianchi defect

This is the cyclic nested-commutator expression on the explicit split-Zorn
carrier.  It is not a differential-form Yang--Mills Bianchi identity: no
exterior degree, connection one-form, or flux functional is introduced here.
-/

namespace InfoGeometry.Canonical.CanonicalZornBianchiDefect

open InfoGeometry.Canonical.NCZorn
open InfoGeometry.Algebra

variable {A : Type*} [NonUnitalNonAssocRing A]

def rightNestedBianchi (x y z : A) : A :=
  zornCommutator x (zornCommutator y z) +
    (zornCommutator y (zornCommutator z x) +
      zornCommutator z (zornCommutator x y))

theorem rightNestedBianchi_eq_neg_jacobiator (x y z : A) :
    rightNestedBianchi x y z = -(zornJacobiator x y z) := by
  simpa [rightNestedBianchi, zornCommutator, zornJacobiator,
    rightNestedJacobiator, add_assoc] using rightNestedJacobiator_eq_neg x y z

end InfoGeometry.Canonical.CanonicalZornBianchiDefect
