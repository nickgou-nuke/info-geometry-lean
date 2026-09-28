import InfoGeometry.Canonical.CanonicalZornBianchiDefect
import InfoGeometry.Canonical.NCZornAkivisIdentity

namespace InfoGeometry.Canonical.Superconnection

open InfoGeometry.Canonical.CanonicalZornBianchiDefect
open InfoGeometry.Canonical.NCZorn

variable {A : Type*} [NonUnitalNonAssocRing A]

structure NonAssocGradedMaurerCartanForm (A : Type*) [NonUnitalNonAssocRing A] where
  w_n2 : A
  w_n1 : A
  w_0 : A
  w_p1 : A
  w_p2 : A

theorem superconnection_bianchi_defect (w : NonAssocGradedMaurerCartanForm A) :
    rightNestedBianchi w.w_n1 w.w_0 w.w_p1 = -zornJacobiator w.w_n1 w.w_0 w.w_p1 := by
  exact rightNestedBianchi_eq_neg_jacobiator w.w_n1 w.w_0 w.w_p1

end InfoGeometry.Canonical.Superconnection
