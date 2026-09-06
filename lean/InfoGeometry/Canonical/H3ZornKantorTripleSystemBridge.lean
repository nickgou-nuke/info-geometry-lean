import InfoGeometry.Canonical.H3ZornTKKNative

/-! The Kantor-facing normal form of the already installed H3 triple.
Only identities owned by the native Jordan and TKK carriers are exported here;
the full abstract Kantor instance remains a separate construction. -/

namespace InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.H3ZornTKKNative

abbrev H3 := H3Zorn ℝ

theorem jordanTriple_eq_left_mul_add_inner (x y z : H3) :
    jordanTriple x y z = (x * y) * z + innerDerivation x y z := by
  exact H3ZornTKKNative.jordanTriple_eq_mul_add_inner x y z

theorem innerDerivation_swap (x y z : H3) :
    innerDerivation y x z = -innerDerivation x y z := by
  simp [innerDerivation, innerDerivation_apply]

theorem kantor_operator_vanishes (x y : H3) :
    kantorOperator x y = 0 :=
  kantorOperator_zero x y

end InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge
