import InfoGeometry.Canonical.H3ZornJordanKantorCapstone

/-! Compatibility owner for the upstream concrete H₃ Kantor path.

The current repository exposes the proved Jordan-boundary and inner-
derivation packets through the capstone owner.  The abstract Kantor instance
and any exceptional-Lie dimension identification remain separate obligations.
-/
namespace InfoGeometry.Canonical.H3ZornKantorTripleSystem

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.H3ZornTKKNative
open InfoGeometry.Canonical.H3ZornJordanKantorCapstone

abbrev H3 := H3Zorn ℝ

theorem jordanTriple_eq_mul_add_inner (x y z : H3) :
    jordanTriple x y z = (x * y) * z + innerDerivation x y z := by
  exact H3ZornTKKNative.jordanTriple_eq_mul_add_inner x y z

theorem inner_swap_apply (x y z : H3) :
    innerDerivation y x z = -innerDerivation x y z := by
  exact InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge.innerDerivation_swap x y z

theorem jordan_boundary_packet (x y : H3) :
    kantorOperator x y = 0 := by
  exact kantorOperator_zero x y

end InfoGeometry.Canonical.H3ZornKantorTripleSystem
