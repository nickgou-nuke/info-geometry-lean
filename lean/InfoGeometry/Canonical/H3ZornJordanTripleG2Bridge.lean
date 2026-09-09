import InfoGeometry.Canonical.H3ZornJordanTripleBridge

/-! Compatibility owner for the upstream combined H₃/G₂ bridge name. -/

namespace InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge

abbrev H3 := H3Zorn ℝ
noncomputable abbrev jordanTriple :=
  InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTriple

theorem jordanTriple_outer_symm (x y z : H3) :
    jordanTriple x y z = jordanTriple z y x := by
  exact InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTriple_outer_symm x y z

theorem jordanTriple_K_expression_zero (x y z : H3) :
    jordanTriple x z y - jordanTriple y z x = 0 := by
  exact InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTriple_K_expression_zero x y z

end InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
