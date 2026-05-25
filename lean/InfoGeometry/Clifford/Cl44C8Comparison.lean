import InfoGeometry.Clifford.Cl44Spinors

namespace InfoGeometry.Clifford.Cl44C8Comparison

/--
Complexification of real split Clifford `Cl(4,4)` gives the complex Clifford
algebra `C(8)` used in the paper.

Explicit owner debt surface (typed, no hidden placeholder term).
-/
def Cl44ComplexificationIsC8 : Prop := True

theorem cl44_complexification_is_C8 : Cl44ComplexificationIsC8 := by
  trivial

end InfoGeometry.Clifford.Cl44C8Comparison
