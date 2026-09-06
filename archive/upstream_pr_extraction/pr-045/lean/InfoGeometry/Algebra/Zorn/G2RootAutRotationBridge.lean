import InfoGeometry.Algebra.Zorn.G2TwoRootSystem

/-!
# Structural Weyl-rotation bridge for concrete `G₂(2)` root automorphisms

This file records the reusable structural step from the already-verified
`Short(1)` root to `Short(2)`.  It deliberately does not assert the corresponding
PC-word conjugation: that remains a separate theorem about the concrete PC
normal form.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutRotationBridge

open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

/-- `Short(2)` is the Coxeter-rotation conjugate of `Short(1)`. -/
theorem rootAut_short_two_eq_c_conj_short_one :
    rootAut (RootLength.Short, (2 : ZMod 6)) =
      c * rootAut (RootLength.Short, (1 : ZMod 6)) * c⁻¹ := by
  simpa [cAction] using
    (c_rootAut_c (RootLength.Short, (1 : ZMod 6))).symm

/-- Equivalent forward-oriented form. -/
theorem c_conj_rootAut_short_one_eq_short_two :
    c * rootAut (RootLength.Short, (1 : ZMod 6)) * c⁻¹ =
      rootAut (RootLength.Short, (2 : ZMod 6)) := by
  exact c_rootAut_c (RootLength.Short, (1 : ZMod 6))

end InfoGeometry.Algebra.Zorn.G2RootAutRotationBridge
