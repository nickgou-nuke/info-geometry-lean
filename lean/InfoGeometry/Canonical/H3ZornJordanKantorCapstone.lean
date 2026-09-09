import InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge
import InfoGeometry.Canonical.H3ZornTKKNative

/-!
# Native H3/Zorn Kantor capstone

This owner replaces the upstream Kantor capstone at the current theorem
surfaces.  It records only facts proved by the native Jordan/TKK owners; no
dimension or exceptional-Lie identification is inferred from the vanishing
Kantor operator alone.
-/

namespace InfoGeometry.Canonical.H3ZornJordanKantorCapstone

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.H3ZornTKKNative

abbrev H3 := H3Zorn ℝ

theorem kantor_boundary_packet (x y : H3) :
    kantorOperator x y = 0 ∧
    innerDerivation x y =
      (InfoGeometry.Algebra.h3ZornJordanInnerDerivation x y : Module.End ℝ H3) := by
  exact ⟨kantorOperator_zero x y, rfl⟩

theorem inner_derivation_packet (x y : H3) :
    H3ZornJordanDerivation (innerDerivation x y) ∧
    innerDerivation y x = -innerDerivation x y := by
  constructor
  · exact innerDerivation_is_jordan_derivation x y
  · apply LinearMap.ext
    intro z
    exact InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge.innerDerivation_swap x y z

theorem triple_derivation_packet (x y u v w : H3) :
    innerDerivation x y (jordanTriple u v w) =
      jordanTriple (innerDerivation x y u) v w +
        jordanTriple u (innerDerivation x y v) w +
          jordanTriple u v (innerDerivation x y w) :=
  innerDerivation_triple x y u v w

end InfoGeometry.Canonical.H3ZornJordanKantorCapstone
