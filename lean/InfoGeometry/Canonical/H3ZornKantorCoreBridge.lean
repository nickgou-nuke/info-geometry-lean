import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Algebra.KantorTripleFiveGrading

/-!
# Current-owner H3/Zorn Kantor core

This bridge exposes the part of the upstream Kantor proposal already owned by
the repository: the split Albert Jordan product and its inner derivations.
It does not assert a TKK or five-graded Lie identification.
-/

namespace InfoGeometry.Canonical.H3ZornKantorCoreBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

abbrev H3 := H3Zorn ℝ

theorem inner_derivation_leibniz (a b x y : H3) :
    (h3ZornJordanInnerDerivation a b : Module.End ℝ H3) (x * y) =
      (h3ZornJordanInnerDerivation a b : Module.End ℝ H3) x * y +
        x * (h3ZornJordanInnerDerivation a b : Module.End ℝ H3) y :=
  h3ZornJordanInnerDerivation_leibniz a b x y

theorem inner_derivation_trace_zero (a b x : H3) :
    linearTrace
        ((h3ZornJordanInnerDerivation a b : Module.End ℝ H3) x) = 0 :=
  h3ZornJordanInnerDerivation_linearTrace_zero a b x

end InfoGeometry.Canonical.H3ZornKantorCoreBridge
