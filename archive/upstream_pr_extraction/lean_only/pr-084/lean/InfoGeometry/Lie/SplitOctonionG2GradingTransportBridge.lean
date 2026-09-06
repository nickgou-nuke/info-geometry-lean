import InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge

/-!
# Native split-octonion grading readout

The repository's proved fine grading is the canonical cochain grading
`Fin 3 → ZMod 2`.  This owner re-exports its basis-level multiplication
consequence under the Lie/G₂ navigation namespace.  It intentionally does
not invent a derivation-grade submodule: transporting this grading to
`Der(𝕆ₛ)` requires an additional operator-level construction.

Thus the current theorem boundary is

`basisMul → cochainF → gradeAdd`,

while the derivation-bracket grading remains a downstream bridge.
-/

namespace InfoGeometry.Lie.SplitOctonionG2GradingTransportBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge

abbrev Z23Group := Grade

def octonionGrade (b : IntegralSplitBasis) : Z23Group :=
  gradeOfBasis b

@[simp] theorem octonionGrade_eq_native (b : IntegralSplitBasis) :
    octonionGrade b = gradeOfBasis b := rfl

theorem basisMul_cochain_target (x y : Z23Group) :
    (fun b =>
        (basisMul (basisOfGrade x) (basisOfGrade y) b : ℚ)) =
      cochainF x y •
        (fun b =>
          (splitBasisVector (basisOfGrade (gradeAdd x y)) b : ℚ)) := by
  exact native_basisMul_is_cochainF x y

theorem basisMul_cochain_target_nonzero (x y : Z23Group) :
    cochainF x y ≠ 0 :=
  cochainF_ne_zero x y

theorem cochain_associator_is_three_cocycle (x y z w : Z23Group) :
    associatorCochain y z w * associatorCochain x (gradeAdd y z) w *
        associatorCochain x y z =
      associatorCochain (gradeAdd x y) z w *
        associatorCochain x y (gradeAdd z w) :=
  native_associator_three_cocycle x y z w

theorem cochain_exchange_sq (x y : Z23Group) :
    exchangeCochain x y * exchangeCochain x y = 1 :=
  exchangeCochain_sq x y

end InfoGeometry.Lie.SplitOctonionG2GradingTransportBridge
