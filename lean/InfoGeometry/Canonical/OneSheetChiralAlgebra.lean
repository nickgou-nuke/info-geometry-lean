import InfoGeometry.Canonical.SplitOctonionJordanStructure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# One-sheet Jordan algebra readout

This owner gives the one-sheet name to the already verified real spin-factor
core.  It is a forwarding theorem layer: it does not identify the carrier
with an unverified octonion-to-matrix representation and does not assume a
two-sheet TKK derivation owner.
-/

namespace InfoGeometry.Canonical.OneSheetChiralAlgebra

open SplitOctonionJordanCore
open SplitOctonionJordanForm
open SplitOctonionJordanStructure

abbrev Carrier := SpinCarrier

abbrev product : Carrier → Carrier → Carrier := jordanMul

theorem product_comm (x y : Carrier) :
    product x y = product y x :=
  jordanMul_comm x y

theorem product_jordan_identity (x y : Carrier) :
    product (product x y) (product x x) =
      product x (product y (product x x)) :=
  jordanMul_jordan_identity x y

theorem product_unit (x : Carrier) :
    product spinUnit x = x := jordanMul_unit_left x

theorem product_spin_factor_formula (a b : ℝ) (u v : MiddleCarrier) :
    product (a, u) (b, v) =
      (a * b + beta44 u v, fun i => a * v i + b * u i) :=
  jordan_spin_factor_formula a b u v

theorem product_left_operator_readout (x y : Carrier) :
    leftJordanMul x y = product x y := rfl

theorem inner_operator_readout (x y z : Carrier) :
    innerJordanDerivation x y z =
      product x (product y z) - product y (product x z) := by
  rfl

end InfoGeometry.Canonical.OneSheetChiralAlgebra
