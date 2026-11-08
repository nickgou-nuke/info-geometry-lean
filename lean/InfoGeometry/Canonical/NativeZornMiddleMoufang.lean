/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.MoufangIdentities
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication

/-!
# Gap 2: Native Zorn Middle Moufang

Native Moufang laws on `ZornVectorMatrix R` for arbitrary `[CommRing R]`,
freed from the integral presentation. All proofs are structural consequences
of the already-proved alternativity laws in `ZornAlternativeLaws`.
-/

namespace InfoGeometry.Canonical.NativeZornMiddleMoufang

open InfoGeometry.Algebra

variable {R : Type*} [CommRing R]

/-- Native middle Moufang identity on `ZornVectorMatrix R`. -/
theorem middle_moufang_native (X Y Z : ZornVectorMatrix R) :
    (X * Y) * (Z * X) = X * ((Y * Z) * X) :=
  InfoGeometry.Algebra.ZornVectorMatrix.middle_moufang X Y Z

/-- Native flexible law on `ZornVectorMatrix R`. -/
theorem flexible_native (X Y : ZornVectorMatrix R) :
    (X * Y) * X = X * (Y * X) :=
  InfoGeometry.Algebra.ZornVectorMatrix.flexible_law X Y

/-- Transport equivalence: native middle Moufang implies the integral presentation. -/
theorem moufang_transport_integral_native (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul x y) (splitOctonionMul z x) =
      splitOctonionMul x (splitOctonionMul (splitOctonionMul y z) x) :=
  splitOctonion_moufang_middle x y z

end InfoGeometry.Canonical.NativeZornMiddleMoufang
