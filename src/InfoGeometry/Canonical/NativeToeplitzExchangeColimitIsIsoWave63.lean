/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorFrechetFormColimitEndomorphismBridge

namespace InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree

open CategoryTheory CategoryTheory.Limits

 theorem exchangeColimit_isIso :
    IsIso exchangeColimit := by
  rw [← exchangeColimitIso_hom_eq_exchangeColimit]
  exact exchangeColimitIso.isIso_hom

end InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree
