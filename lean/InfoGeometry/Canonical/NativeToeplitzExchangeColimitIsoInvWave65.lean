/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NativeToeplitzExchangeColimitIsIsoWave63

namespace InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree

open CategoryTheory CategoryTheory.Limits

theorem exchangeColimitIso_inv_eq_exchangeColimit :
    exchangeColimitIso.inv = exchangeColimit := by
  rw [← exchangeColimitIso_hom_eq_exchangeColimit]
  rfl

end InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree
