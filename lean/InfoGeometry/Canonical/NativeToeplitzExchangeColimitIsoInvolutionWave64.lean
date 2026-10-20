/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NativeToeplitzExchangeColimitIsIsoWave63

namespace InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree

open CategoryTheory CategoryTheory.Limits

 theorem exchangeColimitIso_comp_self :
    exchangeColimitIso ≪≫ exchangeColimitIso =
      Iso.refl (colimit stageDiagram) := by
  apply CategoryTheory.Iso.ext
  rw [Iso.trans_hom, exchangeColimitIso_hom_eq_exchangeColimit]
  exact induced_exchange_involutive

end InfoGeometry.Canonical.OperatorFrechetFormColimit.NativeToeplitzCuntzThree
