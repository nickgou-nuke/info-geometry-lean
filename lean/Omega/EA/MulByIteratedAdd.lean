/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA

/-- Paper-facing corollary: stable multiplication is iterated stable addition.
    thm:mul-by-iterated-add -/
theorem paper_mul_by_iterated_add {m : ℕ} (c d : Omega.X m) :
    Omega.X.iteratedStableAdd c (Omega.stableValue d) = Omega.X.stableMul d c := by
  simpa using Omega.X.iteratedStableAdd_eq_stableMul c d

end Omega.EA
