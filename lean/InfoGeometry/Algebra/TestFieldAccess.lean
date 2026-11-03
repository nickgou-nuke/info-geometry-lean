/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- Test file -/
universe u

namespace InfoGeometry.Algebra.TestFieldAccess

structure MyFibration where
  base : Type u
  total : Type u
  projection : total → base

def test {F : MyFibration} (e : F.total) : F.base := F.projection e

end InfoGeometry.Algebra.TestFieldAccess
