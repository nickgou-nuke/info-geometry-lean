/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs

/-!
# Associative residue commutator

This owner keeps the generic bracket independent of configuration-space and
analytic constructions. The namespace, type, and body are preserved from the
historical `KZLogarithmicConnection` declaration.
-/

namespace InfoGeometry.Canonical.KZLogarithmicConnection

/-- The commutator bracket $[X, Y] = X Y - Y X$ in an associative algebra. -/
def bracket {A : Type*} [Ring A] (X Y : A) : A := X * Y - Y * X

end InfoGeometry.Canonical.KZLogarithmicConnection
