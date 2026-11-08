/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.QDeformedCommutatorCanonical

/-!
# Endpoint consequences of the canonical homogeneous q-commutation owner

This module adds only endpoint specializations to the canonical
`QDeformedCommutatorCanonical` carrier. It introduces no second relation or
duplicate commutator API.
-/

namespace InfoGeometry.Algebra.QHeisenbergCommutator

variable {A : Type*} [Ring A]

open InfoGeometry.Algebra.QDeformedCommutatorCanonical

/-- At `q = 1`, homogeneous q-commutation is ordinary commutation. -/
theorem comm_zero_of_qCommutes_one {X Y : A}
    (h : QCommutes 1 X Y) : comm X Y = 0 := by
  simpa using comm_eq_of_qCommutes 1 X Y h

/-- At `q = -1`, homogeneous q-commutation is ordinary anticommutation. -/
theorem anti_zero_of_qCommutes_neg_one {X Y : A}
    (h : QCommutes (-1) X Y) : anti X Y = 0 := by
  simpa using anti_eq_of_qCommutes (-1) X Y h

end InfoGeometry.Algebra.QHeisenbergCommutator
