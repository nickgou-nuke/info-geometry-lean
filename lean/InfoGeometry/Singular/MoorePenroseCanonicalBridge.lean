/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Canonical.MoorePenrose

/-!
# Bridge between the two Moore--Penrose predicates

The repository carries the same four Penrose laws in
`InfoGeometry.Singular.MoorePenrose` and
`InfoGeometry.Canonical.MoorePenrose`.  The predicates are definitionally
isomorphic but not syntactically the same structure.  This file records the two
directions explicitly so that an owner theorem stated with one API can be used
by the other without duplicating the algebra.

No new mathematical hypothesis is introduced; both directions merely repackage
the same four laws.
-/

namespace InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse

variable {R : Type*} [Ring R] [StarRing R] {a b : R}

/-- View a canonical Moore--Penrose witness as a singular-owner witness. -/
theorem toSingular (h : IsMoorePenroseInverse a b) :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse a b :=
  ⟨h.aba_eq_a, h.bab_eq_b, h.ab_star, h.ba_star⟩

end InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse

namespace InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse

variable {R : Type*} [Ring R] [StarRing R] {a b : R}

/-- View a singular-owner Moore--Penrose witness as a canonical witness. -/
theorem toCanonical (h : IsMoorePenroseInverse a b) :
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse a b :=
  ⟨h.aba_eq_a, h.bab_eq_b, h.ab_adj_eq, h.ba_adj_eq⟩

end InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
