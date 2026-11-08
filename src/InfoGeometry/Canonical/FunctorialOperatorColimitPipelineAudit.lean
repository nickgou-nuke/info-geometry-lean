/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FunctorialOperatorColimitPipeline

/-!
# Axiomatic Audit for Star-Algebra Automorphism Conjugation Transport

Direct Lean 4 `#print axioms` query to confirm standard Lean 4 core axiomatic foundations:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero non-standard axioms.
-/

namespace InfoGeometry.Canonical.FunctorialColimit.Audit

open InfoGeometry.Canonical.FunctorialColimit

#print axioms transportStarAlgAut_apply
#print axioms transportStarAlgAut_refl
#print axioms transportStarAlgAut_trans
#print axioms transportStarAlgAut_isometry
#print axioms transportStarAlgAut_dist_eq

end InfoGeometry.Canonical.FunctorialColimit.Audit
