/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SolderingIsomorphism

/-!
# Axiomatic Audit for Soldering Isomorphism

Direct Lean 4 `#print axioms` query verifying that all theorems depend strictly
on standard Lean 4 core axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Clifford.SolderingIsomorphism.Audit

open InfoGeometry.Clifford.SolderingIsomorphism

#print axioms solderingInv_soldering
#print axioms soldering_solderingInv
#print axioms det_soldering_inv_eq_q22
#print axioms q22_iff_det_zero
#print axioms splitNormSq_eq_q22
#print axioms rootPlus_null
#print axioms rootMinus_null
#print axioms rootPlus_spinor_annihilation
#print axioms rootMinus_spinor_annihilation

end InfoGeometry.Clifford.SolderingIsomorphism.Audit
