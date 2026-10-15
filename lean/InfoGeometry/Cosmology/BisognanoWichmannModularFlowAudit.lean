/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Cosmology.BisognanoWichmannModularFlow

/-!
# Axiomatic Audit for Bisognano–Wichmann Modular Flow and Twistor Dyadics

Direct Lean 4 `#print axioms` query verifying that all theorems depend strictly
on standard Lean 4 core axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Cosmology.BisognanoWichmann.Audit

open InfoGeometry.Cosmology.BisognanoWichmann

#print axioms boostMatrix_det
#print axioms boostMatrix_add
#print axioms boostSpacetime_coords
#print axioms boostSpacetime_preserves_q22
#print axioms modularAutomorphism_axis
#print axioms modularAutomorphism_rootPlus
#print axioms modularAutomorphism_rootMinus
#print axioms dyadicMatrix_det
#print axioms dyadic_spacetime_vector_is_null
#print axioms dyadicMatrix_sq
#print axioms dyadicMatrix_nilpotent_iff

end InfoGeometry.Cosmology.BisognanoWichmann.Audit
