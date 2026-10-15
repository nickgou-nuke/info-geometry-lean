/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ChevalleyKaplanskyBraKetBridge

/-!
# Axiomatic Audit for Idempotent Ideal Annihilation

Verification of standard Lean 4 core axiomatic foundations:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero non-standard axioms.
-/

namespace InfoGeometry.Algebra.ChevalleyKaplansky.Audit

open InfoGeometry.Algebra.ChevalleyKaplansky

#print axioms left_ideal_mul_right_complement_ideal_eq_zero
#print axioms idempotent_state_reconstruction
#print axioms idempotent_kernel_intersection_trivial
#print axioms nilpotent_image_subset_kernel

end InfoGeometry.Algebra.ChevalleyKaplansky.Audit
