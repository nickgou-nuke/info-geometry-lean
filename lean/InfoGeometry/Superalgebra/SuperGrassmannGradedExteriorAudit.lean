/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.SuperGrassmannGradedExterior

/-!
# Audit: Archetypes of Supergeometry — Graded Grassmann Algebras

Independent audit verifying that all theorems in
`InfoGeometry.Superalgebra.SuperGrassmannGradedExterior` compile cleanly and
depend strictly on standard Core Lean 4 / Mathlib axioms (`[propext, Classical.choice, Quot.sound]`),
with zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Superalgebra.SuperGrassmannAudit

open InfoGeometry.Superalgebra.SuperGrassmann

#print axioms bosonic_ne_fermionic
#print axioms koszulSign_zero_left
#print axioms koszulSign_zero_right
#print axioms koszulSign_symm
#print axioms koszulSign_mul
#print axioms koszulSign_one_left
#print axioms koszulSign_one_one
#print axioms ι_mul_ι_anticomm
#print axioms ι_mul_ι_swap
#print axioms fermionic_nilpotent
#print axioms ι_mul_graded_comm
#print axioms supercommutative_exterior
#print axioms superCommutator_vanishes
#print axioms superCommutator_one_one_eq_anticomm

end InfoGeometry.Superalgebra.SuperGrassmannAudit
