/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.CompatibleDerivations
import InfoGeometry.LinearAlgebra.CompatibleBilinearColimit

/-!
# Declaration audit for compatible algebraic colimits

The operators, derivation, and bilinear form are constructed on Mathlib's native
direct limit. The audit covers every public declaration of the three new owners
and the four native radical-map lemmas. Finite Euler remainders are retained;
positivity is transferred only under its stated finite-stage hypotheses.
-/

#print axioms InfoGeometry.Categorical.CompatibleEndomorphisms.liftEnd
#print axioms InfoGeometry.Categorical.CompatibleEndomorphisms.liftEnd_of
#print axioms InfoGeometry.Categorical.CompatibleEndomorphisms.liftEnd_involution
#print axioms InfoGeometry.Categorical.CompatibleEndomorphisms.liftEnd_reflection
#print axioms InfoGeometry.Categorical.CompatibleEndomorphisms.liftEnd_eigen_equation
#print axioms InfoGeometry.Categorical.CompatibleEndomorphisms.liftEnd_eigenpair
#print axioms InfoGeometry.Categorical.CompatibleDerivations.map_units_logDeriv
#print axioms InfoGeometry.Categorical.CompatibleDerivations.colimitDerivation
#print axioms InfoGeometry.Categorical.CompatibleDerivations.colimitDerivation_of
#print axioms InfoGeometry.Categorical.CompatibleDerivations.colimitDerivation_unique
#print axioms InfoGeometry.Categorical.CompatibleDerivations.units_logDeriv_of
#print axioms InfoGeometry.Categorical.CompatibleDerivations.negative_units_logDeriv_eulerProduct_of_eq_sum_add_remainder
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_of
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_unique
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_isSymm
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_nonneg_iff
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.negative_survives
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.negative_survives_quotient
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.quotient_nonneg_iff
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.radical_comap_le
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.radical_map_le_of_nonneg
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm_mapQ
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.mapQ_injective
