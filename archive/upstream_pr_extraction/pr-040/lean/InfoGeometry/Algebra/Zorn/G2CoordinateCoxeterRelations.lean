/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

/-!
# Coxeter relations on the concrete full-root permutation carrier

These are relations of the actual coordinate permutations.  They are kept
separate from the cyclotomic carrier because that carrier is not
equivariantly calibrated to the concrete G₂ reflections.
-/

namespace InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

theorem coordinate_c_pow_six : cRoot ^ 6 = 1 := cRoot_pow_six

theorem coordinate_s1_sq : s1Root ^ 2 = 1 := s1Root_sq

theorem coordinate_s2_sq : s2Root ^ 2 = 1 := s2Root_sq

theorem coordinate_s1_conj_c :
    s1Root * cRoot * s1Root = cRoot⁻¹ := by
  decide

end InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
