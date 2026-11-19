/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl55ChiralSectorPredicateBridge
import InfoGeometry.LinearAlgebra.ExteriorDeterminantLine

/-!
# A determinant line for the native real Clifford chiral map

The existing `Cl(5,5)` owner constructs maps between two different native
chirality submodules and proves that each submodule has real dimension
sixteen. Their determinant carrier is therefore the actual dual of one
sixteenth exterior power tensored with the other.

The distinguished positive Clifford generator gives a nonzero determinant
tensor because its existing chiral sector map is bijective. This concerns
finite Clifford-vector action, without asserting an elliptic Dirac operator,
a lattice overlap operator, or a complex determinant phase.
-/

noncomputable section

open scoped TensorProduct

namespace InfoGeometry.Clifford.Cl55ChiralDeterminantLine

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
open InfoGeometry.LinearAlgebra.ExteriorDeterminantLine

/-- The two actual sixteen-dimensional chiral submodules determine a real
one-dimensional native dual-tensor carrier. -/
theorem chiralDeterminantLine_finrank :
    Module.finrank ℝ
      (Module.Dual ℝ (⋀[ℝ]^16 chiralPlusSector) ⊗[ℝ]
        (⋀[ℝ]^16 chiralMinusSector)) = 1 := by
  exact determinantLine_finrank 16
    cl55_real_chiral_spinor_sectors_finrank.1
    cl55_real_chiral_spinor_sectors_finrank.2

/-- The existing positive generator exchanges the two native chiral
submodules bijectively, so its canonical determinant tensor is nonzero. -/
theorem positiveGenerator_determinantTensor_ne_zero :
    determinantTensor 16
      (cl55OddGeneratorPlusToMinus (wittBasis (Sum.inl 0))) ≠ 0 := by
  exact (determinantTensor_ne_zero_iff_bijective 16
    cl55_real_chiral_spinor_sectors_finrank.1
    cl55_real_chiral_spinor_sectors_finrank.2
    (cl55OddGeneratorPlusToMinus (wittBasis (Sum.inl 0)))).2
      cl55_positive_generator_sector_exchange_bijective

end InfoGeometry.Clifford.Cl55ChiralDeterminantLine
