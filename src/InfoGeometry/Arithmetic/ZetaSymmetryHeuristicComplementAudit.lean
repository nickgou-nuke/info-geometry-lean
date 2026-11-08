/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement

/-!
# Source audit: centered symmetry does not confine zeros to the axis

The explicit even polynomial `z ↦ z^2 - 1` has the off-axis zero pair ±1.
The repaired implication requires the separate `NoOffAxisZeros` premise;
evenness itself only reflects zeros.
-/

#print axioms InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement.even_zero_reflection
#print axioms InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement.evenOffAxisWitness_even
#print axioms InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement.even_symmetry_allows_off_axis_zero_pair
#print axioms InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement.centeredCriticalLine_of_noOffAxisZeros
