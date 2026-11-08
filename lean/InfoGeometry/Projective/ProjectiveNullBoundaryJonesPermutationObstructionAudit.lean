/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction

/-!
# Source audit: the permutation shadow loses Jones braid phase

The square of the first presented braid generator is killed by the
permutation shadow but maps to `-I` under the Jones representation. This
proves non-factorization through that specific finite shadow; it does not
exclude richer monodromy data.
-/

#print axioms InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction.braidPermutation_sig0_sq
#print axioms InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction.jonesBraidRepresentation_firstGeneratorSquare_val
#print axioms InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction.jonesBraidRepresentation_sig0_sq_ne_one
#print axioms InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction.jonesBraidRepresentation_not_factor_through_permutation
