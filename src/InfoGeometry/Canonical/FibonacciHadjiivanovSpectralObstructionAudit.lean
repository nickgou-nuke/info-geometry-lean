/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.FibonacciHadjiivanovSpectralObstruction

/-!
# Source audit: normality forces vanishing Jordan shear

The exact alternative to a blanket non-normality claim is that the equal-
diagonal upper Jordan block is normal iff its shear vanishes. Consequently a
normal matrix can equal this block only at zero shear. This is a finite
matrix statement and makes no claim about a braid word without a proved
identification with the block.
-/

#print axioms InfoGeometry.Canonical.upperJordan_not_normal
#print axioms InfoGeometry.Canonical.upperJordan_normal_iff_shear_zero
#print axioms InfoGeometry.Canonical.normal_ne_nontrivial_hadjiivanov
#print axioms InfoGeometry.Canonical.equality_implies_zero_hadjiivanov_shear
