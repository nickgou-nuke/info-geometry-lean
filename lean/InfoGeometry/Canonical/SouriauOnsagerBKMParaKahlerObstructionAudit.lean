/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.SouriauOnsagerBKMParaKahlerObstruction

/-!
# Source audit: BKM real-form anti-invariance obstruction

The owner theorem rules out a globally anti-invariant positive BKM form on
any nonzero input. Its proof uses strict positivity on `A` and `J A` and the
anti-invariance equation at `(A,A)`. This module records the kernel axiom
surface for that precise owner declaration.
-/

#print axioms SouriauOnsagerBKM.FaithfulDensityOperator.bkmRealBilinForm_no_antiInvariant
