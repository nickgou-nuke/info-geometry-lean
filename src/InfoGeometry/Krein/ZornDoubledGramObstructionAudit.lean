/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Krein.ZornDoubledGramObstruction

/-!
# Source audit: Zorn carrier norm does not match the doubled Krein form

The proved replacement records the actual eight-coordinate signed Gram form
under the carrier map. The explicit `uPlus` witness has Krein self-pairing one
but native split norm zero, so the map is not an isometry. No norm
identification between these distinct carriers is asserted.
-/

#print axioms InfoGeometry.Krein.MajoranaBdGSheetBridge.nambuDoubledEquiv_kreinForm
#print axioms InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.zornToDoubleKrein_kreinForm
#print axioms InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.zornToDoubleKrein_uPlus_krein_self
#print axioms InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.native_uPlus_norm_zero
#print axioms InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.zornToDoubleKrein_not_norm_isometry
