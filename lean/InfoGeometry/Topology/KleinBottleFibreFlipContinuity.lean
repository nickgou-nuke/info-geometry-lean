/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleCanonicalCarrier

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCanonicalCarrier

open KleinBrillouinBase
open InfoGeometry.Topology.CompactMappingTorus

theorem canonicalFibreFlip_continuous :
    Continuous (canonicalFibreFlip : CanonicalKleinBottle → CanonicalKleinBottle) := by
  change Continuous (fibreFlipMap : CanonicalKleinBottle → CanonicalKleinBottle)
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (continuous_fst.prodMk (continuous_neg.comp continuous_snd))

end InfoGeometry.Topology.KleinBottleCanonicalCarrier

end noncomputable section
