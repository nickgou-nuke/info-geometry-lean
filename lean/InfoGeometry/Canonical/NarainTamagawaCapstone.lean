/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Adelic.NarainTamagawa
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.NarainTamagawaCapstone

open InfoGeometry.Adelic.NarainTamagawa

/-- Canonical projection of the normalized `SL₂` Tamagawa-volume owner law. -/
theorem capstone_narain_tamagawa_synthesis :
    tamagawaVolumeSL2 = 1 :=
  tamagawa_volume_is_one

end InfoGeometry.Canonical.NarainTamagawaCapstone
