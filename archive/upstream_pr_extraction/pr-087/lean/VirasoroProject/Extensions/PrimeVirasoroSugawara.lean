import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

noncomputable section

namespace VirasoroProject.Extensions.PrimeVirasoroSugawara

open InfoGeometry.Canonical.SplitCliffordInfiniteCurrent
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

theorem level_one_commutator
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :
    ⁅Jinf 𝕜 1, Jinf 𝕜 (-1)⁆ =
      (1 : 𝕜) • Kinf 𝕜 := by
  exact canonicalInfiniteCurrent_lie_one_neg_one (𝕜 := 𝕜)

theorem level_one_commutator_reverse
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :
    ⁅Jinf 𝕜 (-1), Jinf 𝕜 1⁆ =
      ((-1 : Int) : 𝕜) • Kinf 𝕜 := by
  exact canonicalInfiniteCurrent_lie_neg_one_one (𝕜 := 𝕜)

end VirasoroProject.Extensions.PrimeVirasoroSugawara
