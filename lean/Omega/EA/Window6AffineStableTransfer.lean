import Omega.Folding.FiberRing

namespace Omega.EA

open Omega

noncomputable section

/-- Paper label: `lem:window6-affine-stable-transfer`. -/
theorem paper_window6_affine_stable_transfer (m a b : ℕ) :
    ∀ lhs rhs : X.AffineMagmaTerm (Fin 6),
      X.AffineMagmaTerm.SatisfiesX m (X.ofNat m a) (X.ofNat m b) lhs rhs ↔
        X.AffineMagmaTerm.SatisfiesZ m
          (X.stableValueRingEquiv m (X.ofNat m a))
          (X.stableValueRingEquiv m (X.ofNat m b)) lhs rhs := by
  intro lhs rhs
  exact X.stableValueRingEquiv_preserves_magma_satisfaction m
    (X.ofNat m a) (X.ofNat m b) lhs rhs

end

end Omega.EA
