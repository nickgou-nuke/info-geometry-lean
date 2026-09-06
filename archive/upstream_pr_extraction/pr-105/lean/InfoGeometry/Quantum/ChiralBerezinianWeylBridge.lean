import InfoGeometry.Canonical.BerezinianTrace

/-!
# Finite diagonal Berezinian readout of two Weyl channels

This file consumes the existing diagonal Berezinian owner.  It adds only the
two-sheet Weyl interpretation: the ordinary paired trace sees a sum, while
the Berezinian sees a difference.
-/

namespace InfoGeometry.Quantum.ChiralBerezinianWeylBridge

open InfoGeometry.Canonical.BerezinianTrace

theorem berezinian_scalar_weyl
    (n : ℕ) (kplus kminus : ℝ) :
     berezinian
           (Real.exp ((n : ℝ) * kplus))
           (Real.exp ((n : ℝ) * kminus))
           (Real.exp_ne_zero _) =
         Real.exp ((n : ℝ) * (kplus - kminus)) := by
     rw [show (n : ℝ) * (kplus - kminus) =
       (n : ℝ) * kplus - (n : ℝ) * kminus by ring]
     simpa [supertrace] using
       (ber_exp_eq_exp_str
         ((n : ℝ) * kplus) 0 ((n : ℝ) * kminus) 0)

theorem berezinian_common_scalar_weyl
    (n : ℕ) (k : ℝ) :
    berezinian
        (Real.exp ((n : ℝ) * k))
        (Real.exp ((n : ℝ) * k))
        (Real.exp_ne_zero _) = 1 := by
  exact ber_eq_one _ (Real.exp_ne_zero _)

end InfoGeometry.Quantum.ChiralBerezinianWeylBridge
