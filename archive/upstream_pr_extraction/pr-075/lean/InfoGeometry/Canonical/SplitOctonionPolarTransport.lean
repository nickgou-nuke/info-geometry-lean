import InfoGeometry.Canonical.SplitOctonionQuaternionPolar

/-!
# Transport of split-octonion polar decompositions

The quaternion-pair polar theorem is proved on `SplitOctonion`.  This file
records the exact hypothesis needed to transport its factorization to another
linear carrier: the chosen linear equivalence must also preserve the native
product.  No associativity or unproved CanonicalZorn identification is
assumed.
-/

noncomputable section

namespace SplitOctonion

theorem polar_decomposition_transport
    {B : Type*} [Mul B]
    (T : SplitOctonion ≃ B)
    (hT : ∀ A C : SplitOctonion, T (A * C) = T A * T C)
    (X : SplitOctonion) (h : isHyperbolic X) (hb : X.b ≠ 0) :
    T X =
      T ⟨polarRho X h • polarU X (a_ne_zero_of_isHyperbolic X h), 0⟩ *
        T (expHyperbolic 1 (polarEta X h)
          (J_g (polarG X (a_ne_zero_of_isHyperbolic X h) hb))) := by
  have hX := congrArg T (polar_decomposition X h hb)
  simpa only [hT] using hX

end SplitOctonion
