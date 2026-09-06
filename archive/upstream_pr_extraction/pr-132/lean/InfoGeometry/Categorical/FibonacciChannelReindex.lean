import InfoGeometry.Categorical.FibonacciPentagonChannelCarrier

/-!
# Canonical reindexing between parenthesized Fibonacci channel spaces

All parenthesized four-`τ` objects have the same total channel count.  The
existing carrier equivalences to `Basis6` therefore give a canonical linear
reindexing between their channel-function spaces.  This is a basis transport
lemma only; it does not choose a physical fusion-tree basis.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonChannelCarrier

open InfoGeometry.Categorical.FibonacciPentagonPathCarrier

noncomputable def parenthesizedChannelReindex (v w : PentagonVertex) :
    ChannelFunctions v ≃ₗ[ℂ] ChannelFunctions w :=
  (parenthesizedChannelCarrierEquiv v).trans
    (parenthesizedChannelCarrierEquiv w).symm

@[simp] theorem parenthesizedChannelReindex_apply
    (v w : PentagonVertex) (x : ChannelFunctions v) (j : ChannelIndex w) :
    parenthesizedChannelReindex v w x j =
      (parenthesizedChannelCarrierEquiv v x)
        (parenthesizedChannelEquiv w j) := by
  rfl

@[simp] theorem parenthesizedChannelReindex_refl
    (v : PentagonVertex) :
    parenthesizedChannelReindex v v = LinearEquiv.refl ℂ (ChannelFunctions v) := by
  ext x j
  simp [parenthesizedChannelReindex]

@[simp] theorem parenthesizedChannelReindex_trans
    (u v w : PentagonVertex) :
    (parenthesizedChannelReindex u v).trans
        (parenthesizedChannelReindex v w) =
      parenthesizedChannelReindex u w := by
  ext x j
  simp [parenthesizedChannelReindex]

@[simp] theorem parenthesizedChannelReindex_symm
    (v w : PentagonVertex) :
    (parenthesizedChannelReindex v w).symm =
      parenthesizedChannelReindex w v := by
  ext x j
  simp [parenthesizedChannelReindex]

end InfoGeometry.Categorical.FibonacciPentagonChannelCarrier
