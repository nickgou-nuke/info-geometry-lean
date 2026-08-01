import InfoGeometry.Lie.G2FromSplitOctonions

/-!
# Native real split-octonion derivation surface

The concrete Zorn product, its composition norm, and the canonical derivation
Lie algebra are owned by the algebra and Lie modules imported below.  This
module only names those native results and keeps the finite `G₂(2)` and real
split `G₂` classification lanes distinct.

No computer-algebra status flags are stored here.  In particular, root-system
counts, `Dmodules` output, and a global automorphism-group equivalence remain
separate obligations until an actual Lean owner supplies them.
-/

namespace InfoGeometry.Lie.RealSplitOctonionG2Classification

open InfoGeometry.Lie.G2FromSplitOctonions
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-! ## Native composition and derivation theorems -/

theorem split_octonion_norm_composition (X Y : SplitOct) :
    normZ (mulZ X Y) = normZ X * normZ Y :=
  normZ_mul X Y

theorem split_octonion_derivation_bracket_closed
    {D₁ D₂ : DerivSpace}
    (hD1 : IsDeriv D₁) (hD2 : IsDeriv D₂) :
    IsDeriv (bracket D₁ D₂) :=
  bracket_closed hD1 hD2

theorem canonical_split_octonion_derivation_finrank :
    Module.finrank ℝ
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 :=
  canonicalDerivations_finrank

theorem standard_split_octonion_derivations_span :
    InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivationSpan = ⊤ :=
  canonicalDerivations_span_standard

theorem canonical_rotation_is_derivation : IsDeriv D01 :=
  D01_deriv

end InfoGeometry.Lie.RealSplitOctonionG2Classification
