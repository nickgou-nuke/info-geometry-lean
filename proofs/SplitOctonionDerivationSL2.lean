import proofs.SplitOctonionInnerDerivation
import proofs.SplitOctonionSL2MatrixBridge
import proofs.SplitOctonionNilpotentExp

open SplitOctonion
open SplitOctonionSL2MatrixBridge
open SplitOctonionNilpotentExp
open SplitOctonionInnerDerivation
open SplitOctonionDerivationSpace

namespace SplitOctonionDerivationSL2

-- The associative slice gives us E, F, H.
-- We want to construct derivations out of them.

-- eAlphaBase, fAlphaBase, hAlphaBase
def hAlphaBase : SplitOct := H
def eAlphaBase : SplitOct := E
def fAlphaBase : SplitOct := F

/-- H_alpha inner derivation -/
noncomputable def H_alpha : OctDerivation := mkInnerDeriv (2 • eAlphaBase) (-2 • fAlphaBase)

/-- E_alpha inner derivation -/
noncomputable def E_alpha : OctDerivation := mkInnerDeriv hAlphaBase eAlphaBase

/-- F_alpha inner derivation -/
noncomputable def F_alpha : OctDerivation := mkInnerDeriv hAlphaBase fAlphaBase

-- Instead of proving the identities as raw operators, we will prove them in G2Chevalley as Lie bracket identities!
-- But first we need to make sure that the raw commutators work.
theorem alpha_sl2_HE :
  ⁅H_alpha, E_alpha⁆ = (2 : ℝ) • E_alpha := by
  ext z
  simp [H_alpha, E_alpha, mkInnerDeriv, Bracket.bracket, innerDeriv, associator, bracket, hAlphaBase, eAlphaBase, fAlphaBase, H, E, F, u, ell, smul_def, add_def, sub_def, mul_def, star, zero_def, neg_def]
  -- We just need the ring tactic to evaluate this on each component of z.
  sorry

theorem alpha_sl2_HF :
  ⁅H_alpha, F_alpha⁆ = (-2 : ℝ) • F_alpha := by
  ext z
  simp [H_alpha, F_alpha, mkInnerDeriv, Bracket.bracket, innerDeriv, associator, bracket, hAlphaBase, eAlphaBase, fAlphaBase, H, E, F, u, ell, smul_def, add_def, sub_def, mul_def, star, zero_def, neg_def]
  sorry

theorem alpha_sl2_EF :
  ⁅E_alpha, F_alpha⁆ = H_alpha := by
  ext z
  simp [H_alpha, E_alpha, F_alpha, mkInnerDeriv, Bracket.bracket, innerDeriv, associator, bracket, hAlphaBase, eAlphaBase, fAlphaBase, H, E, F, u, ell, smul_def, add_def, sub_def, mul_def, star, zero_def, neg_def]
  sorry

end SplitOctonionDerivationSL2
