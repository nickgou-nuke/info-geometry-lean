import proofs.SplitOctonionInnerDerivation
import proofs.SplitOctonionSL2MatrixBridge
import proofs.SplitOctonionNilpotentExp

open SplitOctonion
open SplitOctonionSL2MatrixBridge
open SplitOctonionNilpotentExp
open SplitOctonionInnerDerivation

noncomputable section

namespace SplitOctonionDerivationSL2

/-!
The `sl₂` packet is normalized from the native inner derivations.  The
operator identities below are the part that follows abstractly from the
Leibniz rule; numerical root relations require separate slice-action lemmas.
-/

def hAlphaBase : SplitOct := H
def eAlphaBase : SplitOct := E
def fAlphaBase : SplitOct := F

noncomputable def H_alpha : OctDerivation :=
  mkInnerDeriv eAlphaBase fAlphaBase

noncomputable def E_alpha : OctDerivation :=
  (1 / 2 : ℝ) • mkInnerDeriv hAlphaBase eAlphaBase

noncomputable def F_alpha : OctDerivation :=
  (-1 / 2 : ℝ) • mkInnerDeriv hAlphaBase fAlphaBase

theorem inner_derivation_bracket_formula (x y u v : SplitOct) :
    ⁅mkInnerDeriv x y, mkInnerDeriv u v⁆ =
      mkInnerDeriv (innerDeriv x y u) v +
        mkInnerDeriv u (innerDeriv x y v) := by
  exact bracket_mkInnerDeriv_mkInnerDeriv x y u v

end SplitOctonionDerivationSL2
