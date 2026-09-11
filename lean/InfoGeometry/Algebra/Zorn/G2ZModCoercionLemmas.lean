import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2ZModCoercionLemmas

theorem natCast_sub_mod_six (k : ZMod 6) :
    (((6 - k.val) % 6 : ℕ) : ZMod 6) = -k := by
  apply ZMod.val_injective 6
  simp [ZMod.neg_val']

end InfoGeometry.Algebra.Zorn.G2ZModCoercionLemmas
