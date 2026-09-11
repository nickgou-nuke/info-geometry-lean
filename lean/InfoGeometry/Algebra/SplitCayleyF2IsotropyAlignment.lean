import InfoGeometry.Algebra.SplitCayleyF2NormCarrierAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

def CayleyIsotropic (x : Cayley) : Prop := norm x = 0

theorem cayleyIsotropic_iff_nativeIsotropic (x : Cayley) :
    CayleyIsotropic x ↔ Isotropic (cayleyToSplitOctF2 x) := by
  have hz (a : ZMod 2) : a = 0 ↔ zModToBool a = false := by
    fin_cases a <;> simp [zModToBool]
  unfold CayleyIsotropic Isotropic
  rw [hz, cayley_norm_bool_readback]

end InfoGeometry.Algebra.SplitCayleyF2
