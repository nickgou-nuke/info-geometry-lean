import InfoGeometry.Algebra.SplitCayleyF2NormCarrierAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

def CayleyIsotropic (x : Cayley) : Prop := norm x = 0

theorem cayleyIsotropic_iff_nativeIsotropic (x : Cayley) :
    CayleyIsotropic x ↔ Isotropic (cayleyToSplitOctF2 x) := by
  have hz (a : ZMod 2) : a = 0 ↔ zModToBool a = false := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      have hne : a ≠ 1 := by simpa [zModToBool] using h
      apply ZMod.val_injective 2
      have hlt : a.val < 2 := ZMod.val_lt a
      have hval_ne : a.val ≠ 1 := by
        intro hv
        apply hne
        apply ZMod.val_injective 2
        simpa only [ZMod.val_one 2] using hv
      have hzero : a.val = 0 := by omega
      simpa only [ZMod.val_zero] using hzero
  unfold CayleyIsotropic Isotropic
  rw [hz, cayley_norm_bool_readback]

end InfoGeometry.Algebra.SplitCayleyF2
