import InfoGeometry.Algebra.SplitCayleyF2IsotropyAlignment
import InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates

theorem cayleyIsotropic_add_iff_nativeIncident
    (x y : Cayley)
    (hx : CayleyIsotropic x)
    (hy : CayleyIsotropic y) :
    CayleyIsotropic (add x y) ↔
      nativeIncident (cayleyToSplitOctF2 x) (cayleyToSplitOctF2 y) := by
  have hx' : Isotropic (cayleyToSplitOctF2 x) :=
    (cayleyIsotropic_iff_nativeIsotropic x).mp hx
  have hy' : Isotropic (cayleyToSplitOctF2 y) :=
    (cayleyIsotropic_iff_nativeIsotropic y).mp hy
  rw [cayleyIsotropic_iff_nativeIsotropic]
  rw [cayleySplitOctF2Equiv_add]
  exact (nativePolar_isotropic_sum_iff
    (cayleyToSplitOctF2 x) (cayleyToSplitOctF2 y) hx' hy').symm

end InfoGeometry.Algebra.SplitCayleyF2
