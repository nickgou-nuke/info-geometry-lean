import InfoGeometry.Algebra.Zorn.G2NativeCertificateTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CASNativePointAction

/-!
# Relabeling the two 63-point enumerations

`casPointEnum` and `nativePointEnum` enumerate the same isotropic-point
carrier.  This file records the resulting permutation conjugation only; it
does not assert that the exported incidence table is preserved.
-/

namespace InfoGeometry.Algebra.Zorn.G2PointEnumRelabeling

open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
open InfoGeometry.Algebra.Zorn.G2NativeCertificateTransport
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def casToNative : Equiv.Perm (Fin 63) :=
  casPointEnum.trans nativePointEnum.symm

theorem casToNative_apply (i : Fin 63) :
    casToNative i = nativePointEnum.symm (casPointEnum i) := rfl

theorem casToNative_conjugates_pc (k : Fin 6) (i : Fin 63) :
    casToNative (casPointPerm ⟨k, by omega⟩ i) =
      nativePointEnum.symm
        (octImPointPerm (pcGenerator k) (casPointEnum i)) := by
  rw [casToNative_apply]
  rw [casPointEnum_pc_intertwines]

end InfoGeometry.Algebra.Zorn.G2PointEnumRelabeling
