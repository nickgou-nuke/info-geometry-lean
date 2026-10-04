import InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

/-!
# Isotropic points in a native line set

This is the first carrier-alignment edge.  It does not identify native and
intrinsic lines; it only proves that each element of a valid native line set
has the isotropic-point subtype required by the intrinsic carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineSetIsotropicBridge

open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeCandidateSymmetry
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

theorem nativeLineSetAt_mem_isotropicPoint
    (y : G2ParabolicLineCarrier.OctImF2)
    (hy : nativeCandidateAt nativeBasePoint y)
    {v : G2ParabolicLineCarrier.OctImF2}
    (hv : v ∈ nativeLineSetAt nativeBasePoint y) :
    ∃ p : OctImIsotropicPoint, p.1 = v := by
  have hv' : v = nativeBasePoint ∨ v = y ∨
      v = nativeBasePoint + y := by
    simpa only [nativeLineSetAt, Finset.mem_insert, Finset.mem_singleton] using hv
  rcases hv' with h | h | h
  · exact ⟨nativeBaseIsotropicPoint, h.symm⟩
  · subst v
    exact ⟨⟨y, nativeCandidateAt_isotropic y hy, hy.1⟩, rfl⟩
  · exact ⟨⟨nativeBasePoint + y,
      nativeCandidateAt_sum_isotropic y hy,
      by native_decide +revert⟩, h.symm⟩

end InfoGeometry.Algebra.Zorn.G2NativeLineSetIsotropicBridge
