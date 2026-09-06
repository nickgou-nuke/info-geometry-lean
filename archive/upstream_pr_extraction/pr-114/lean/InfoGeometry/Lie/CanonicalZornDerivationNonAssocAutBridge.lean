import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
import InfoGeometry.Lie.BaezG2SplitOctonion

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationNonAssocAutBridge

open InfoGeometry.Canonical
open InfoGeometry.Lie.BaezG2SplitOctonion
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge

/-!
# Native bridge from the canonical Zorn automorphism lane

The canonical Zorn exponential and the nonassociative automorphism surface use
the same carrier, but package the same preservation laws in different native
interfaces.  This file only transports those existing laws; it introduces no
new exponential construction.
-/

/-- Repackage a native real split-octonion automorphism as a nonassociative
automorphism on the definitionally identical split-Cayley carrier. -/
def realSplitOctonionAutToNonAssocAut
    (φ : RealSplitOctonionAut) : SplitCayleyG2Aut where
  toLinearEquiv := φ.1
  map_one' := φ.2.1
  map_mul' := φ.2.2

@[simp]
theorem realSplitOctonionAutToNonAssocAut_apply
    (φ : RealSplitOctonionAut) (x : SplitCayley) :
    realSplitOctonionAutToNonAssocAut φ x = φ.1 x :=
  rfl

/-- Transport a canonical Zorn derivation into the generic nonassociative
derivation subtype. -/
def canonicalToSplitCayleyG2Derivation
    (D : canonicalZornDerivations) : SplitCayleyG2Derivation :=
  ⟨D.1, D.2⟩

@[simp]
theorem canonicalToSplitCayleyG2Derivation_apply
    (D : canonicalZornDerivations) (x : SplitCayley) :
    (canonicalToSplitCayleyG2Derivation D).1 x = D.1 x :=
  rfl

/-- The already-proved canonical Zorn exponential, read through the generic
nonassociative automorphism interface. -/
def canonicalZornExpNonAssocAut
    (D : canonicalZornDerivations) (t : ℝ) : SplitCayleyG2Aut :=
  realSplitOctonionAutToNonAssocAut (zornFlowRealAut D t)

@[simp]
theorem canonicalZornExpNonAssocAut_apply
    (D : canonicalZornDerivations) (t : ℝ) (x : SplitCayley) :
    canonicalZornExpNonAssocAut D t x =
      InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv
        D.1 t x :=
  rfl

theorem canonicalZornExpNonAssocAut_map_one
    (D : canonicalZornDerivations) (t : ℝ) :
    canonicalZornExpNonAssocAut D t (1 : SplitCayley) = 1 := by
  exact (zornFlowRealAut D t).preserves_one

theorem canonicalZornExpNonAssocAut_map_mul
    (D : canonicalZornDerivations) (t : ℝ) (x y : SplitCayley) :
    canonicalZornExpNonAssocAut D t (x * y) =
      canonicalZornExpNonAssocAut D t x *
        canonicalZornExpNonAssocAut D t y := by
  exact (zornFlowRealAut D t).preserves_mul x y

end InfoGeometry.Lie.CanonicalZornDerivationNonAssocAutBridge
