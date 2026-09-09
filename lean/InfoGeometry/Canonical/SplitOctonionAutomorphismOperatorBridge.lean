import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-! Automorphisms transport regular multiplication operators. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge

open InfoGeometry.Canonical
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

abbrev Carrier := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCarrier := Module.End ℝ Carrier

noncomputable def leftRegular (x : Carrier) : EndCarrier :=
  leftMultiplication x

def conjugateLeftRegular (φ : RealSplitOctonionAut) (x : Carrier) : EndCarrier :=
  φ.1.toLinearMap * leftRegular x * φ.1.symm.toLinearMap

theorem conjugateLeftRegular_apply (φ : RealSplitOctonionAut) (x y : Carrier) :
    conjugateLeftRegular φ x y = φ.1 (x * φ.1.symm y) := by
  simp [conjugateLeftRegular, leftRegular, leftMultiplication_apply]

theorem conjugateLeftRegular_eq_leftRegular (φ : RealSplitOctonionAut) (x : Carrier) :
    conjugateLeftRegular φ x = leftRegular (φ.1 x) := by
  apply LinearMap.ext
  intro y
  rw [conjugateLeftRegular_apply, φ.preserves_mul]
  simp [leftRegular, leftMultiplication_apply]

noncomputable def rightRegular (x : Carrier) : EndCarrier :=
  rightMultiplication x

def conjugateRightRegular (φ : RealSplitOctonionAut) (x : Carrier) : EndCarrier :=
  φ.1.toLinearMap * rightRegular x * φ.1.symm.toLinearMap

theorem conjugateRightRegular_apply (φ : RealSplitOctonionAut) (x y : Carrier) :
    conjugateRightRegular φ x y = φ.1 (φ.1.symm y * x) := by
  simp [conjugateRightRegular, rightRegular, rightMultiplication_apply]

theorem conjugateRightRegular_eq_rightRegular (φ : RealSplitOctonionAut) (x : Carrier) :
    conjugateRightRegular φ x = rightRegular (φ.1 x) := by
  apply LinearMap.ext
  intro y
  rw [conjugateRightRegular_apply, φ.preserves_mul]
  simp [rightRegular, rightMultiplication_apply]

/-! The regular representation is equivariant on both sides at once.  This is
the canonical operator-level soldering statement for a split-octonion
automorphism; it does not impose associativity on the source product. -/
theorem conjugateRegular_packet (φ : RealSplitOctonionAut) (x : Carrier) :
    conjugateLeftRegular φ x = leftRegular (φ.1 x) ∧
      conjugateRightRegular φ x = rightRegular (φ.1 x) := by
  exact ⟨conjugateLeftRegular_eq_leftRegular φ x,
    conjugateRightRegular_eq_rightRegular φ x⟩

/-! The left-regular companion.  Both identities use only the Leibniz rule;
the nonassociative product is never replaced by operator multiplication. -/
theorem derivation_lie_leftRegular
    (D : EndCarrier) (hD : IsDerivation D) (x : Carrier) :
    ⁅D, leftRegular x⁆ = leftRegular (D x) := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro y
  change D (x * y) - x * D y = D x * y
  rw [hD x y]
  abel

/-! A genuine split-octonion derivation acts on right-regular multiplication
by the corresponding transported commutator identity.  This is the right
regular companion to the left-regular intertwiner and uses only Leibniz. -/
theorem derivation_lie_rightRegular
    (D : EndCarrier) (hD : IsDerivation D) (x : Carrier) :
    ⁅D, rightRegular x⁆ = rightRegular (D x) := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro y
  change D (y * x) - D y * x = y * D x
  rw [hD y x]
  abel

/-! Infinitesimal equivariance of the complete regular representation. -/
theorem derivation_lie_regular_packet
    (D : EndCarrier) (hD : IsDerivation D) (x : Carrier) :
    ⁅D, leftRegular x⁆ = leftRegular (D x) ∧
      ⁅D, rightRegular x⁆ = rightRegular (D x) := by
  exact ⟨derivation_lie_leftRegular D hD x,
    derivation_lie_rightRegular D hD x⟩

end InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge
end noncomputable section
