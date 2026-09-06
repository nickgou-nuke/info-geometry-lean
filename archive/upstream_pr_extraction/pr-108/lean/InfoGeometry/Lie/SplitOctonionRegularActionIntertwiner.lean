import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

/-!
# Split-octonion automorphism and derivation action on regular operators

The native split-octonion carrier is nonassociative, while its linear
endomorphism algebra is associative.  Left and right regular multiplication
therefore provide the theorem-safe operator lift.

This file proves both levels of covariance:

* a split-octonion automorphism conjugates `L_x` and `R_x` to the regular
  operators labelled by the transformed carrier element;
* a genuine split-octonion derivation satisfies
  `[D,L_x] = L_(D x)` and `[D,R_x] = R_(D x)`.

No claim is made that the regular representation is multiplicative; its
failure to be multiplicative is the already-owned associator defect.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionRegularActionIntertwiner

open InfoGeometry.Canonical
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- Conjugation of a native Zorn endomorphism by a split-octonion
automorphism. -/
def conjugateEnd
    (φ : RealSplitOctonionAut) (T : EndCZ) : EndCZ :=
  (φ : SplitOctonionAutCandidate ℝ).toLinearMap.comp
    (T.comp (φ : SplitOctonionAutCandidate ℝ).symm.toLinearMap)

@[simp] theorem conjugateEnd_apply
    (φ : RealSplitOctonionAut) (T : EndCZ) (x : CZ) :
    conjugateEnd φ T x =
      (φ : SplitOctonionAutCandidate ℝ)
        (T ((φ : SplitOctonionAutCandidate ℝ).symm x)) :=
  rfl

/-- Group-level covariance of native left-regular multiplication. -/
theorem automorphism_conjugates_leftRegular
    (φ : RealSplitOctonionAut) (x : CZ) :
    conjugateEnd φ
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x) =
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        ((φ : SplitOctonionAutCandidate ℝ) x) := by
  apply LinearMap.ext
  intro y
  change
    (φ : SplitOctonionAutCandidate ℝ)
        (x * (φ : SplitOctonionAutCandidate ℝ).symm y) =
      (φ : SplitOctonionAutCandidate ℝ) x * y
  rw [RealSplitOctonionAut.preserves_mul,
    LinearEquiv.apply_symm_apply]

/-- Group-level covariance of native right-regular multiplication. -/
theorem automorphism_conjugates_rightRegular
    (φ : RealSplitOctonionAut) (x : CZ) :
    conjugateEnd φ
        (InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular x) =
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        ((φ : SplitOctonionAutCandidate ℝ) x) := by
  apply LinearMap.ext
  intro y
  change
    (φ : SplitOctonionAutCandidate ℝ)
        ((φ : SplitOctonionAutCandidate ℝ).symm y * x) =
      y * (φ : SplitOctonionAutCandidate ℝ) x
  rw [RealSplitOctonionAut.preserves_mul,
    LinearEquiv.apply_symm_apply]

/-- Infinitesimal covariance of native left-regular multiplication. -/
theorem derivation_commutator_leftRegular
    (D : EndCZ) (hD : IsDerivation D) (x : CZ) :
    ⁅D,
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x⁆ =
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (D x) :=
  InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.derivation_lie_leftRegular
    D hD x

/-- Infinitesimal covariance of native right-regular multiplication. -/
theorem derivation_commutator_rightRegular
    (D : EndCZ) (hD : IsDerivation D) (x : CZ) :
    ⁅D,
        InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular x⁆ =
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (D x) := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro y
  change D (y * x) - D y * x = y * D x
  rw [hD y x]
  abel

/-- Complete regular-action covariance packet for one automorphism and one
infinitesimal derivation. -/
theorem regularAction_covariance_packet
    (φ : RealSplitOctonionAut)
    (D : EndCZ) (hD : IsDerivation D) (x : CZ) :
    conjugateEnd φ
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x) =
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        ((φ : SplitOctonionAutCandidate ℝ) x) ∧
    conjugateEnd φ
        (InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular x) =
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        ((φ : SplitOctonionAutCandidate ℝ) x) ∧
    ⁅D,
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x⁆ =
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (D x) ∧
    ⁅D,
        InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular x⁆ =
      InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.rightRegular
        (D x) := by
  exact ⟨automorphism_conjugates_leftRegular φ x,
    automorphism_conjugates_rightRegular φ x,
    derivation_commutator_leftRegular D hD x,
    derivation_commutator_rightRegular D hD x⟩

end InfoGeometry.Lie.SplitOctonionRegularActionIntertwiner
