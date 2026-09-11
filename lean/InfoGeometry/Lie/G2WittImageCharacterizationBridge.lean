import InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Intrinsic Leibniz selector for the transported `G₂` Witt image

This owner does not characterize the image by a dimension count.  Instead it
transports the native Zorn Leibniz predicate through the canonical coordinate
equivalence and proves the resulting existential image statement.
-/

noncomputable section

namespace InfoGeometry.Lie.G2WittImageCharacterizationBridge

open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge

abbrev CanonicalZorn :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn
abbrev Derivation := SplitOctonionDerivationWittOrthogonalBridge.Derivation
abbrev Coord8 := SplitOctonionWittPairingTransportBridge.Coord8

def transportedAction (T : Coord8 →ₗ[ℝ] Coord8) :
    CanonicalZorn →ₗ[ℝ] CanonicalZorn :=
  (neutralCanonicalToCoord.symm).toLinearMap.comp
    (T.comp neutralCanonicalToCoord.toLinearMap)

/-- The transported Leibniz selector on the coordinate carrier. -/
def IsTransportedLeibniz (T : Coord8 →ₗ[ℝ] Coord8) : Prop :=
  ∀ X Y : CanonicalZorn,
    transportedAction T (X * Y) =
      transportedAction T X * Y + X * transportedAction T Y

/-! The coordinate invariant-form selector.  It is stated using the same
neutral pairing that defines the canonical Witt matrix, so it does not
introduce a second matrix convention. -/

def IsCoordinateWittSkew (T : Coord8 →ₗ[ℝ] Coord8) : Prop :=
  ∀ x y,
    neutralEtaPairing (T x) y + neutralEtaPairing x (T y) = 0

def transportedDerivationOf (T : Coord8 →ₗ[ℝ] Coord8)
    (hT : IsTransportedLeibniz T) : Derivation :=
  ⟨transportedAction T, hT⟩

theorem transportedAction_transport (D : Derivation) :
    transportedAction (transportedDerivation D) = D.1 := by
  apply LinearMap.ext
  intro X
  apply neutralCanonicalToCoord.injective
  simp [transportedAction, transportedDerivation]

theorem transportedLeibniz_of_derivation (D : Derivation) :
    IsTransportedLeibniz (transportedDerivation D) := by
  intro X Y
  simpa [transportedAction_transport D] using D.property X Y

theorem transportedDerivation_coordinate_witt_skew (D : Derivation) :
    IsCoordinateWittSkew (transportedDerivation D) := by
  intro x y
  have h := neutral_canonical_derivation_eta_skew D
    (neutralCanonicalToCoord.symm x) (neutralCanonicalToCoord.symm y)
  simpa [IsCoordinateWittSkew, transportedDerivation] using h

theorem transportedDerivation_eq_of_action
    (T : Coord8 →ₗ[ℝ] Coord8) (hT : IsTransportedLeibniz T) :
    transportedDerivation (transportedDerivationOf T hT) = T := by
  apply LinearMap.ext
  intro z
  simp [transportedDerivation, transportedDerivationOf, transportedAction]

theorem transported_leibniz_iff_in_derivation_image
    (T : Coord8 →ₗ[ℝ] Coord8) :
    IsTransportedLeibniz T ↔
      ∃ D : Derivation, transportedDerivation D = T := by
  constructor
  · intro hT
    exact ⟨transportedDerivationOf T hT,
      transportedDerivation_eq_of_action T hT⟩
  · rintro ⟨D, rfl⟩
    exact transportedLeibniz_of_derivation D

theorem transported_image_iff_leibniz_and_witt
    (T : Coord8 →ₗ[ℝ] Coord8) :
    (∃ D : Derivation, transportedDerivation D = T) ↔
      IsTransportedLeibniz T ∧ IsCoordinateWittSkew T := by
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨transportedLeibniz_of_derivation D,
      transportedDerivation_coordinate_witt_skew D⟩
  · rintro ⟨hT, _hW⟩
    exact (transported_leibniz_iff_in_derivation_image T).mp hT

theorem mem_transportedDerivationLieSubalgebra_iff
    (T : Module.End ℝ Coord8) :
    T ∈ (transportedDerivationLieHom.range :
      LieSubalgebra ℝ (Module.End ℝ Coord8)) ↔
      IsTransportedLeibniz T := by
  rw [LieHom.mem_range]
  simpa [transportedDerivationLieHom_apply] using
    (transported_leibniz_iff_in_derivation_image T).symm

def IsG2WittBlock (M : WittBlockMatrix) : Prop :=
  ∃ D : Derivation, canonicalDerivationBlock D = M

theorem g2WittBlock_iff_transportedLeibniz
    (M : WittBlockMatrix) :
    IsG2WittBlock M ↔
      ∃ T : Coord8 →ₗ[ℝ] Coord8,
        ∃ hT : IsTransportedLeibniz T,
          canonicalDerivationBlock (transportedDerivationOf T hT) = M := by
  constructor
  · rintro ⟨D, rfl⟩
    let T := transportedDerivation D
    have hT : IsTransportedLeibniz T := transportedLeibniz_of_derivation D
    have hD : transportedDerivationOf T hT = D := by
      apply Subtype.ext
      exact transportedAction_transport D
    exact ⟨T, hT, by rw [hD]⟩
  · rintro ⟨T, hT, hM⟩
    exact ⟨transportedDerivationOf T hT, hM⟩

theorem g2WittBlock_iff_leibniz_and_witt
    (M : WittBlockMatrix) :
    IsG2WittBlock M ↔
      ∃ (T : Coord8 →ₗ[ℝ] Coord8)
        (hT : IsTransportedLeibniz T),
        IsCoordinateWittSkew T ∧
          canonicalDerivationBlock (transportedDerivationOf T hT) = M := by
  constructor
  · rintro ⟨D, rfl⟩
    let T := transportedDerivation D
    have hT : IsTransportedLeibniz T := transportedLeibniz_of_derivation D
    have hW : IsCoordinateWittSkew T := transportedDerivation_coordinate_witt_skew D
    have hD : transportedDerivationOf T hT = D := by
      apply Subtype.ext
      exact transportedAction_transport D
    exact ⟨T, hT, hW, by rw [hD]⟩
  · rintro ⟨T, hT, _hW, hM⟩
    exact ⟨transportedDerivationOf T hT, hM⟩

theorem g2WittBlock_isWittSkew {M : WittBlockMatrix}
    (hM : IsG2WittBlock M) : IsWittSkew M := by
  rcases hM with ⟨D, rfl⟩
  exact canonicalDerivationBlock_isWittSkew D

end InfoGeometry.Lie.G2WittImageCharacterizationBridge
