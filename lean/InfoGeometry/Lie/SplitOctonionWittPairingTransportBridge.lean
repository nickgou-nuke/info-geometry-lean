import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

/-!
# Explicit finite Witt pairing transport

The vector/covector carrier `V₊ × V₋` is linearly equivalent to the eight
coordinate functions used by the matrix-level Witt owner.  The symmetric
neutral pairing is written explicitly on both sides, giving a concrete
instance of the abstract `PairingTransport` socket.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge

open InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

abbrev WittCoord := VPlus × VMinus
abbrev Coord8 := Fin 8 → ℝ

def toCoord : WittCoord ≃ₗ[ℝ] Coord8 where
  toFun x i := if h : i.val < 4 then x.1 ⟨i.val, h⟩ else x.2 ⟨i.val - 4, by omega⟩
  invFun x := (fun i => x ⟨i.val, by omega⟩, fun i => x ⟨i.val + 4, by omega⟩)
  left_inv x := by
    rcases x with ⟨u, v⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  right_inv x := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    by_cases h : i.val < 4 <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i.val < 4 <;> simp [h]

def etaPairing (x y : Coord8) : ℝ :=
  (1 / 2 : ℝ) *
    (x 0 * y 4 + x 4 * y 0 -
      (x 1 * y 5 + x 5 * y 1 +
        (x 2 * y 6 + x 6 * y 2 +
          (x 3 * y 7 + x 7 * y 3))))

def nativeWittPairing (x y : WittCoord) : ℝ :=
  (1 / 2 : ℝ) *
    (wittPairing x.1 y.2 + wittPairing y.1 x.2)

theorem etaPairing_transport (x y : WittCoord) :
    nativeWittPairing x y = etaPairing (toCoord x) (toCoord y) := by
  rcases x with ⟨u, v⟩
  rcases y with ⟨u', v'⟩
  dsimp [nativeWittPairing, etaPairing, toCoord, wittPairing]
  ring

def explicitPairingTransport : PairingTransport WittCoord where
  toCoord := toCoord
  nativePairing := nativeWittPairing
  coordinatePairing := etaPairing
  pairing_transport := etaPairing_transport

theorem explicit_transport_skew
    (D : WittCoord →ₗ[ℝ] WittCoord)
    (hD : ∀ x y, nativeWittPairing (D x) y + nativeWittPairing x (D y) = 0) :
    ∀ x y, etaPairing (toCoord (D x)) (toCoord y) +
      etaPairing (toCoord x) (toCoord (D y)) = 0 := by
  exact transported_skew explicitPairingTransport D hD

/-! The same coordinate presentation can be attached directly to the canonical
Zorn carrier.  The factor `1/2` matches the symmetric Witt polarization with
the native trace pairing used by the derivation owner. -/

abbrev CanonicalZorn :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn

def canonicalToCoord : CanonicalZorn ≃ₗ[ℝ] Coord8 where
  toFun X i :=
    if i = 0 then X.a else if i = 1 then X.x 0 else if i = 2 then X.x 1 else
    if i = 3 then X.x 2 else if i = 4 then X.b else if i = 5 then X.y 0 else
    if i = 6 then X.y 1 else X.y 2
  invFun z :=
    { a := z 0, b := z 4, x := ![z 1, z 2, z 3], y := ![z 5, z 6, z 7] }
  left_inv X := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv z := by
    funext i
    fin_cases i <;> simp
  map_add' X Y := by
    funext i
    fin_cases i <;> rfl
  map_smul' r X := by
    funext i
    fin_cases i <;> rfl

/-! The three transverse signs are absorbed into the covector half to obtain
the neutral cross-pairing used by `etaW`. -/

def neutralize : Coord8 ≃ₗ[ℝ] Coord8 where
  toFun z i := if i.val < 5 then z i else -z i
  invFun z i := if i.val < 5 then z i else -z i
  left_inv z := by
    funext i
    by_cases h : i.val < 5 <;> simp [h]
  right_inv z := by
    funext i
    by_cases h : i.val < 5 <;> simp [h]
  map_add' x y := by
    funext i
    by_cases h : i.val < 5 <;> simp [h] <;> ring
  map_smul' r x := by
    funext i
    by_cases h : i.val < 5 <;> simp [h]

def neutralEtaPairing (x y : Coord8) : ℝ :=
  (1 / 2 : ℝ) *
    (x 0 * y 4 + x 4 * y 0 +
      (x 1 * y 5 + x 5 * y 1 +
        (x 2 * y 6 + x 6 * y 2 +
          (x 3 * y 7 + x 7 * y 3))))

theorem neutralEtaPairing_neutralize (x y : Coord8) :
    neutralEtaPairing (neutralize x) (neutralize y) = etaPairing x y := by
  dsimp [neutralEtaPairing, neutralize, etaPairing]
  ring

def neutralCanonicalToCoord : CanonicalZorn ≃ₗ[ℝ] Coord8 :=
  canonicalToCoord.trans neutralize

def canonicalCoordinatePairing (X Y : CanonicalZorn) : ℝ :=
  (1 / 2 : ℝ) *
    InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge.nativeCanonicalWittPairing X Y

theorem canonical_pairing_transport (X Y : CanonicalZorn) :
    canonicalCoordinatePairing X Y =
      etaPairing (canonicalToCoord X) (canonicalToCoord Y) := by
  dsimp [canonicalCoordinatePairing,
    InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge.nativeCanonicalWittPairing,
    InfoGeometry.Algebra.ZornVectorMatrix.trace,
    InfoGeometry.Algebra.ZornVectorMatrix.mul,
    InfoGeometry.Algebra.ZornVectorMatrix.conj,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVectorMatrix.neg,
    InfoGeometry.Algebra.ZornVectorMatrix.smul,
    InfoGeometry.Algebra.ZornVec3.dot,
    InfoGeometry.Algebra.ZornVec3.cross, canonicalToCoord, etaPairing]
  simp [Fin.sum_univ_three]
  ring

theorem neutral_canonical_pairing_transport (X Y : CanonicalZorn) :
    (1 / 2 : ℝ) *
        InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge.nativeCanonicalWittPairing X Y =
      neutralEtaPairing (neutralCanonicalToCoord X) (neutralCanonicalToCoord Y) := by
  rw [show neutralCanonicalToCoord X = neutralize (canonicalToCoord X) by rfl,
    show neutralCanonicalToCoord Y = neutralize (canonicalToCoord Y) by rfl,
    neutralEtaPairing_neutralize]
  exact canonical_pairing_transport X Y

def canonicalPairingTransport : PairingTransport CanonicalZorn where
  toCoord := canonicalToCoord
  nativePairing := canonicalCoordinatePairing
  coordinatePairing := etaPairing
  pairing_transport := canonical_pairing_transport

theorem canonical_derivation_eta_skew
    (D : InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge.Derivation)
    (X Y : CanonicalZorn) :
    etaPairing (canonicalToCoord (D.1 X)) (canonicalToCoord Y) +
      etaPairing (canonicalToCoord X) (canonicalToCoord (D.1 Y)) = 0 := by
  apply transported_skew canonicalPairingTransport D.1
  intro x y
  dsimp [canonicalPairingTransport, canonicalCoordinatePairing]
  calc
    (1 / 2 : ℝ) * nativeCanonicalWittPairing (D.1 x) y +
        (1 / 2 : ℝ) * nativeCanonicalWittPairing x (D.1 y) =
      (1 / 2 : ℝ) *
        (nativeCanonicalWittPairing (D.1 x) y +
          nativeCanonicalWittPairing x (D.1 y)) := by ring
    _ = 0 := by rw [InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge.derivation_native_witt_skew D x y]; ring

end InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
