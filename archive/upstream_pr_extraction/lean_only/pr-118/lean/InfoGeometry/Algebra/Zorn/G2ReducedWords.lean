/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWordInversion
import InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

/-!
# Reduced words for the existing `WeylG2` normal-form parameter

This owner reuses `WeylG2 = ZMod 6 × Bool`; it introduces no second dihedral
carrier.  The word action is the already verified signed-root action.
-/

namespace InfoGeometry.Algebra.Zorn.G2ReducedWords

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CoordinateWordInversion
open InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

def reducedRotationWord : Fin 6 → List Bool
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [true, false]
  | ⟨2, _⟩ => [true, false, true, false]
  | ⟨3, _⟩ => [true, false, true, false, true, false]
  | ⟨4, _⟩ => [false, true, false, true]
  | ⟨5, _⟩ => [false, true]

def reducedReflectionWord : Fin 6 → List Bool
  | ⟨0, _⟩ => [true]
  | ⟨1, _⟩ => [false]
  | ⟨2, _⟩ => [false, true, false]
  | ⟨3, _⟩ => [false, true, false, true, false]
  | ⟨4, _⟩ => [true, false, true, false, true]
  | ⟨5, _⟩ => [true, false, true]

def toReducedWord : WeylG2 → List Bool
  | (k, false) => reducedRotationWord ⟨k.val, k.isLt⟩
  | (k, true) => reducedReflectionWord ⟨k.val, k.isLt⟩

def dihedralLength (w : WeylG2) : ℕ := (toReducedWord w).length

theorem toReducedWord_length (w : WeylG2) :
    (toReducedWord w).length = dihedralLength w := rfl

theorem toReducedWord_length_le_six (w : WeylG2) :
    dihedralLength w ≤ 6 := by
  rcases w with ⟨k, b⟩
  fin_cases k <;> cases b <;> decide

noncomputable def dihedralToPerm (w : WeylG2) : Equiv.Perm G2CoordinateRoot :=
  coordinateWordAction (toReducedWord w)

theorem coordinateWordAction_toReducedWord_signed
    (w : WeylG2) (r : Bool × G2PositiveRoot) :
    dihedralToPerm w (signedRootCoordinate r) =
      signedRootCoordinate (simpleWordAction (toReducedWord w) r) := by
  exact coordinateWordAction_apply_signed (toReducedWord w) r

noncomputable def dihedralInversionRoots (w : WeylG2) : Finset G2PositiveRoot :=
  coordinateWordInversionRoots (toReducedWord w)

def dihedralSignedInversionRoots (w : WeylG2) : Finset G2PositiveRoot :=
  wordInversionRoots (toReducedWord w)

theorem dihedralInversionRoots_eq_signed (w : WeylG2) :
    dihedralInversionRoots w = dihedralSignedInversionRoots w := by
  rcases w with ⟨k, b⟩
  fin_cases k <;> cases b <;>
    simp only [dihedralInversionRoots, dihedralSignedInversionRoots] <;>
    ext α <;>
    rw [mem_coordinateWordInversionRoots_iff_signed,
      mem_wordInversionRoots_iff] <;>
    cases α <;> decide

theorem dihedralInversion_card_eq_length (w : WeylG2) :
    (dihedralInversionRoots w).card = dihedralLength w := by
  rw [dihedralInversionRoots_eq_signed]
  rcases w with ⟨k, b⟩
  fin_cases k <;> cases b <;> decide

theorem dihedralResidualExponent_card (w : WeylG2) :
    Fintype.card
        ({ α : G2PositiveRoot // α ∈ dihedralInversionRoots w } → Bool) =
      2 ^ dihedralLength w := by
  simp [dihedralInversion_card_eq_length w]

abbrev ResidualCoords (w : WeylG2) :=
  { α : G2PositiveRoot // α ∈ dihedralInversionRoots w } → Bool

theorem residualCoords_card (w : WeylG2) :
    Fintype.card (ResidualCoords w) = 2 ^ dihedralLength w := by
  exact dihedralResidualExponent_card w

theorem residualSigma_card_eq_189 :
    Fintype.card (Σ w : WeylG2, ResidualCoords w) = 189 := by
  calc
    Fintype.card (Σ w : WeylG2, ResidualCoords w) =
        ∑ w : WeylG2, Fintype.card (ResidualCoords w) :=
      Fintype.card_sigma
    _ = ∑ w : WeylG2, 2 ^ dihedralLength w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact residualCoords_card w
    _ = 189 := by decide

theorem dihedralToPerm_injective :
    Function.Injective dihedralToPerm := by
  intro p q hpq
  have hact : ∀ r : Bool × G2PositiveRoot,
      simpleWordAction (toReducedWord p) r =
        simpleWordAction (toReducedWord q) r := by
    intro r
    apply signedRootCoordinate_bijective.injective
    have hr := congrArg
      (fun f : Equiv.Perm G2CoordinateRoot =>
        f (signedRootCoordinate r)) hpq
    simpa [dihedralToPerm, coordinateWordAction_apply_signed] using hr
  rcases p with ⟨kp, bp⟩
  rcases q with ⟨kq, bq⟩
  revert hact
  fin_cases kp <;> fin_cases kq <;> cases bp <;> cases bq <;> decide

/-! The finite carrier bridge.  The source and target are kept separate until
    this explicit table is available. -/

def weylElementOfNF : WeylG2 → G2WeylElement
  | (k, false) =>
      match k.val with
      | 0 => .id
      | 1 => .s1s2
      | 2 => .s1s2s1s2
      | 3 => .w0
      | 4 => .s2s1s2s1
      | 5 => .s2s1
      | _ => .id
  | (k, true) =>
      match k.val with
      | 0 => .s1
      | 1 => .s2
      | 2 => .s2s1s2
      | 3 => .s2s1s2s1s2
      | 4 => .s1s2s1s2s1
      | 5 => .s1s2s1
      | _ => .id

theorem toReducedWord_eq_canonicalWeylWord (w : WeylG2) :
    toReducedWord w = canonicalWeylWord (weylElementOfNF w) := by
  rcases w with ⟨k, b⟩
  fin_cases k <;> cases b <;> rfl

theorem dihedralInversionRoots_eq_canonical (w : WeylG2) :
    dihedralInversionRoots w =
      canonicalInversionRoots (weylElementOfNF w) := by
  rw [dihedralInversionRoots, canonicalInversionRoots,
    toReducedWord_eq_canonicalWeylWord]

theorem dihedralInversionRoots_eq_canonicalSigned (w : WeylG2) :
    dihedralInversionRoots w =
      canonicalSignedInversionRoots (weylElementOfNF w) := by
  rw [dihedralInversionRoots_eq_signed, dihedralSignedInversionRoots,
    canonicalSignedInversionRoots, toReducedWord_eq_canonicalWeylWord]

theorem weylElementOfNF_length (w : WeylG2) :
    weylLength (weylElementOfNF w) = dihedralLength w := by
  rcases w with ⟨k, b⟩
  fin_cases k <;> cases b <;> decide

theorem weylElementOfNF_injective :
    Function.Injective weylElementOfNF := by
  intro p q h
  rcases p with ⟨kp, bp⟩
  rcases q with ⟨kq, bq⟩
  revert h
  fin_cases kp <;> fin_cases kq <;> cases bp <;> cases bq <;> decide

theorem weylElementOfNF_surjective :
    Function.Surjective weylElementOfNF := by
  intro w
  cases w <;>
    first
    | exact ⟨(0, false), rfl⟩
    | exact ⟨(0, true), rfl⟩
    | exact ⟨(1, false), rfl⟩
    | exact ⟨(2, false), rfl⟩
    | exact ⟨(5, false), rfl⟩
    | exact ⟨(2, true), rfl⟩
    | exact ⟨(4, false), rfl⟩
    | exact ⟨(3, false), rfl⟩
    | exact ⟨(5, true), rfl⟩
    | exact ⟨(4, true), rfl⟩
    | exact ⟨(1, true), rfl⟩
    | exact ⟨(3, true), rfl⟩

noncomputable def weylElementOfNFEquiv : WeylG2 ≃ G2WeylElement :=
  Equiv.ofBijective weylElementOfNF
    ⟨weylElementOfNF_injective, weylElementOfNF_surjective⟩

noncomputable def residualRootEquiv (w : WeylG2) :
    { α : G2PositiveRoot // α ∈ dihedralInversionRoots w } ≃
      { α : G2PositiveRoot //
        α ∈ canonicalSignedInversionRoots (weylElementOfNF w) } := by
  let h := dihedralInversionRoots_eq_canonicalSigned w
  exact {
    toFun := fun α => ⟨α.1, by
      rw [← h]
      exact α.2⟩
    invFun := fun α => ⟨α.1, by
      rw [h]
      exact α.2⟩
    left_inv := by intro α; rfl
    right_inv := by intro α; rfl }

noncomputable def residualCoordsCanonicalEquiv (w : WeylG2) :
    ResidualCoords w ≃ CanonicalResidualExponent (weylElementOfNF w) :=
  (residualRootEquiv w).arrowCongr (Equiv.refl Bool)

noncomputable def residualCanonicalSigmaEquiv :
    (Σ w : WeylG2, ResidualCoords w) ≃
      (Σ v : G2WeylElement, CanonicalResidualExponent v) :=
  Equiv.sigmaCongr weylElementOfNFEquiv residualCoordsCanonicalEquiv

noncomputable def residualFlagIndexEquiv :
    (Σ w : WeylG2, ResidualCoords w) ≃ Fin 189 :=
  residualCanonicalSigmaEquiv.trans canonicalFlagIndexEquiv

theorem residualCanonicalSigma_card :
    Fintype.card (Σ w : WeylG2, ResidualCoords w) = 189 := by
  exact (Fintype.card_congr residualCanonicalSigmaEquiv).trans
    canonicalResidualFiber_total_card

end InfoGeometry.Algebra.Zorn.G2ReducedWords
