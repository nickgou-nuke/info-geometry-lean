import Mathlib.Algebra.PresentedMonoid.Basic
import InfoGeometry.Exceptional.G2ArtinPresentation

/-!
# The positive `I₂(6)` Artin monoid

This is the positive monoid presentation associated with the existing
`ArtinG2` group.  It deliberately contains no inverses and introduces no
second Weyl or Artin group carrier.
-/

namespace InfoGeometry.Exceptional.G2ArtinPositiveMonoid

open InfoGeometry.Exceptional.G2ArtinPresentation

noncomputable section

abbrev Generator := Fin 2

def alternatingLeft : FreeMonoid Generator :=
  FreeMonoid.of 0 * FreeMonoid.of 1 * FreeMonoid.of 0 *
    FreeMonoid.of 1 * FreeMonoid.of 0 * FreeMonoid.of 1

def alternatingRight : FreeMonoid Generator :=
  FreeMonoid.of 1 * FreeMonoid.of 0 * FreeMonoid.of 1 *
    FreeMonoid.of 0 * FreeMonoid.of 1 * FreeMonoid.of 0

inductive Relation : FreeMonoid Generator → FreeMonoid Generator → Prop
  | braid : Relation alternatingLeft alternatingRight

abbrev PositiveArtinG2 := PresentedMonoid Relation

def sigmaZero : PositiveArtinG2 := PresentedMonoid.of Relation 0

def sigmaOne : PositiveArtinG2 := PresentedMonoid.of Relation 1

/-- The positive six-letter Garside word in the monoid presentation. -/
def garside : PositiveArtinG2 :=
  sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne

/-! ## Canonical alternating prefixes

The finite index `Fin 7` records the seven prefixes of the positive
six-letter Garside word, from the empty prefix through the whole word.  The
index already carries Mathlib's native linear lattice; the theorem below
connects those indices to actual left-divisibility witnesses in the presented
monoid.
-/

def alternatingPrefix : Fin 7 → PositiveArtinG2
  | 0 => 1
  | 1 => sigmaZero
  | 2 => sigmaZero * sigmaOne
  | 3 => sigmaZero * sigmaOne * sigmaZero
  | 4 => sigmaZero * sigmaOne * sigmaZero * sigmaOne
  | 5 => sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero
  | 6 => garside

/-! Left divisibility in the positive presentation. -/
def leftDivides (a b : PositiveArtinG2) : Prop := ∃ c, a * c = b

theorem alternatingPrefix_leftDivides_garside (n : Fin 7) :
    leftDivides (alternatingPrefix n) garside := by
  fin_cases n
  · exact ⟨garside, by simp [alternatingPrefix, garside]⟩
  · exact ⟨sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne,
      by simp [alternatingPrefix, garside, mul_assoc]⟩
  · exact ⟨sigmaZero * sigmaOne * sigmaZero * sigmaOne,
      by simp [alternatingPrefix, garside, mul_assoc]⟩
  · exact ⟨sigmaOne * sigmaZero * sigmaOne,
      by simp [alternatingPrefix, garside, mul_assoc]⟩
  · exact ⟨sigmaZero * sigmaOne,
      by simp [alternatingPrefix, garside, mul_assoc]⟩
  · exact ⟨sigmaOne, by simp [alternatingPrefix, garside, mul_assoc]⟩
  · exact ⟨1, by simp [alternatingPrefix, garside]⟩

/-- Right divisibility in the positive presentation. -/
def rightDivides (a b : PositiveArtinG2) : Prop := ∃ c, c * a = b

theorem leftDivides_refl (a : PositiveArtinG2) : leftDivides a a := by
  exact ⟨1, mul_one a⟩

theorem leftDivides_trans {a b c : PositiveArtinG2}
    (hab : leftDivides a b) (hbc : leftDivides b c) : leftDivides a c := by
  rcases hab with ⟨u, rfl⟩
  rcases hbc with ⟨v, rfl⟩
  exact ⟨u * v, (mul_assoc _ _ _).symm⟩

theorem rightDivides_refl (a : PositiveArtinG2) : rightDivides a a := by
  exact ⟨1, one_mul a⟩

theorem rightDivides_trans {a b c : PositiveArtinG2}
    (hab : rightDivides a b) (hbc : rightDivides b c) : rightDivides a c := by
  rcases hab with ⟨u, rfl⟩
  rcases hbc with ⟨v, rfl⟩
  exact ⟨v * u, mul_assoc _ _ _⟩

theorem sigmaZero_leftDivides_garside : leftDivides sigmaZero garside := by
  exact ⟨sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne,
    rfl⟩

theorem sigmaOne_rightDivides_garside : rightDivides sigmaOne garside := by
  exact ⟨sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero,
    rfl⟩

theorem positive_artin_relation :
    sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne =
      sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero := by
  change PresentedMonoid.mk Relation alternatingLeft =
    PresentedMonoid.mk Relation alternatingRight
  exact Quotient.sound (ConGen.Rel.of _ _ Relation.braid)

theorem sigmaOne_leftDivides_garside : leftDivides sigmaOne garside := by
  simp only [leftDivides, garside]
  rw [positive_artin_relation]
  exact ⟨sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero,
    rfl⟩

theorem sigmaZero_rightDivides_garside : rightDivides sigmaZero garside := by
  simp only [rightDivides, garside]
  rw [positive_artin_relation]
  exact ⟨sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne,
    rfl⟩

def generatorAssignment : Generator → ArtinG2
  | 0 => G2ArtinPresentation.sigmaZero
  | 1 => G2ArtinPresentation.sigmaOne

theorem generatorAssignment_respects_relation :
    ∀ a b, Relation a b →
      FreeMonoid.lift generatorAssignment a =
        FreeMonoid.lift generatorAssignment b := by
  intro a b h
  cases h
  simp only [alternatingLeft, alternatingRight, map_mul,
    FreeMonoid.lift_eval_of, generatorAssignment]
  exact G2ArtinPresentation.artin_relation

def toArtinGroup : PositiveArtinG2 →* ArtinG2 :=
  PresentedMonoid.lift generatorAssignment generatorAssignment_respects_relation

@[simp] theorem toArtinGroup_sigmaZero :
    toArtinGroup sigmaZero = G2ArtinPresentation.sigmaZero := by
  exact PresentedMonoid.lift_of _ _

@[simp] theorem toArtinGroup_sigmaOne :
    toArtinGroup sigmaOne = G2ArtinPresentation.sigmaOne := by
  exact PresentedMonoid.lift_of _ _

theorem toArtinGroup_garside :
    toArtinGroup garside = G2ArtinPresentation.garside := by
  simp only [garside, map_mul, toArtinGroup_sigmaZero, toArtinGroup_sigmaOne]
  rfl

end
end InfoGeometry.Exceptional.G2ArtinPositiveMonoid
