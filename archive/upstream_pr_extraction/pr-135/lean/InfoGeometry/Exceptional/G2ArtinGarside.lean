import InfoGeometry.Exceptional.G2ArtinPositiveMonoid

/-!
# Finite simple divisors for the positive `I₂(6)` Artin monoid

This owner records the finite simple prefix interval
`1, s, st, sts, stst, ststs, ststst` inside the existing positive
`I₂(6)` Artin monoid.  It deliberately does not claim cancellativity or a
global Garside normal-form theorem for `PositiveArtinG2`; those require
additional algebra not supplied by `PresentedMonoid` alone.
-/

namespace InfoGeometry.Exceptional.G2ArtinGarside

open InfoGeometry.Exceptional.G2ArtinPositiveMonoid

noncomputable section

abbrev Simple := Fin 7

def simpleElement (i : Simple) : PositiveArtinG2 :=
  alternatingPrefix i

def simpleComplementLetters : Simple → List G2ArtinPositiveMonoid.Generator
  | ⟨0, _⟩ => [0, 1, 0, 1, 0, 1]
  | ⟨1, _⟩ => [1, 0, 1, 0, 1]
  | ⟨2, _⟩ => [0, 1, 0, 1]
  | ⟨3, _⟩ => [1, 0, 1]
  | ⟨4, _⟩ => [0, 1]
  | ⟨5, _⟩ => [1]
  | ⟨6, _⟩ => []

def simpleComplement (i : Simple) : PositiveArtinG2 :=
  PresentedMonoid.mk Relation
    (FreeMonoid.ofList (simpleComplementLetters i))

def positiveGarside : PositiveArtinG2 :=
  PresentedMonoid.mk Relation alternatingLeft

def simplePrefixLe (i j : Simple) : Prop := i.val ≤ j.val

theorem simplePrefixLe_refl (i : Simple) : simplePrefixLe i i := by
  exact le_rfl

theorem simplePrefixLe_trans {i j k : Simple}
    (hij : simplePrefixLe i j) (hjk : simplePrefixLe j k) :
    simplePrefixLe i k := by
  exact le_trans hij hjk

def simplePrefixSup (i j : Simple) : Simple := ⟨max i.val j.val, by omega⟩

def simplePrefixInf (i j : Simple) : Simple := ⟨min i.val j.val, by omega⟩

theorem simplePrefixLe_sup (i j : Simple) :
    simplePrefixLe i (simplePrefixSup i j) ∧
      simplePrefixLe j (simplePrefixSup i j) := by
  constructor <;> dsimp [simplePrefixLe, simplePrefixSup] <;> omega

theorem simplePrefix_inf_le (i j : Simple) :
    simplePrefixLe (simplePrefixInf i j) i ∧
      simplePrefixLe (simplePrefixInf i j) j := by
  constructor <;> dsimp [simplePrefixLe, simplePrefixInf] <;> omega

theorem simplePrefixSup_least (i j k : Simple) :
    simplePrefixLe (simplePrefixSup i j) k ↔
      simplePrefixLe i k ∧ simplePrefixLe j k := by
  dsimp [simplePrefixLe, simplePrefixSup]
  omega

theorem simplePrefixInf_greatest (i j k : Simple) :
    simplePrefixLe k (simplePrefixInf i j) ↔
      simplePrefixLe k i ∧ simplePrefixLe k j := by
  dsimp [simplePrefixLe, simplePrefixInf]
  omega

theorem simpleElement_mul_complement (i : Simple) :
    simpleElement i * simpleComplement i = positiveGarside := by
  unfold simpleElement simpleComplement positiveGarside
    simpleComplementLetters
  fin_cases i <;> rfl

theorem positiveGarside_toArtinGroup :
    toArtinGroup positiveGarside = G2ArtinPresentation.garside := by
  simpa [positiveGarside] using toArtinGroup_garside

def groupSimpleElement : Simple → G2ArtinPresentation.ArtinG2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => G2ArtinPresentation.sigmaZero
  | ⟨2, _⟩ => G2ArtinPresentation.sigmaZero * G2ArtinPresentation.sigmaOne
  | ⟨3, _⟩ => G2ArtinPresentation.sigmaZero * G2ArtinPresentation.sigmaOne *
      G2ArtinPresentation.sigmaZero
  | ⟨4, _⟩ => G2ArtinPresentation.sigmaZero * G2ArtinPresentation.sigmaOne *
      G2ArtinPresentation.sigmaZero * G2ArtinPresentation.sigmaOne
  | ⟨5, _⟩ => G2ArtinPresentation.sigmaZero * G2ArtinPresentation.sigmaOne *
      G2ArtinPresentation.sigmaZero * G2ArtinPresentation.sigmaOne *
      G2ArtinPresentation.sigmaZero
  | ⟨6, _⟩ => G2ArtinPresentation.garside

theorem simpleElement_toArtinGroup (i : Simple) :
    toArtinGroup (simpleElement i) = groupSimpleElement i := by
  unfold simpleElement groupSimpleElement
  fin_cases i <;> simp [alternatingPrefix, garside,
    G2ArtinPresentation.sigmaZero, G2ArtinPresentation.sigmaOne,
    G2ArtinPresentation.garside]

end
end InfoGeometry.Exceptional.G2ArtinGarside
