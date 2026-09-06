import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

/-!
# The native line-set quotient

`nativeLines` stores three finite line sets, whereas a candidate vector is only
a generator of one of those sets.  This owner records the exact quotient
relation before any transport to the older `LinesThroughPoint` carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient

open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber

def lineGeneratorRel (y z : OctImF2) : Prop :=
  lineSet y = lineSet z

def lineGeneratorSetoid : Setoid OctImF2 where
  r := lineGeneratorRel
  iseqv := by
    constructor
    · intro y
      rfl
    · intro y z h
      exact h.symm
    · intro y z w hyz hzw
      exact hyz.trans hzw

theorem lineGeneratorRel_iff
    {y z : OctImF2} :
    lineGeneratorRel y z ↔ lineSet y = lineSet z := Iff.rfl

abbrev NativeCandidate := {y : OctImF2 // y ∈ candidates}

/-! The canonical quotient map from a candidate generator to its native
line-set carrier.  Its codomain is the already deduplicated image
`nativeLines`; no legacy incidence carrier is involved. -/
def candidateLine (y : NativeCandidate) : NativeLine :=
  ⟨lineSet y.1, Finset.mem_image.mpr ⟨y.1, y.2, rfl⟩⟩

theorem candidateLine_surjective : Function.Surjective candidateLine := by
  rintro ⟨L, hL⟩
  have hmem : L ∈ candidates.image lineSet := by
    change L ∈ nativeLines at hL
    exact hL
  rcases Finset.mem_image.mp hmem with ⟨y, hy, hline⟩
  exact ⟨⟨y, hy⟩, by
    apply Subtype.ext
    exact hline⟩

def nativeCandidateRel (y z : NativeCandidate) : Prop :=
  lineGeneratorRel y.1 z.1

theorem nativeCandidateRel_iff
    {y z : NativeCandidate} :
    nativeCandidateRel y z ↔
      z.1 = y.1 ∨ z.1 =
        InfoGeometry.Algebra.Zorn.G2NativePointFoundation.nativeBasePoint + y.1 := by
  change lineSet y.1 = lineSet z.1 ↔ _
  exact lineSet_eq_lineSet_iff y.2 z.2

def nativeCandidateSetoid : Setoid NativeCandidate where
  r := nativeCandidateRel
  iseqv := by
    constructor
    · intro y
      rfl
    · intro y z h
      exact h.symm
    · intro y z w hyz hzw
      exact hyz.trans hzw

instance : Setoid NativeCandidate := nativeCandidateSetoid

abbrev nativeLineQuotient := Quotient nativeCandidateSetoid

noncomputable def nativeCandidateOfLine
    (L : NativeLine) : NativeCandidate :=
  let h : L.1 ∈ candidates.image lineSet := by
    have h0 : L.1 ∈ nativeLines := L.2
    change L.1 ∈ candidates.image lineSet at h0
    exact h0
  let w := Classical.choose (Finset.mem_image.mp h)
  ⟨w, (Classical.choose_spec (Finset.mem_image.mp h)).1⟩

theorem nativeCandidateOfLine_spec
    (L : NativeLine) :
    lineSet (nativeCandidateOfLine L).1 = L.1 := by
  dsimp [nativeCandidateOfLine]
  have h : L.1 ∈ candidates.image lineSet := by
    have h0 : L.1 ∈ nativeLines := L.2
    change L.1 ∈ candidates.image lineSet at h0
    exact h0
  exact (Classical.choose_spec (Finset.mem_image.mp h)).2

def nativeLineOfQuotient (q : nativeLineQuotient) :
    NativeLine := Quotient.lift
      (fun y => ⟨lineSet y.1, Finset.mem_image.mpr ⟨y.1, y.2, rfl⟩⟩)
      (by
        intro y z h
        apply Subtype.ext
        exact h)
      q

noncomputable def quotientOfNativeLine
    (L : NativeLine) : nativeLineQuotient :=
  Quotient.mk' (nativeCandidateOfLine L)

theorem quotientOfNativeLine_spec
    (L : NativeLine) :
    lineSet (nativeCandidateOfLine L).1 = L.1 :=
  nativeCandidateOfLine_spec L

noncomputable def lineSetQuotientToNativeLines :
    nativeLineQuotient ≃ NativeLine where
  toFun := nativeLineOfQuotient
  invFun := quotientOfNativeLine
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change Quotient.mk' (nativeCandidateOfLine
        (nativeLineOfQuotient (Quotient.mk' y))) = Quotient.mk' y
      apply Quotient.sound
      change lineSet (nativeCandidateOfLine
        (nativeLineOfQuotient (Quotient.mk' y))).1 = lineSet y.1
      have hmem : lineSet y.1 ∈ candidates.image lineSet :=
        Finset.mem_image.mpr ⟨y.1, y.2, rfl⟩
      have hchosen := Classical.choose_spec (Finset.mem_image.mp hmem)
      exact hchosen.2
  right_inv L := by
    apply Subtype.ext
    exact quotientOfNativeLine_spec L

end InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient
