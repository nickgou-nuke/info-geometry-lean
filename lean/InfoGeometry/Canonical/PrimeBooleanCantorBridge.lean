/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.CantorCylinderLattice

/-!
# Prime Boolean–Cantor Cylinder Lattice Bridge

Connects the finite Boolean powerset `B(P)` (and `BooleanWeylGroup L` from
`FormalPrimeRootSystem`) to the level-`n` Cantor cylinder lattice
`Set (BinaryWord n)` from `CantorCylinderLattice`.

Because `Set (BinaryWord n)` has cardinality `2^(2^n)` while `B(n)` has
cardinality `2^n`, the two lattices are **not** isomorphic for `n ≥ 1`.
This module records the exact typed embeddings:

1. **Support-cone meet-semilattice embedding**
   `supportCone S = { w : BinaryWord n | ∀ i, w i = true → i ∈ S }`:
   injective, order-reflecting (`supportCone S ⊆ supportCone T ↔ S ⊆ T`),
   preserves `∩` and `⊤`, and provably does **not** preserve `∪` for `n = 2`.
2. **Weight-one atom embedding**
   `weightOneEmbed S = ⋃ i ∈ S, cylinder n (singleBitWord i)`:
   an injective generalized-Boolean lattice homomorphism into the singleton
   cylinder atoms (preserving `∅`, `∪`, `∩`, and set difference `\`).
3. **Boolean Weyl group to binary-word readout**:
   given an enumeration `e : Fin L.primes.card ≃ L.primes`, `BooleanWeylGroup L`
   is in bijection with `BinaryWord L.primes.card` and `weylSign w` equals
   `(-1 : ℝ) ^ wordWeight (weylToWord e w)`.
-/

namespace InfoGeometry.Canonical.PrimeBooleanCantorBridge

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.CantorCylinderLattice

/-! ## 1. Support-cone order & meet embedding -/

/-- The support of a binary word: indices where the bit is `true`. -/
def wordSupport {n : ℕ} (w : BinaryWord n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i = true)

/-- Hamming weight (number of `true` bits) of a binary word. -/
def wordWeight {n : ℕ} (w : BinaryWord n) : ℕ :=
  (wordSupport w).card

/-- Characteristic binary word of a subset `S : Finset (Fin n)`. -/
def subsetToWord {n : ℕ} (S : Finset (Fin n)) : BinaryWord n :=
  fun i => decide (i ∈ S)

@[simp] theorem wordSupport_subsetToWord {n : ℕ} (S : Finset (Fin n)) :
    wordSupport (subsetToWord S) = S := by
  ext i
  simp [wordSupport, subsetToWord]

@[simp] theorem subsetToWord_wordSupport {n : ℕ} (w : BinaryWord n) :
    subsetToWord (wordSupport w) = w := by
  funext i
  cases h : w i <;> simp [wordSupport, subsetToWord, h]

/-- Bijection between subsets of `Fin n` and level-`n` binary words. -/
def finsetEquivBinaryWord (n : ℕ) : Finset (Fin n) ≃ BinaryWord n where
  toFun := subsetToWord
  invFun := wordSupport
  left_inv := wordSupport_subsetToWord
  right_inv := subsetToWord_wordSupport

/-- Support cone `S ↦ { w : BinaryWord n | supp(w) ⊆ S }` in the Cantor cylinder lattice. -/
def supportCone {n : ℕ} (S : Finset (Fin n)) : Set (BinaryWord n) :=
  { w : BinaryWord n | wordSupport w ⊆ S }

theorem mem_supportCone_iff {n : ℕ} {S : Finset (Fin n)} {w : BinaryWord n} :
    w ∈ supportCone S ↔ ∀ i : Fin n, w i = true → i ∈ S := by
  simp [supportCone, wordSupport, Finset.subset_iff]

theorem subsetToWord_mem_supportCone {n : ℕ} (S : Finset (Fin n)) :
    subsetToWord S ∈ supportCone S := by
  simp [supportCone]

/-- Order-embedding property: `supportCone S ⊆ supportCone T ↔ S ⊆ T`. -/
theorem supportCone_subset_iff {n : ℕ} (S T : Finset (Fin n)) :
    supportCone S ⊆ supportCone T ↔ S ⊆ T := by
  constructor
  · intro h
    have hmem : subsetToWord S ∈ supportCone T := h (subsetToWord_mem_supportCone S)
    simpa [supportCone] using hmem
  · intro hST w hw
    exact Finset.Subset.trans hw hST

theorem supportCone_injective (n : ℕ) :
    Function.Injective (@supportCone n) := by
  intro S T h
  apply Finset.Subset.antisymm
  · exact (supportCone_subset_iff S T).mp (by rw [h])
  · exact (supportCone_subset_iff T S).mp (by rw [h])

/-- `supportCone` preserves meets (intersections). -/
theorem supportCone_inter {n : ℕ} (S T : Finset (Fin n)) :
    supportCone (S ∩ T) = supportCone S ∩ supportCone T := by
  ext w
  simp [supportCone, Finset.subset_inter_iff]

/-- `supportCone` preserves the top element. -/
theorem supportCone_univ (n : ℕ) :
    supportCone (Finset.univ : Finset (Fin n)) = Set.univ := by
  ext w
  simp [supportCone]

/-- Explicit counterexample showing `supportCone` is NOT a join homomorphism at `n = 2`:
the all-ones word lies in `supportCone ({0} ∪ {1})` but in neither `supportCone {0}` nor
`supportCone {1}`. -/
theorem supportCone_union_ne_n2 :
    supportCone ({(0 : Fin 2)} ∪ {(1 : Fin 2)}) ≠
      supportCone {(0 : Fin 2)} ∪ supportCone {(1 : Fin 2)} := by
  intro h
  have hmem : subsetToWord ({(0 : Fin 2), (1 : Fin 2)}) ∈
      supportCone ({(0 : Fin 2)} ∪ {(1 : Fin 2)}) := by
    simp [supportCone]
  rw [h] at hmem
  rcases hmem with h0 | h1
  · have : (1 : Fin 2) ∈ ({(0 : Fin 2)} : Finset (Fin 2)) := by
      have := (mem_supportCone_iff.mp h0) 1
      simp [subsetToWord] at this
    simp at this
  · have : (0 : Fin 2) ∈ ({(1 : Fin 2)} : Finset (Fin 2)) := by
      have := (mem_supportCone_iff.mp h1) 0
      simp [subsetToWord] at this
    simp at this

/-! ## 2. Injective lattice / generalized-Boolean embedding into Cantor cylinder atoms -/

/-- The weight-one binary word with a single `true` bit at coordinate `i`. -/
def singleBitWord {n : ℕ} (i : Fin n) : BinaryWord n :=
  fun j => decide (j = i)

theorem singleBitWord_injective (n : ℕ) :
    Function.Injective (@singleBitWord n) := by
  intro i j h
  have hi := congrFun h i
  simp [singleBitWord] at hi
  exact hi

/-- Embedding of `Finset (Fin n)` into unions of weight-one Cantor cylinder atoms. -/
def weightOneEmbed {n : ℕ} (S : Finset (Fin n)) : Set (BinaryWord n) :=
  ⋃ i ∈ S, cylinder n (singleBitWord i)

theorem mem_weightOneEmbed_iff {n : ℕ} {S : Finset (Fin n)} {w : BinaryWord n} :
    w ∈ weightOneEmbed S ↔ ∃ i ∈ S, w = singleBitWord i := by
  simp [weightOneEmbed, cylinder]

theorem singleBitWord_mem_weightOneEmbed_iff {n : ℕ} {S : Finset (Fin n)} {i : Fin n} :
    singleBitWord i ∈ weightOneEmbed S ↔ i ∈ S := by
  rw [mem_weightOneEmbed_iff]
  constructor
  · rintro ⟨j, hj, hij⟩
    have := singleBitWord_injective n hij
    simpa [this] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem weightOneEmbed_injective (n : ℕ) :
    Function.Injective (@weightOneEmbed n) := by
  intro S T h
  ext i
  rw [← singleBitWord_mem_weightOneEmbed_iff (S := S),
    ← singleBitWord_mem_weightOneEmbed_iff (S := T), h]

theorem weightOneEmbed_empty (n : ℕ) :
    weightOneEmbed (∅ : Finset (Fin n)) = ⊥ := by
  ext w
  simp [mem_weightOneEmbed_iff]

theorem weightOneEmbed_union {n : ℕ} (S T : Finset (Fin n)) :
    weightOneEmbed (S ∪ T) = weightOneEmbed S ⊔ weightOneEmbed T := by
  ext w
  simp only [mem_weightOneEmbed_iff, Finset.mem_union, Set.sup_eq_union, Set.mem_union]
  constructor
  · rintro ⟨i, hi | hi, rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, Or.inl hi, rfl⟩
    · exact ⟨i, Or.inr hi, rfl⟩

theorem weightOneEmbed_inter {n : ℕ} (S T : Finset (Fin n)) :
    weightOneEmbed (S ∩ T) = weightOneEmbed S ⊓ weightOneEmbed T := by
  ext w
  simp only [mem_weightOneEmbed_iff, Finset.mem_inter, Set.inf_eq_inter, Set.mem_inter_iff]
  constructor
  · rintro ⟨i, ⟨hiS, hiT⟩, rfl⟩
    exact ⟨⟨i, hiS, rfl⟩, ⟨i, hiT, rfl⟩⟩
  · rintro ⟨⟨i, hiS, rfl⟩, ⟨j, hjT, hij⟩⟩
    have hEq := singleBitWord_injective n hij
    exact ⟨i, ⟨hiS, hEq ▸ hjT⟩, rfl⟩

theorem weightOneEmbed_sdiff {n : ℕ} (S T : Finset (Fin n)) :
    weightOneEmbed (S \ T) = weightOneEmbed S \ weightOneEmbed T := by
  ext w
  simp only [mem_weightOneEmbed_iff, Finset.mem_sdiff, Set.mem_sdiff]
  constructor
  · rintro ⟨i, ⟨hiS, hiT⟩, rfl⟩
    refine ⟨⟨i, hiS, rfl⟩, ?_⟩
    rintro ⟨j, hjT, hij⟩
    exact hiT (singleBitWord_injective n hij ▸ hjT)
  · rintro ⟨⟨i, hiS, rfl⟩, hnot⟩
    refine ⟨i, ⟨hiS, ?_⟩, rfl⟩
    intro hiT
    exact hnot ⟨i, hiT, rfl⟩

/-! ## 3. Boolean Weyl group to Cantor binary-word readout -/

/-- Read a `BooleanWeylGroup L` element as a binary word via an enumeration
`e : Fin L.primes.card ≃ L.primes`. -/
def weylToWord {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BooleanWeylGroup L) :
    BinaryWord L.primes.card :=
  fun i => decide ((e i : ℕ) ∈ w.support)

/-- Encode a binary word as the Boolean Weyl element supported on the
corresponding enumerated prime modes. -/
def wordToWeyl {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BinaryWord L.primes.card) :
    BooleanWeylGroup L where
  support := (Finset.univ.filter fun i => w i = true).image fun i => (e i : ℕ)
  support_subset := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
    exact (e i).property

/-- Encoding a word as a Weyl support and reading it back recovers the word. -/
@[simp] theorem weylToWord_wordToWeyl {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BinaryWord L.primes.card) :
    weylToWord e (wordToWeyl e w) = w := by
  funext i
  simp [weylToWord, wordToWeyl]

/-- Reading a Weyl support as a word and encoding it recovers the Weyl element. -/
private theorem booleanWeylGroup_ext {L : FormalPrimeRootLattice}
    {a b : BooleanWeylGroup L} (h : a.support = b.support) : a = b := by
  cases a with
  | mk sa ha =>
    cases b with
    | mk sb hb =>
      cases h
      rfl

@[simp] theorem wordToWeyl_weylToWord {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BooleanWeylGroup L) :
    wordToWeyl e (weylToWord e w) = w := by
  cases w with
  | mk support hsubset =>
    have hSupport : (wordToWeyl e (weylToWord e ⟨support, hsubset⟩)).support = support := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_image.mp hp with ⟨i, hi, hip⟩
        subst p
        have hi' : (e i : ℕ) ∈ support := by
          simpa [weylToWord] using hi
        exact hi'
      · intro hp
        have hpL : p ∈ L.primes := hsubset hp
        refine Finset.mem_image.mpr ⟨e.symm ⟨p, hpL⟩, ?_, ?_⟩
        · simp [weylToWord, hp]
        · simp
    exact booleanWeylGroup_ext hSupport

/-- The finite Boolean Weyl carrier is equivalent to the bit-vector carrier
after choosing an enumeration of the finite prime cutoff. -/
def booleanWeylEquivBinaryWord {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) :
    BooleanWeylGroup L ≃ BinaryWord L.primes.card where
  toFun := weylToWord e
  invFun := wordToWeyl e
  left_inv := wordToWeyl_weylToWord e
  right_inv := weylToWord_wordToWeyl e

/-- The Hamming weight of `weylToWord e w` equals the cardinality of `w.support`. -/
theorem wordWeight_weylToWord {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BooleanWeylGroup L) :
    wordWeight (weylToWord e w) = w.support.card := by
  classical
  unfold wordWeight wordSupport weylToWord
  refine Finset.card_bij (fun i _ => (e i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi
    exact hi
  · intro i _ j _ hij
    exact e.injective (Subtype.ext hij)
  · intro p hp
    have hpL : p ∈ L.primes := w.support_subset hp
    refine ⟨e.symm ⟨p, hpL⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      simpa using hp
    · simp

/-- The Weyl sign character `weylSign w` equals `(-1)^(wordWeight (weylToWord e w))`. -/
theorem weylSign_eq_neg_one_pow_wordWeight {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BooleanWeylGroup L) :
    weylSign w = (-1 : ℝ) ^ wordWeight (weylToWord e w) := by
  rw [wordWeight_weylToWord, weylSign]

end InfoGeometry.Canonical.PrimeBooleanCantorBridge
