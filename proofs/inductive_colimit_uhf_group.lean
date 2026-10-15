import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence

open CategoryTheory
open CategoryTheory.Limits
open TypeCat

noncomputable section

/--
  The ω-chain and inductive colimit shape.
-/

abbrev DiagonalLevel (n : ℕ) : Type := Fin n → Bool

instance (n : ℕ) : Fintype (DiagonalLevel n) := by
  infer_instance

/-- Stage n → stage n+1 by appending one fixed bit (0) at the new coordinate. -/
def diagonalEmbed (n : ℕ) : DiagonalLevel n → DiagonalLevel (n + 1) :=
  fun b i => if h : i.1 < n then b ⟨i.1, h⟩ else false

lemma diagonalEmbed_lt (n : ℕ) (b : DiagonalLevel n) {k : ℕ} (hk : k < n) :
    diagonalEmbed n b ⟨k, Nat.lt_succ_of_lt hk⟩ = b ⟨k, hk⟩ := by
  simp [diagonalEmbed, hk]

lemma diagonalEmbed_eq (n : ℕ) (b : DiagonalLevel n) :
    diagonalEmbed n b ⟨n, Nat.lt_succ_self n⟩ = false := by
  simp [diagonalEmbed]

/-- The chain as a functor from `ℕ` to `Type`. -/
def diagonalDiagram : ℕ ⥤ Type _ :=
  Functor.ofSequence (X := DiagonalLevel) (fun n => ↾(diagonalEmbed n))

def uHFColimit : Type := colimit diagonalDiagram

theorem finite_stage_card (n : ℕ) : Fintype.card (DiagonalLevel n) = 2 ^ n := by
  simp [DiagonalLevel]

/-- Projective limit boundary object (Cantor space). -/
def CantorBoundary : Type := ℕ → Bool

def finiteToBoundary (n : ℕ) : DiagonalLevel n → CantorBoundary :=
  fun b k => if h : k < n then b ⟨k, h⟩ else false

/-- Cocone from each finite level into the boundary.
    This is the usual consistency condition for the colimit.
-/
def boundaryCocone : Cocone diagonalDiagram where
  pt := CantorBoundary
  ι := NatTrans.ofSequence (F := diagonalDiagram)
    (G := (Functor.const ℕ).obj CantorBoundary)
    (app := fun n => ↾(finiteToBoundary n))
    (naturality := by
      intro n
      ext b
      dsimp [diagonalDiagram]
      rw [Functor.ofSequence_map_homOfLE_succ]
      funext k
      change finiteToBoundary (n + 1) (diagonalEmbed n b) k = finiteToBoundary n b k
      by_cases hkn : k < n
      · have hk1 : k < n + 1 := Nat.lt_succ_of_lt hkn
        simp only [finiteToBoundary, dif_pos hk1, dif_pos hkn]
        exact diagonalEmbed_lt n b hkn
      · by_cases hk : k < n + 1
        · have hk' : k = n := Nat.eq_of_lt_succ_of_not_lt hk hkn
          subst k
          simpa [finiteToBoundary] using (diagonalEmbed_eq n b)
        · simp [finiteToBoundary, hkn, hk])

/-- Universal map from bulk colimit to boundary. -/
noncomputable def fromColimitBoundary : colimit diagonalDiagram → CantorBoundary :=
  colimit.desc (F := diagonalDiagram) (c := boundaryCocone)

-- Number-theory inductive picture (dyadic rationals = union of 2-power denominators).

-- Helper: change denominator from 2^n to 2^m when n ≤ m.
lemma shift_den (n m : ℕ) (h : n ≤ m) (z : ℤ) :
    (z : ℚ) / (2 ^ n : ℚ) = (((z * (2 ^ (m - n) : ℤ) : ℤ) : ℚ) / (2 ^ m : ℚ)) := by
  have hpow : (2 ^ m : ℚ) = (2 ^ (m - n) : ℚ) * (2 ^ n : ℚ) := by
    rw [← Nat.sub_add_cancel h]
    simp [pow_add, mul_comm]
  rw [hpow]
  field_simp
  have hmul : (((z * (2 ^ (m - n) : ℤ) : ℤ) : ℚ) = (z : ℚ) * ((2 ^ (m - n) : ℕ) : ℚ)) := by
    norm_num
  simpa [hmul]

/-- nth-stage dyadic set. -/
def DyadicLevel (n : ℕ) : Set ℚ :=
  {q | ∃ z : ℤ, q = (z : ℚ) / (2 ^ n : ℚ)}

/--
  Bridge map: each finite diagonal word at level n defines a canonical dyadic rational
  with denominator 2^n via its binary coordinates.
-/
def diagonalWordNumerator (n : ℕ) (b : DiagonalLevel n) : ℤ :=
  ∑ i : Fin n, (if b i then (2 ^ (n - i.1 - 1) : ℤ) else 0)

/-- Canonical dyadic embedding of stage-n words into ℚ at stage n. -/
def diagonalWordToDyadic (n : ℕ) (b : DiagonalLevel n) : ℚ :=
  (diagonalWordNumerator n b : ℚ) / (2 ^ n : ℚ)

lemma diagonalWord_mem_dyadicLevel (n : ℕ) (b : DiagonalLevel n) :
    diagonalWordToDyadic n b ∈ DyadicLevel n := by
  refine ⟨diagonalWordNumerator n b, rfl⟩

lemma diagonalWord_to_dyadic_directed (n : ℕ) (b : DiagonalLevel n) :
    diagonalWordToDyadic n b ∈ DyadicLevel n := by
  exact diagonalWord_mem_dyadicLevel n b

/-- Range of all finite-stage diagonal words under the canonical dyadic map. -/
def diagonalWordToDyadicRange : Set ℚ :=
  Set.range (fun p : Sigma DiagonalLevel => diagonalWordToDyadic p.1 p.2)

/-- The dyadic subgroup `Q_(2)` of rationals with denominator a power of 2. -/
def DyadicGroup : AddSubgroup ℚ :=
{ carrier := {q | ∃ n : ℕ, ∃ z : ℤ, q = (z : ℚ) / (2 ^ n : ℚ)}
  zero_mem' := by
    refine ⟨0, 0, ?_⟩
    norm_num
  add_mem' := by
    rintro a b ⟨n, z, rfl⟩ ⟨m, w, rfl⟩
    let k : ℕ := Nat.max n m
    let Z : ℤ := z * (2 ^ (k - n) : ℤ) + w * (2 ^ (k - m) : ℤ)
    refine ⟨k, Z, ?_⟩
    have hn : n ≤ k := le_max_left _ _
    have hm : m ≤ k := le_max_right _ _
    have hx : (z : ℚ) / (2 ^ n : ℚ) = (((z * (2 ^ (k - n) : ℤ) : ℤ) : ℚ) / (2 ^ k : ℚ)) := by
      simpa using (shift_den n k hn z)
    have hy : (w : ℚ) / (2 ^ m : ℚ) = (((w * (2 ^ (k - m) : ℤ) : ℤ) : ℚ) / (2 ^ k : ℚ)) := by
      simpa using (shift_den m k hm w)
    rw [hx, hy]
    dsimp [Z]
    field_simp
    norm_num
  neg_mem' := by
    rintro q ⟨n, z, rfl⟩
    refine ⟨n, -z, ?_⟩
    simp [div_eq_mul_inv]

}

/-- `DyadicGroup` is exactly the union of all dyadic levels. -/
theorem dyadic_is_union :
    (DyadicGroup : Set ℚ) = ⋃ n : ℕ, DyadicLevel n := by
  ext q
  constructor
  · rintro ⟨n, z, rfl⟩
    exact Set.mem_iUnion.2 ⟨n, ⟨z, rfl⟩⟩
  · rintro hq
    rcases Set.mem_iUnion.mp hq with ⟨n, hn⟩
    rcases hn with ⟨z, rfl⟩
    exact ⟨n, z, rfl⟩

/--
  Bridge theorem: diagonal words from the finite colimit stages map into the
  dyadic subgroup, while the dyadic subgroup is the directed union of stages.
-/
lemma diagonalWordRange_subset_dyadicUnion :
    diagonalWordToDyadicRange ⊆ ⋃ n : ℕ, DyadicLevel n := by
  intro x hx
  rcases hx with ⟨⟨n, b⟩, rfl⟩
  exact Set.mem_iUnion.2 ⟨n, diagonalWord_mem_dyadicLevel n b⟩

/-- Final conceptual bridge statement used by the narrative files. -/
theorem uhf_colimit_dyadic_bridge :
    diagonalWordToDyadicRange ⊆ (DyadicGroup : Set ℚ) := by
  simpa [dyadic_is_union] using diagonalWordRange_subset_dyadicUnion
