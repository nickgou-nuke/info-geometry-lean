import InfoGeometry.Cantor.CantorRandomWalk
import InfoGeometry.Analysis.L2CantorCommutation

/-!
# Cantor golden-mean bitword bridge

This module isolates the exact relation between the repository's full dyadic
Cantor boundary and the Omega/Automath golden-mean bitword lane.

The repository's Cantor carrier is the full sequence space `Nat -> Bool`.  The
Omega lane studies the golden-mean subshift, i.e. the subtype of sequences with
no adjacent `true true` pattern.  This file keeps that distinction explicit:
the golden-mean space is a closed symbolic subspace of the full Cantor
boundary, not a replacement for the full Cuntz boundary.

No external repository is imported.  The definitions here are the repo-native
shadow of the shared bitword interface.
-/

namespace InfoGeometry.Canonical.CantorGoldenMeanBitwordBridge

open InfoGeometry.Cantor.CantorRandomWalk

/-- The Omega/golden-mean admissibility predicate: no adjacent occupied bits. -/
def NoAdjacentOnes (x : ℕ → Bool) : Prop :=
  ∀ n : Nat, ¬ (x n = true ∧ x (n + 1) = true)

/-- The golden-mean subshift as a subtype of the full Cantor boundary. -/
abbrev GoldenMeanBoundary : Type :=
  {x : ℕ → Bool // NoAdjacentOnes x}

/-- The length-`n` prefix of an infinite Cantor boundary point. -/
def prefixWord (x : ℕ → Bool) (n : Nat) : Fin n → Bool :=
  fun i => x i.1

/-- Finite no-adjacent-ones predicate on a fixed-length bitword. -/
def NoAdjacentFinite {n : Nat} (w : Fin n → Bool) : Prop :=
  ∀ i : Fin n, ∀ hnext : i.1 + 1 < n,
    ¬ (w i = true ∧ w ⟨i.1 + 1, hnext⟩ = true)

/-- Prefixes of a golden-mean boundary point are finite golden-mean words. -/
theorem prefix_noAdjacentFinite (x : GoldenMeanBoundary) (n : Nat) :
    NoAdjacentFinite (prefixWord x.1 n) := by
  intro i hnext hpair
  exact x.2 i.1 hpair

/--
Full Cantor boundary points are determined by all finite prefixes.

This is the repo-native counterpart of Omega's inverse-limit determinacy
statement for stable addresses.
-/
theorem eq_of_prefix_eq
    (x y : ℕ → Bool)
    (h : ∀ n : Nat, prefixWord x n = prefixWord y n) :
    x = y := by
  funext k
  have hk :=
    congrArg
      (fun w : Fin (k + 1) → Bool => w ⟨k, Nat.lt_succ_self k⟩)
      (h (k + 1))
  simpa [prefixWord] using hk

/-- Golden-mean boundary points are determined by all finite prefixes. -/
theorem goldenMean_ext
    {x y : GoldenMeanBoundary}
    (h : ∀ n : Nat, prefixWord x.1 n = prefixWord y.1 n) :
    x = y := by
  apply Subtype.ext
  exact eq_of_prefix_eq x.1 y.1 h

/-! ## Boolean boundary versus plus/minus Cuntz boundary -/

/-- Boolean `false/true` as the `plus/minus` branch alphabet of `L2CantorCommutation`. -/
def sectorOfBool : Bool -> InfoGeometry.Analysis.L2CantorCommutation.BinarySector
  | false => InfoGeometry.Analysis.L2CantorCommutation.BinarySector.plus
  | true => InfoGeometry.Analysis.L2CantorCommutation.BinarySector.minus

/-- Inverse alphabet map from `plus/minus` sectors to Boolean bits. -/
def boolOfSector : InfoGeometry.Analysis.L2CantorCommutation.BinarySector -> Bool
  | InfoGeometry.Analysis.L2CantorCommutation.BinarySector.plus => false
  | InfoGeometry.Analysis.L2CantorCommutation.BinarySector.minus => true

@[simp] theorem boolOfSector_sectorOfBool (b : Bool) :
    boolOfSector (sectorOfBool b) = b := by
  cases b <;> rfl

@[simp] theorem sectorOfBool_boolOfSector (s : InfoGeometry.Analysis.L2CantorCommutation.BinarySector) :
    sectorOfBool (boolOfSector s) = s := by
  cases s <;> rfl

/-- Convert a Boolean Cantor boundary point to the `plus/minus` Cuntz boundary. -/
def toBaseIndex (x : ℕ → Bool) : InfoGeometry.Analysis.L2CantorCommutation.BaseIndex :=
  fun n => sectorOfBool (x n)

/-- Convert the `plus/minus` Cuntz boundary back to Boolean bits. -/
def ofBaseIndex (x : InfoGeometry.Analysis.L2CantorCommutation.BaseIndex) : ℕ → Bool :=
  fun n => boolOfSector (x n)

@[simp] theorem ofBaseIndex_toBaseIndex (x : ℕ → Bool) :
    ofBaseIndex (toBaseIndex x) = x := by
  funext n
  simp [ofBaseIndex, toBaseIndex]

@[simp] theorem toBaseIndex_ofBaseIndex (x : InfoGeometry.Analysis.L2CantorCommutation.BaseIndex) :
    toBaseIndex (ofBaseIndex x) = x := by
  funext n
  simp [ofBaseIndex, toBaseIndex]

/-- The full Boolean Cantor boundary is equivalent to the repo's `plus/minus` Cuntz boundary. -/
def cantorBoundaryEquivBaseIndex : (ℕ → Bool) ≃ InfoGeometry.Analysis.L2CantorCommutation.BaseIndex where
  toFun := toBaseIndex
  invFun := ofBaseIndex
  left_inv := ofBaseIndex_toBaseIndex
  right_inv := toBaseIndex_ofBaseIndex

/-- Prepend a Boolean bit to an infinite boundary point. -/
def consBit (b : Bool) (x : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | n + 1 => x n

@[simp] theorem consBit_zero (b : Bool) (x : ℕ → Bool) :
    consBit b x 0 = b := by
  rfl

@[simp] theorem consBit_succ (b : Bool) (x : ℕ → Bool) (n : Nat) :
    consBit b x (n + 1) = x n := by
  rfl

/-- Boolean prepend is transported to `L2.prepend` under the alphabet equivalence. -/
theorem toBaseIndex_consBit (b : Bool) (x : ℕ → Bool) :
    toBaseIndex (consBit b x) =
      InfoGeometry.Analysis.L2CantorCommutation.prepend (sectorOfBool b) (toBaseIndex x) := by
  funext n
  cases n <;> cases b <;> rfl

/-- Adding a leading zero preserves the golden-mean subshift. -/
theorem noAdjacentOnes_cons_false (x : GoldenMeanBoundary) :
    NoAdjacentOnes (consBit false x.1) := by
  intro n hpair
  cases n with
  | zero =>
      simp [consBit] at hpair
  | succ n =>
      exact x.2 n hpair

/-- Finite prefixes remain golden-mean admissible after prepending `false`. -/
theorem prefix_noAdjacentFinite_cons_false
    (x : GoldenMeanBoundary) (n : Nat) :
    NoAdjacentFinite (prefixWord (consBit false x.1) n) := by
  exact prefix_noAdjacentFinite ⟨consBit false x.1, noAdjacentOnes_cons_false x⟩ n

/--
Adding a leading one preserves the golden-mean subshift exactly when the old
head bit is zero.
-/
theorem noAdjacentOnes_cons_true_of_head_false
    (x : GoldenMeanBoundary)
    (hhead : x.1 0 = false) :
    NoAdjacentOnes (consBit true x.1) := by
  intro n hpair
  cases n with
  | zero =>
      have hx0 : x.1 0 = true := by
        simpa [consBit] using hpair.2
      rw [hhead] at hx0
      contradiction
  | succ n =>
      exact x.2 n hpair

theorem noAdjacentOnes_cons_true_iff_head_false
    (x : GoldenMeanBoundary) :
    NoAdjacentOnes (consBit true x.1) ↔ x.1 0 = false := by
  constructor
  · intro h
    by_cases hx : x.1 0 = false
    · exact hx
    · have hxtrue : x.1 0 = true := by
        cases hbit : x.1 0 <;> simp_all
      have hpair :
          consBit true x.1 0 = true ∧
            consBit true x.1 (0 + 1) = true := by
        constructor
        · rfl
        · simpa [consBit] using hxtrue
      exact False.elim (h 0 hpair)
  · intro hhead
    exact noAdjacentOnes_cons_true_of_head_false x hhead

/-- Finite prefixes remain golden-mean admissible after legally prepending `true`. -/
theorem prefix_noAdjacentFinite_cons_true_of_head_false
    (x : GoldenMeanBoundary) (hhead : x.1 0 = false) (n : Nat) :
    NoAdjacentFinite (prefixWord (consBit true x.1) n) := by
  exact prefix_noAdjacentFinite
    ⟨consBit true x.1, noAdjacentOnes_cons_true_of_head_false x hhead⟩ n

end InfoGeometry.Canonical.CantorGoldenMeanBitwordBridge
