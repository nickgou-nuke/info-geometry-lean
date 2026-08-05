import Mathlib.Tactic
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Clifford.BottPeriodicity

/-!
# InfoGeometry.Topology.BottPeriodicCantorEntropyGraph

Bott-periodic Cantor entropy graph socket.

The ordinary binary Cantor boundary uses one stream of bits.  The Bott-periodic
boundary keeps a finite clock of parallel bit streams:

* complex Bott clock: period `2`;
* real Bott clock: period `8`.

This file does not construct the full infinite CAR algebra or a topological
K-theory classification.  It records the theorem-safe interface consumed by
those layers: Bott clock blocks, multi-stream Cantor addresses, random-walk
weights, entropy coupling between streams, and the Drazin-Hodge matter envelope.
-/

noncomputable section

namespace InfoGeometry.Topology.BottPeriodicCantorEntropyGraph

open scoped BigOperators
open scoped TensorProduct

/-! ## 1. Bott clocks and multi-stream binary addresses -/

/-- The two Bott clocks used by the boundary socket. -/
inductive BottKind where
  | complex
  | real
  deriving DecidableEq, Repr

/-- Bott period: complex period `2`, real period `8`. -/
def bottPeriod : BottKind → ℕ
  | BottKind.complex => 2
  | BottKind.real => 8

/-- Matrix amplification per full Bott cycle. -/
def bottMatrixFactor : BottKind → ℕ
  | BottKind.complex => 2
  | BottKind.real => 16

@[simp] theorem bottPeriod_complex :
    bottPeriod BottKind.complex = 2 :=
  rfl

@[simp] theorem bottPeriod_real :
    bottPeriod BottKind.real = 8 :=
  rfl

@[simp] theorem bottMatrixFactor_complex :
    bottMatrixFactor BottKind.complex = 2 :=
  rfl

@[simp] theorem bottMatrixFactor_real :
    bottMatrixFactor BottKind.real = 16 :=
  rfl

theorem bottPeriod_pos (kind : BottKind) :
    0 < bottPeriod kind := by
  cases kind <;> decide

/-- One phase slot in the Bott clock. -/
abbrev BottPhase (kind : BottKind) : Type :=
  Fin (bottPeriod kind)

/-- One full Bott block: one bit in every phase slot of the clock. -/
abbrev BottBlock (kind : BottKind) : Type :=
  BottPhase kind → Bool

/-- A finite Bott-periodic Cantor word of depth `n`. -/
abbrev BottWord (kind : BottKind) (n : ℕ) : Type :=
  Fin n → BottBlock kind

/-- The infinite Bott-periodic Cantor boundary. -/
abbrev BottBoundary (kind : BottKind) : Type :=
  ℕ → BottBlock kind

/-- Read the bit in phase `phase` of a block. -/
def blockBit {kind : BottKind}
    (block : BottBlock kind)
    (phase : BottPhase kind) : Bool :=
  block phase

/-- Read the bit at depth `i` and phase `phase` of a finite Bott word. -/
def wordBit {kind : BottKind} {n : ℕ}
    (word : BottWord kind n)
    (i : Fin n)
    (phase : BottPhase kind) : Bool :=
  word i phase

/-- Read the stream indexed by one Bott phase. -/
def phaseStream {kind : BottKind}
    (boundary : BottBoundary kind)
    (phase : BottPhase kind) : ℕ → Bool :=
  fun n => boundary n phase

/--
Extend a finite Bott word by one full Bott block.

The Lean cast is kept inside this definition; downstream modules should use the
definition rather than reimplementing length transport.
-/
def extendWord {kind : BottKind} {n : ℕ}
    (word : BottWord kind n)
    (block : BottBlock kind) :
    BottWord kind (n + 1) :=
  fun i =>
    if h : (i : ℕ) < n then
      word ⟨i, h⟩
    else
      block

@[simp] theorem extendWord_last {kind : BottKind} {n : ℕ}
    (word : BottWord kind n)
    (block : BottBlock kind) :
    extendWord word block ⟨n, Nat.lt_succ_self n⟩ = block := by
  simp [extendWord]

theorem extendWord_cast {kind : BottKind} {n : ℕ}
    (word : BottWord kind n)
    (block : BottBlock kind)
    (i : Fin n) :
    extendWord word block ⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩ = word i := by
  simp [extendWord, i.isLt]

/-! ## 2. Bott-periodic random walks and entropy readouts -/

/--
A Bott-periodic random walk on multi-stream Cantor words.

At each depth the walk chooses one full Bott block, i.e. one bit for each
parallel stream.
-/

def IsBottPeriodicRandomWalk
    {kind : BottKind}
    (transitionWeight :
      ∀ n : ℕ, BottWord kind n → BottBlock kind → ℝ) : Prop :=
  (∀ (n : ℕ) (word : BottWord kind n) (block : BottBlock kind),
    0 ≤ transitionWeight n word block) ∧
  (∀ (n : ℕ) (word : BottWord kind n),
    Finset.univ.sum
      (fun block : BottBlock kind => transitionWeight n word block) = 1)

def localBlockEntropy
    {kind : BottKind}
    (transitionWeight :
      ∀ n : ℕ, BottWord kind n → BottBlock kind → ℝ)
    (n : ℕ) (word : BottWord kind n) : ℝ :=
  - Finset.univ.sum
      (fun block : BottBlock kind =>
        let p := transitionWeight n word block
        if p = 0 then 0 else p * Real.log p)

theorem localBlockEntropy_nonnegative
    {kind : BottKind}
    (transitionWeight :
      ∀ n : ℕ, BottWord kind n → BottBlock kind → ℝ)
    (h : IsBottPeriodicRandomWalk transitionWeight)
    (n : ℕ) (word : BottWord kind n) :
    0 ≤ localBlockEntropy transitionWeight n word := by
  unfold localBlockEntropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro block hblock
  dsimp
  split_ifs with hp
  · simp
  · have hnonneg : 0 ≤ transitionWeight n word block :=
      h.1 n word block
    have hle : transitionWeight n word block ≤ 1 := by
      calc
        transitionWeight n word block ≤
            Finset.univ.sum (fun b : BottBlock kind =>
              transitionWeight n word b) :=
          Finset.single_le_sum
            (fun b hb => h.1 n word b) hblock
        _ = 1 := h.2 n word
    exact mul_nonpos_of_nonneg_of_nonpos hnonneg
      (Real.log_nonpos hnonneg hle)

def couplingReadout
    {kind : BottKind}
    (jointEntropy : ℝ)
    (streamEntropy : BottPhase kind → ℝ) : ℝ :=
  jointEntropy -
    Finset.univ.sum (fun phase : BottPhase kind => streamEntropy phase)

def IsBottPeriodicCantorEntropy
    {kind : BottKind}
    (transitionWeight :
      ∀ n : ℕ, BottWord kind n → BottBlock kind → ℝ)
    (depthEntropy : ℕ → ℝ) : Prop :=
  IsBottPeriodicRandomWalk transitionWeight ∧
  ∀ n : ℕ, 0 ≤ depthEntropy n

noncomputable def bottSplitStep (towerIndex : ℕ) :=
  InfoGeometry.Clifford.BottPeriodicity.splitBottStep towerIndex

theorem splitStep_eq_owner (towerIndex : ℕ) :
    bottSplitStep towerIndex =
      InfoGeometry.Clifford.BottPeriodicity.splitBottStep towerIndex :=
  rfl

theorem block_periodicity (towerIndex : ℕ) :
    Function.Bijective (bottSplitStep towerIndex) :=
  (bottSplitStep towerIndex).bijective

theorem matrix_amplification
    (towerIndex : ℕ)
    (x y :
      InfoGeometry.Clifford.BottPeriodicity.SplitBottClifford
        (towerIndex + 1)) :
    bottSplitStep towerIndex (x * y) =
      bottSplitStep towerIndex x * bottSplitStep towerIndex y :=
  map_mul (bottSplitStep towerIndex) x y

/- The Fierz--Klein law is a direct proposition on readout data. -/
def BottPeriodicFierzKleinLaw
    (coords : FractalCantorFockWitness.FierzChannel → ℝ)
    (residual : (FractalCantorFockWitness.FierzChannel → ℝ) → ℝ) : Prop :=
  residual coords = 0

end InfoGeometry.Topology.BottPeriodicCantorEntropyGraph
