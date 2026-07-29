import Mathlib.Tactic
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

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
@[rep_depth transport]
structure BottPeriodicRandomWalk (kind : BottKind) where
  transitionWeight :
    ∀ n : ℕ, BottWord kind n → BottBlock kind → ℝ

  nonnegative :
    ∀ (n : ℕ) (word : BottWord kind n) (block : BottBlock kind),
      0 ≤ transitionWeight n word block

  row_sum_one :
    ∀ (n : ℕ) (word : BottWord kind n),
      Finset.univ.sum
        (fun block : BottBlock kind => transitionWeight n word block) = 1

namespace BottPeriodicRandomWalk

variable {kind : BottKind}
variable (R : BottPeriodicRandomWalk kind)

/-- One-step block entropy at a finite Bott word. -/
def localBlockEntropy (n : ℕ) (word : BottWord kind n) : ℝ :=
  - Finset.univ.sum
      (fun block : BottBlock kind =>
        let p := R.transitionWeight n word block
        if p = 0 then 0 else p * Real.log p)

/-- Row normalization readback. -/
@[rep_depth transport]
theorem transition_sum_one (n : ℕ) (word : BottWord kind n) :
    Finset.univ.sum
      (fun block : BottBlock kind => R.transitionWeight n word block) = 1 :=
  R.row_sum_one n word

/-- Transition nonnegativity readback. -/
@[rep_depth transport]
theorem transition_nonnegative
    (n : ℕ) (word : BottWord kind n) (block : BottBlock kind) :
    0 ≤ R.transitionWeight n word block :=
  R.nonnegative n word block

end BottPeriodicRandomWalk

/--
Entropy coupling between the Bott streams at one finite stage.

`jointEntropy` is the entropy of full Bott blocks.  `streamEntropy phase` is the
entropy readout assigned to an individual stream.  The coupling is their
non-additive residual.
-/
@[rep_depth transport]
structure BottStreamEntropyCoupling (kind : BottKind) where
  jointEntropy : ℝ
  streamEntropy : BottPhase kind → ℝ

namespace BottStreamEntropyCoupling

variable {kind : BottKind}
variable (C : BottStreamEntropyCoupling kind)

/-- Non-additive residual between joint and single-stream entropy readouts. -/
def couplingReadout : ℝ :=
  C.jointEntropy -
    Finset.univ.sum (fun phase : BottPhase kind => C.streamEntropy phase)

/-- Coupling is the non-additive residual between joint and stream entropies. -/
@[rep_depth transport]
theorem coupling_eq_joint_sub_streams_readout :
    C.couplingReadout =
      C.jointEntropy - Finset.univ.sum (fun phase : BottPhase kind => C.streamEntropy phase) :=
  rfl

end BottStreamEntropyCoupling

/--
Entropy packet for a Bott-periodic Cantor boundary.

The entropy values are supplied as readouts because proving nonnegativity and
entropy-rate convergence depends on the chosen Markov/dynamical model.
-/
@[rep_depth transport]
structure BottPeriodicCantorEntropyPacket (kind : BottKind) where
  walk : BottPeriodicRandomWalk kind

  depthEntropy : ℕ → ℝ
  entropy_nonnegative : ∀ n : ℕ, 0 ≤ depthEntropy n

  coupling : ℕ → BottStreamEntropyCoupling kind

namespace BottPeriodicCantorEntropyPacket

variable {kind : BottKind}
variable (P : BottPeriodicCantorEntropyPacket kind)

/-- Entropy nonnegativity is part of the selected entropy model. -/
@[rep_depth transport]
theorem depth_entropy_nonnegative (n : ℕ) :
    0 ≤ P.depthEntropy n :=
  P.entropy_nonnegative n

/-- The coupling law at depth `n`. -/
@[rep_depth transport]
theorem coupling_eq_joint_sub_streams_readout (n : ℕ) :
    (P.coupling n).couplingReadout =
      (P.coupling n).jointEntropy -
        Finset.univ.sum
          (fun phase : BottPhase kind => (P.coupling n).streamEntropy phase) :=
  (P.coupling n).coupling_eq_joint_sub_streams_readout

end BottPeriodicCantorEntropyPacket

/-! ## 3. Bott-periodic Clifford and It-from-bit sockets -/

/--
Clifford/CAR block data attached to a Bott clock.

The phase-indexed operators are calibrated to the repository-owned split
Clifford Bott step.  The witness is an actual algebra equivalence.
-/
@[rep_depth operator]
structure BottPeriodicCliffordPacket
    (kind : BottKind)
    (Op : Type*) [Ring Op] where
  gamma : BottPhase kind → Op
  towerIndex : ℕ

namespace BottPeriodicCliffordPacket

variable {kind : BottKind} {Op : Type*} [Ring Op]

/-- The Bott step is derived from its canonical Clifford-periodicity owner. -/
noncomputable def splitStep
    (C : BottPeriodicCliffordPacket kind Op) :=
  InfoGeometry.Clifford.BottPeriodicity.splitBottStep C.towerIndex

/-- The derived Bott step is definitionally the canonical owner equivalence. -/
@[simp]
theorem splitStep_eq_owner
    (C : BottPeriodicCliffordPacket kind Op) :
    C.splitStep =
      InfoGeometry.Clifford.BottPeriodicity.splitBottStep C.towerIndex :=
  rfl

/--
Block periodicity is the bijectivity of the native split Bott algebra
equivalence, not a stored proposition.
-/
@[rep_depth operator]
theorem block_periodicity
    (C : BottPeriodicCliffordPacket kind Op) :
    Function.Bijective C.splitStep :=
  C.splitStep.bijective

/--
The graded `Cl(1,1)` amplification preserves multiplication through the native
split Bott algebra equivalence.
-/
@[rep_depth operator]
theorem matrix_amplification
    (C : BottPeriodicCliffordPacket kind Op)
    (x y :
      InfoGeometry.Clifford.BottPeriodicity.SplitBottClifford
        (C.towerIndex + 1)) :
    C.splitStep (x * y) = C.splitStep x * C.splitStep y :=
  map_mul C.splitStep x y

end BottPeriodicCliffordPacket

/--
Bott-periodic It-from-bit socket.

The "bit" side is the Bott-periodic Cantor entropy packet.  The "it" side is
the Drazin-Hodge envelope of a bit-derived operator.
-/
@[socket_debt_tag, rep_depth operator]
structure BottPeriodicItFromBitSocket
    (Op : Type*) [Ring Op] where
  kind : BottKind

  entropyBoundary : BottPeriodicCantorEntropyPacket kind
  cliffordBlock : BottPeriodicCliffordPacket kind Op

  A : Op
  AD : Op

  L : Op
  LD : Op

  xRaw : Op

namespace BottPeriodicItFromBitSocket

variable {Op : Type*} [Ring Op]
variable (S : BottPeriodicItFromBitSocket Op)

/-- Support expression generated by the operator and its chosen Drazin partner. -/
def pA : Op :=
  S.A * S.AD

@[simp]
theorem pA_def :
    S.pA = S.A * S.AD :=
  rfl

/-- Harmonic complement expression generated by `L` and `LD`. -/
def HL : Op :=
  1 - S.L * S.LD

@[simp]
theorem HL_def :
    S.HL = 1 - S.L * S.LD :=
  rfl

/-- Noncommutative It-from-bit compression into the harmonic support. -/
def xIt : Op :=
  S.HL * (S.pA * S.xRaw * S.pA) * S.HL

@[simp]
theorem xIt_def :
    S.xIt = S.HL * (S.pA * S.xRaw * S.pA) * S.HL :=
  rfl

end BottPeriodicItFromBitSocket

/--
Fierz-Klein law for a Bott-periodic It-from-bit socket.

The residual is abstract because different downstream files choose different
Fierz coordinate systems.  The theorem-owned statement here is that the chosen
readout lies on its declared quadric.
-/
@[rep_depth operator]
structure BottPeriodicFierzKleinLaw
    (Op : Type*) [Ring Op] where
  socket : BottPeriodicItFromBitSocket Op
  coords : FractalCantorFockWitness.FierzChannel → ℝ
  residual : (FractalCantorFockWitness.FierzChannel → ℝ) → ℝ
  quadric_zero_property : residual coords = 0

namespace BottPeriodicFierzKleinLaw

variable {Op : Type*} [Ring Op]
variable (L : BottPeriodicFierzKleinLaw Op)

/-- The state-measured Fierz readout lies on the chosen Klein/Fierz quadric. -/
@[rep_depth operator]
  theorem quadric_zero :
    L.residual L.coords = 0 :=
  L.quadric_zero_property

end BottPeriodicFierzKleinLaw

end InfoGeometry.Topology.BottPeriodicCantorEntropyGraph
