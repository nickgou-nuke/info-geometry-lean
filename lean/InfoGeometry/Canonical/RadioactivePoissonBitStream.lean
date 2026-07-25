import Mathlib.Tactic
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget

/-!
# Radioactive Poisson bit streams

Physical source socket for primordial bit streams.

This file records the theorem-safe dictionary:

```text
radioactive decay
  -> Poisson window counts
  -> parity bits
  -> optional von Neumann extraction
  -> spinor socket bit streams
  -> centered covariance calibration
  -> Clifford quadratic-form socket.
```

The stochastic laws are not proved here.  They are stored as explicit
calibration/assumption packets.  In particular, independence of time windows
and the Poisson odd-count formula are not silently converted into theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.RadioactivePoissonBitStream

open scoped BigOperators

/-- Infinite bit stream. No probability law is built into this type. -/
@[rep_depth projective]
abbrev BitStream : Type :=
  ℕ → Bool

/-- Counts of radioactive decay events in discrete time windows. -/
@[rep_depth projective]
abbrev DecayCountStream : Type :=
  ℕ → ℕ

/-- Raw parity bit emitted by a count window. -/
@[rep_depth projective]
def decayBit (k : ℕ) : Bool :=
  decide (k % 2 = 1)

/-- Bit stream obtained from radioactive decay counts by parity. -/
@[rep_depth projective]
def radioactiveBitStream (counts : DecayCountStream) : BitStream :=
  fun n => decayBit (counts n)

/-- Mean probability of an odd Poisson count with parameter `μ`. -/
@[rep_depth projective]
def poissonOddProb (μ : ℝ) : ℝ :=
  (1 - Real.exp (-2 * μ)) / 2

/-- Extractor output for one pair of raw bits. -/
@[rep_depth projective]
inductive ExtractedBit where
  | bit : Bool → ExtractedBit
  | discard : ExtractedBit
  deriving DecidableEq

/--
Von Neumann pair extractor:

* `01 ↦ 0`;
* `10 ↦ 1`;
* `00` and `11` are discarded.
-/
@[rep_depth projective]
def vonNeumannPair (a b : Bool) : ExtractedBit :=
  match a, b with
  | false, true => ExtractedBit.bit false
  | true, false => ExtractedBit.bit true
  | _, _ => ExtractedBit.discard

/-- Apply the pair extractor to consecutive pairs of a stream. -/
@[rep_depth projective]
def vonNeumannExtractedStream (s : BitStream) : ℕ → ExtractedBit :=
  fun n => vonNeumannPair (s (2 * n)) (s (2 * n + 1))

/-- Boolean bit as a real readout. -/
@[rep_depth projective]
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Empirical mean signal of the first `N` bits. -/
@[rep_depth projective]
def empiricalBitSignal (s : BitStream) (N : ℕ) : ℝ :=
  if _h : N = 0 then
    0
  else
    (Finset.range N).sum (fun n => boolToReal (s n)) / (N : ℝ)

/-- Finite binary prefix of a bit stream as the repo's Cantor `BinaryWord`. -/
@[rep_depth projective]
def streamPrefix (s : BitStream) : ℕ → TypeIIIModularCantorSystem.BinaryWord
  | 0 => []
  | n + 1 => streamPrefix s n ++ [s n]

@[simp, rep_depth projective]
theorem streamPrefix_zero (s : BitStream) :
    streamPrefix s 0 = [] := by
  rfl

@[simp, rep_depth projective]
theorem streamPrefix_succ (s : BitStream) (n : ℕ) :
    streamPrefix s (n + 1) = streamPrefix s n ++ [s n] := by
  rfl

/-- A finite stream prefix is the child of the previous prefix. -/
@[simp, rep_depth projective]
theorem streamPrefix_child (s : BitStream) (n : ℕ) :
    streamPrefix s (n + 1) =
      TypeIIIModularCantorSystem.BinaryWord.child (streamPrefix s n) (s n) := by
  simp [streamPrefix, TypeIIIModularCantorSystem.BinaryWord.child]

/-- Stream prefixes have the expected finite length. -/
@[simp, rep_depth projective]
theorem streamPrefix_length (s : BitStream) (n : ℕ) :
    (streamPrefix s n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [streamPrefix, ih]

/-- A longer stream prefix always lies in the closed cylinder of any earlier prefix. -/
@[rep_depth projective]
theorem streamPrefix_mem_closedCylinder_of_le (s : BitStream) (m n : ℕ) (h : m ≤ n) :
    streamPrefix s n ∈ TypeIIIModularCantorSystem.BinaryWord.closedCylinder (streamPrefix s m) := by
  refine Nat.le_induction
    (m := m)
    (P := fun t _ =>
      streamPrefix s t ∈ TypeIIIModularCantorSystem.BinaryWord.closedCylinder (streamPrefix s m))
    ?base ?succ n h
  · refine ⟨[], ?_⟩
    simp [TypeIIIModularCantorSystem.BinaryWord.closedCylinder]
  · intro t hmt ih
    rcases ih with ⟨u, hu⟩
    refine ⟨u ++ [s t], ?_⟩
    simp [TypeIIIModularCantorSystem.BinaryWord.closedCylinder, streamPrefix, hu, List.append_assoc]

/-- Each new stream prefix extends the previous prefix by one bit. -/
@[rep_depth projective]
theorem streamPrefix_mem_closedCylinder_succ (s : BitStream) (n : ℕ) :
    streamPrefix s (n + 1) ∈ TypeIIIModularCantorSystem.BinaryWord.closedCylinder (streamPrefix s n) := by
  simpa using (streamPrefix_mem_closedCylinder_of_le (s := s) n (n + 1) (Nat.le_succ n))

/--
A radioactive decay channel is a Poissonian count source.

The rate/window fields are physical parameters.  The actual stochastic law is
not asserted by the structure.
-/
@[rep_depth projective]
structure RadioactiveDecayChannel where
  rate : ℝ
  window : ℝ
  counts : DecayCountStream
  rate_nonneg : 0 ≤ rate
  window_pos : 0 < window

namespace RadioactiveDecayChannel

variable (ch : RadioactiveDecayChannel)

/-- Window mean `μ = λ Δ`. -/
@[rep_depth projective]
def mean : ℝ :=
  ch.rate * ch.window

/-- Raw parity bit stream of the decay channel. -/
@[rep_depth projective]
def bitstream : BitStream :=
  radioactiveBitStream ch.counts

/-- The odd-count probability predicted by the ideal Poisson model. -/
@[rep_depth projective]
def idealOddProbability : ℝ :=
  poissonOddProb ch.mean

end RadioactiveDecayChannel

/--
Calibration assumption that a channel's parity bit has the ideal Poisson
odd-count probability.

This is assumption data, not a theorem derived from `counts`.
-/
@[rep_depth projective]
structure ParityPoissonCalibrationAssumption
    (ch : RadioactiveDecayChannel) where
  oddProbability : ℝ
  oddProbability_eq_poisson :
    oddProbability = ch.idealOddProbability

/-- Four raw bit streams used as a stochastic spinor socket. -/
@[socket_debt_tag, rep_depth projective]
structure SpinorSocket where
  streams : Fin 4 → BitStream

/-- Four independent radioactive decay channels for a spinor socket. -/
@[socket_debt_tag, rep_depth projective]
structure RadioactiveSpinorSocket where
  channels : Fin 4 → RadioactiveDecayChannel

/-- Convert four radioactive channels to four parity-bit streams. -/
@[rep_depth projective]
def RadioactiveSpinorSocket.toSpinorSocket
    (rss : RadioactiveSpinorSocket) : SpinorSocket where
  streams i := (rss.channels i).bitstream

/-- Centered and variance-normalized bit readout for a Bernoulli probability `p`. -/
@[rep_depth projective]
def centeredBit (p : ℝ) (s : BitStream) (n : ℕ) : ℝ :=
  (boolToReal (s n) - p) / Real.sqrt (p * (1 - p))

/-- Kronecker delta on four spinor channels as a real covariance target. -/
@[rep_depth projective]
def deltaFin4 (i j : Fin 4) : ℝ :=
  if i = j then 1 else 0

/--
Centered covariance calibration for four independent channels.

This explicitly records the statistical bridge:

```text
Poisson independence + centering/normalization
  -> diagonal covariance
  -> Clifford quadratic-form socket.
```
-/
@[rep_depth projective]
structure IndependentCenteredSpinorCalibration
    (S : SpinorSocket) where
  centered : Fin 4 → ℕ → ℝ
  covariance : Fin 4 → Fin 4 → ℝ
  centered_eq :
    ∀ i n, centered i n = centeredBit (covariance i i) (S.streams i) n
  covariance_eq_delta :
    ∀ i j, covariance i j = deltaFin4 i j

/--
Readback: an independent centered spinor calibration has diagonal covariance.

This is a calibration-field readout, not a probabilistic limit theorem.
-/
@[bridge_target_tag, rep_depth projective]
theorem covariance_eq_clifford_delta
    (S : SpinorSocket)
    (C : IndependentCenteredSpinorCalibration S)
    (i j : Fin 4) :
    C.covariance i j = deltaFin4 i j :=
  C.covariance_eq_delta i j

/-- Owner target for radioactive spinor sockets. -/
@[rep_depth projective]
def RadioactiveSpinorSocketTarget : Prop :=
  Nonempty RadioactiveSpinorSocket

/-- Constructor for the radioactive spinor socket target. -/
@[rep_depth projective]
theorem constructRadioactiveSpinorSocketTarget
    (rss : RadioactiveSpinorSocket) :
    RadioactiveSpinorSocketTarget :=
  ⟨rss⟩

end InfoGeometry.Canonical.RadioactivePoissonBitStream
