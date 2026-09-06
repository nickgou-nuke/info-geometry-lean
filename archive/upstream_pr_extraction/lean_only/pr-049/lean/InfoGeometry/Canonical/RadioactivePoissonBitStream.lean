import Mathlib.Tactic
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Meta.Architecture

/-!
# Radioactive Poisson bit streams

Physical source data for primordial bit streams.

This file records the theorem-safe dictionary:

```text
radioactive decay
  -> Poisson window counts
  -> parity bits
  -> optional von Neumann extraction
  -> spinor bit streams
  -> centered covariance calibration
  -> Clifford quadratic-form data.
```

The stochastic laws are not proved here.  They are stored as explicit
calibration/property packets.  In particular, independence of time windows
and the Poisson odd-count formula are not silently converted into theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.RadioactivePoissonBitStream

open scoped BigOperators

@[rep_depth projective]
def decayBit (k : ℕ) : Bool :=
  decide (k % 2 = 1)

@[simp, rep_depth projective]
theorem decayBit_eq_true_iff (k : ℕ) :
    decayBit k = true ↔ k % 2 = 1 := by
  simp [decayBit]

@[simp, rep_depth projective]
theorem decayBit_eq_false_iff (k : ℕ) :
    decayBit k = false ↔ k % 2 ≠ 1 := by
  simp [decayBit]

/-- Bit stream obtained from radioactive decay counts by parity. -/
@[rep_depth projective]
def radioactiveBitStream (counts : ℕ → ℕ) : ℕ → Bool :=
  fun n => decayBit (counts n)

@[simp, rep_depth projective]
theorem radioactiveBitStream_apply
    (counts : ℕ → ℕ) (n : ℕ) :
    radioactiveBitStream counts n = decayBit (counts n) := by
  rfl

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

@[simp, rep_depth projective]
theorem vonNeumannPair_discard_iff (a b : Bool) :
    vonNeumannPair a b = ExtractedBit.discard ↔ a = b := by
  cases a <;> cases b <;> simp [vonNeumannPair]

@[simp, rep_depth projective]
theorem vonNeumannPair_bit_false :
    vonNeumannPair false true = ExtractedBit.bit false := by
  rfl

@[simp, rep_depth projective]
theorem vonNeumannPair_bit_true :
    vonNeumannPair true false = ExtractedBit.bit true := by
  rfl

/-- Apply the pair extractor to consecutive pairs of a stream. -/
@[rep_depth projective]
def vonNeumannExtractedStream (s : ℕ → Bool) : ℕ → ExtractedBit :=
  fun n => vonNeumannPair (s (2 * n)) (s (2 * n + 1))

/-- Boolean bit as a real readout. -/
@[rep_depth projective]
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0

@[simp, rep_depth projective]
theorem boolToReal_eq_zero_iff (b : Bool) :
    boolToReal b = 0 ↔ b = false := by
  cases b <;> simp [boolToReal]

@[simp, rep_depth projective]
theorem boolToReal_eq_one_iff (b : Bool) :
    boolToReal b = 1 ↔ b = true := by
  cases b <;> simp [boolToReal]

@[rep_depth projective]
theorem boolToReal_nonneg (b : Bool) :
    0 ≤ boolToReal b := by
  cases b <;> simp [boolToReal]

@[rep_depth projective]
theorem boolToReal_le_one (b : Bool) :
    boolToReal b ≤ 1 := by
  cases b <;> simp [boolToReal]

/-- Empirical mean signal of the first `N` bits. -/
@[rep_depth projective]
def empiricalBitSignal (s : ℕ → Bool) (N : ℕ) : ℝ :=
  if _h : N = 0 then
    0
  else
    (Finset.range N).sum (fun n => boolToReal (s n)) / (N : ℝ)

@[simp, rep_depth projective]
theorem empiricalBitSignal_zero (s : ℕ → Bool) :
    empiricalBitSignal s 0 = 0 := by
  simp [empiricalBitSignal]

@[rep_depth projective]
theorem empiricalBitSignal_nonneg
    (s : ℕ → Bool) {N : ℕ} (hN : 0 < N) :
    0 ≤ empiricalBitSignal s N := by
  rw [empiricalBitSignal, dif_neg (Nat.ne_of_gt hN)]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun n _ => boolToReal_nonneg (s n))
  · exact_mod_cast hN.le

@[rep_depth projective]
theorem empiricalBitSignal_le_one
    (s : ℕ → Bool) {N : ℕ} (hN : 0 < N) :
    empiricalBitSignal s N ≤ 1 := by
  rw [empiricalBitSignal, dif_neg (Nat.ne_of_gt hN)]
  apply (div_le_iff₀ (by exact_mod_cast hN)).mpr
  calc
    (Finset.range N).sum (fun n => boolToReal (s n)) ≤
        (Finset.range N).sum (fun _ => (1 : ℝ)) := by
      exact Finset.sum_le_sum (fun n _ => boolToReal_le_one (s n))
    _ = (N : ℝ) := by
      simp
    _ ≤ 1 * (N : ℝ) := by
      simp

@[simp, rep_depth projective]
theorem poissonOddProb_zero :
    poissonOddProb 0 = 0 := by
  simp [poissonOddProb]

@[rep_depth projective]
theorem poissonOddProb_nonneg {μ : ℝ} (hμ : 0 ≤ μ) :
    0 ≤ poissonOddProb μ := by
  have h_exp : Real.exp (-2 * μ) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  exact div_nonneg (sub_nonneg.mpr h_exp) (by norm_num)

@[rep_depth projective]
theorem poissonOddProb_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < poissonOddProb μ := by
  have h_exp : Real.exp (-2 * μ) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  exact div_pos (sub_pos.mpr h_exp) (by norm_num)

@[rep_depth projective]
theorem poissonOddProb_le_one (μ : ℝ) :
    poissonOddProb μ ≤ 1 := by
  have h_exp : 0 ≤ Real.exp (-2 * μ) := Real.exp_nonneg _
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith

@[rep_depth projective]
theorem poissonOddProb_lt_one {μ : ℝ} :
    poissonOddProb μ < 1 := by
  have h_exp : 0 < Real.exp (-2 * μ) := Real.exp_pos _
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith

@[rep_depth projective]
theorem centeredBit_denominator_pos
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) := by
  apply Real.sqrt_pos.2
  exact mul_pos hp0 (sub_pos.mpr hp1)

/-- Finite binary prefix of a bit stream as the repo's Cantor `BinaryWord`. -/
@[rep_depth projective]
def streamPrefix (s : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => streamPrefix s n ++ [s n]

@[simp, rep_depth projective]
theorem streamPrefix_zero (s : ℕ → Bool) :
    streamPrefix s 0 = [] := by
  rfl

@[simp, rep_depth projective]
theorem streamPrefix_succ (s : ℕ → Bool) (n : ℕ) :
    streamPrefix s (n + 1) = streamPrefix s n ++ [s n] := by
  rfl

/-- A finite stream prefix is the child of the previous prefix. -/
@[simp, rep_depth projective]
theorem streamPrefix_child (s : ℕ → Bool) (n : ℕ) :
    streamPrefix s (n + 1) =
      TypeIIIModularCantorSystem.child (streamPrefix s n) (s n) := by
  simp [streamPrefix, TypeIIIModularCantorSystem.child]

/-- Stream prefixes have the expected finite length. -/
@[simp, rep_depth projective]
theorem streamPrefix_length (s : ℕ → Bool) (n : ℕ) :
    (streamPrefix s n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [streamPrefix, ih]

/-- A longer stream prefix always lies in the closed cylinder of any earlier prefix. -/
@[rep_depth projective]
theorem streamPrefix_mem_closedCylinder_of_le (s : ℕ → Bool) (m n : ℕ) (h : m ≤ n) :
    streamPrefix s n ∈ TypeIIIModularCantorSystem.closedCylinder (streamPrefix s m) := by
  refine Nat.le_induction
    (m := m)
    (P := fun t _ =>
      streamPrefix s t ∈ TypeIIIModularCantorSystem.closedCylinder (streamPrefix s m))
    ?base ?succ n h
  · refine ⟨[], ?_⟩
    simp
  · intro t hmt ih
    rcases ih with ⟨u, hu⟩
    refine ⟨u ++ [s t], ?_⟩
    simp [streamPrefix, hu, List.append_assoc]

/-- Each new stream prefix extends the previous prefix by one bit. -/
@[rep_depth projective]
theorem streamPrefix_mem_closedCylinder_succ (s : ℕ → Bool) (n : ℕ) :
    streamPrefix s (n + 1) ∈ TypeIIIModularCantorSystem.closedCylinder (streamPrefix s n) := by
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
  counts : ℕ → ℕ
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
def bitstream : ℕ → Bool :=
  radioactiveBitStream ch.counts

/-- The odd-count probability predicted by the ideal Poisson model. -/
@[rep_depth projective]
def idealOddProbability : ℝ :=
  poissonOddProb ch.mean

@[rep_depth projective]
theorem mean_nonneg : 0 ≤ ch.mean := by
  exact mul_nonneg ch.rate_nonneg (le_of_lt ch.window_pos)

@[rep_depth projective]
theorem idealOddProbability_nonneg :
    0 ≤ ch.idealOddProbability := by
  exact poissonOddProb_nonneg ch.mean_nonneg

@[rep_depth projective]
theorem idealOddProbability_le_one :
    ch.idealOddProbability ≤ 1 := by
  exact poissonOddProb_le_one ch.mean

end RadioactiveDecayChannel

/-- Centered and variance-normalized bit readout for a Bernoulli probability `p`. -/
@[rep_depth projective]
def centeredBit (p : ℝ) (s : ℕ → Bool) (n : ℕ) : ℝ :=
  (boolToReal (s n) - p) / Real.sqrt (p * (1 - p))

/-- Kronecker delta on four spinor channels as a real covariance target. -/
@[rep_depth projective]
def deltaFin4 (i j : Fin 4) : ℝ :=
  if i = j then 1 else 0

@[simp, rep_depth projective]
theorem deltaFin4_self (i : Fin 4) :
    deltaFin4 i i = 1 := by
  simp [deltaFin4]

@[simp, rep_depth projective]
theorem deltaFin4_ne {i j : Fin 4} (hij : i ≠ j) :
    deltaFin4 i j = 0 := by
  simp [deltaFin4, hij]

/--
Centered covariance calibration for four independent channels.

This explicitly records the statistical bridge:

```text
Poisson independence + centering/normalization
  -> diagonal covariance
  -> Clifford quadratic-form data.
```
-/
@[rep_depth projective]
theorem centered_calibration_eq
    (S : Fin 4 → ℕ → Bool)
    (centered : Fin 4 → ℕ → ℝ)
    (covariance : Fin 4 → Fin 4 → ℝ)
    (hcentered :
      ∀ i n, centered i n = centeredBit (covariance i i) (S i) n)
    (i : Fin 4) (n : ℕ) :
    centered i n = centeredBit (covariance i i) (S i) n :=
  hcentered i n

/--
Readback: an independent centered spinor calibration has diagonal covariance.

This is a calibration-field readout, not a probabilistic limit theorem.
-/
@[rep_depth projective]
theorem covariance_eq_clifford_delta
    (S : Fin 4 → ℕ → Bool)
    (covariance : Fin 4 → Fin 4 → ℝ)
    (hcovariance :
      ∀ i j, covariance i j = deltaFin4 i j)
    (i j : Fin 4) :
    covariance i j = deltaFin4 i j :=
  hcovariance i j

end InfoGeometry.Canonical.RadioactivePoissonBitStream
