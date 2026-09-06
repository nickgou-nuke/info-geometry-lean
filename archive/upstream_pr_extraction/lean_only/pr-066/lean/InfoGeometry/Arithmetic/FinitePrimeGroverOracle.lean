import Mathlib.Tactic
import InfoGeometry.Arithmetic.GenuineBounds

/-!
# InfoGeometry.Arithmetic.FinitePrimeGroverOracle

Finite Grover-oracle layer for prime-state algorithms.

This file formalizes the conservative algebraic core of a primality phase
oracle:

* a marked predicate on a finite register support;
* the real phase sign `-1` on marked states and `+1` otherwise;
* the phase oracle is involutive;
* the finite squared amplitude norm is preserved;
* marked and unmarked supports split the finite register.

No claim is made here about an implemented primality test, Grover complexity,
quantum counting accuracy, analytic prime-number estimates, or RH.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.FinitePrimeGroverOracle

/-! ## 1. Finite phase oracle -/

/-- Real phase sign of a marked item. -/
def phaseSign
    {α : Type*}
    (marked : α → Prop) [DecidablePred marked]
    (a : α) : ℝ :=
  if marked a then -1 else 1

lemma phaseSign_ne_zero
    {α : Type*} (marked : α → Prop) [DecidablePred marked] (a : α) :
    phaseSign marked a ≠ 0 := by
  by_cases h : marked a <;> simp [phaseSign, h]

/-- Phase sign squares to `1`. -/
@[simp]
theorem phaseSign_sq
    {α : Type*}
    (marked : α → Prop) [DecidablePred marked]
    (a : α) :
    phaseSign marked a ^ 2 = 1 := by
  by_cases h : marked a <;> simp [phaseSign, h]

/--
Real phase oracle on amplitudes.

Marked basis elements receive a sign flip; unmarked elements are unchanged.
-/
def phaseOracle
    {α : Type*}
    (marked : α → Prop) [DecidablePred marked]
    (amp : α → ℝ) : α → ℝ :=
  fun a => phaseSign marked a * amp a

/-- The phase oracle is an involution. -/
@[simp]
theorem phaseOracle_phaseOracle
    {α : Type*}
    (marked : α → Prop) [DecidablePred marked]
    (amp : α → ℝ) :
    phaseOracle marked (phaseOracle marked amp) = amp := by
  funext a
  by_cases h : marked a <;> simp [phaseOracle, phaseSign, h]

/-- Finite squared amplitude norm on a support. -/
def finiteAmplitudeNormSq
    {α : Type*}
    (A : Finset α)
    (amp : α → ℝ) : ℝ :=
  ∑ a ∈ A, amp a ^ 2

lemma finiteAmplitudeNormSq_nonneg
    {α : Type*} (A : Finset α) (amp : α → ℝ) :
    0 ≤ finiteAmplitudeNormSq A amp := by
  unfold finiteAmplitudeNormSq
  exact Finset.sum_nonneg (fun a _ha => sq_nonneg (amp a))

lemma finiteAmplitudeNormSq_phaseOracle_nonneg
    {α : Type*} (A : Finset α)
    (marked : α → Prop) [DecidablePred marked]
    (amp : α → ℝ) :
    0 ≤ finiteAmplitudeNormSq A (phaseOracle marked amp) :=
  finiteAmplitudeNormSq_nonneg A (phaseOracle marked amp)

/-- The phase oracle preserves the finite squared amplitude norm. -/
theorem finiteAmplitudeNormSq_phaseOracle
    {α : Type*}
    (A : Finset α)
    (marked : α → Prop) [DecidablePred marked]
    (amp : α → ℝ) :
    finiteAmplitudeNormSq A (phaseOracle marked amp) =
      finiteAmplitudeNormSq A amp := by
  unfold finiteAmplitudeNormSq phaseOracle
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases h : marked a <;> simp [phaseSign, h, pow_two]

/-! ## 2. Marked/unmarked finite support split -/

/-- Number of marked basis elements in a finite support. -/
def markedCount
    {α : Type*}
    (A : Finset α)
    (marked : α → Prop) [DecidablePred marked] : ℕ :=
  (A.filter marked).card

/-- Number of unmarked basis elements in a finite support. -/
def unmarkedCount
    {α : Type*}
    (A : Finset α)
    (marked : α → Prop) [DecidablePred marked] : ℕ :=
  (A.filter fun a => ¬ marked a).card

/-- Marked and unmarked counts split the finite support. -/
theorem markedCount_add_unmarkedCount
    {α : Type*}
    (A : Finset α)
    (marked : α → Prop) [DecidablePred marked] :
    markedCount A marked + unmarkedCount A marked = A.card := by
  unfold markedCount unmarkedCount
  exact Finset.card_filter_add_card_filter_not (s := A) (p := marked)

/-! ## 3. Prime-oracle and quantum-counting layer -/

/-- A finite register of natural-number modes.  Marking is native primality. -/
structure FinitePrimeOracleRegister where
  support : Finset ℕ

def FinitePrimeOracleRegister.marked (_P : FinitePrimeOracleRegister) (n : ℕ) : Prop :=
  Nat.Prime n

instance FinitePrimeOracleRegister.decidableMarked (P : FinitePrimeOracleRegister) :
    DecidablePred P.marked := fun n => by
      change Decidable (Nat.Prime n)
      infer_instance

namespace FinitePrimeOracleRegister

variable (P : FinitePrimeOracleRegister)

/-- Phase sign for the packet's marked predicate. -/
def sign (n : ℕ) : ℝ :=
  phaseSign P.marked n

/-- Phase oracle for amplitudes on natural-number registers. -/
def oracle (amp : ℕ → ℝ) : ℕ → ℝ :=
  phaseOracle P.marked amp

/-- The packet oracle is involutive. -/
theorem oracle_oracle (amp : ℕ → ℝ) :
    P.oracle (P.oracle amp) = amp := by
  exact phaseOracle_phaseOracle P.marked amp

/-- The packet oracle preserves finite squared norm on its support. -/
theorem normSq_oracle (amp : ℕ → ℝ) :
    finiteAmplitudeNormSq P.support (P.oracle amp) =
      finiteAmplitudeNormSq P.support amp := by
  exact finiteAmplitudeNormSq_phaseOracle P.support P.marked amp

/-- Number of marked items in the packet support. -/
def markedCard : ℕ :=
  markedCount P.support P.marked

/-- Number of unmarked items in the packet support. -/
def unmarkedCard : ℕ :=
  unmarkedCount P.support P.marked

/-- Marked and unmarked packet counts split the finite support. -/
theorem markedCard_add_unmarkedCard :
    P.markedCard + P.unmarkedCard = P.support.card := by
  exact markedCount_add_unmarkedCount P.support P.marked

end FinitePrimeOracleRegister

namespace QuantumCountingGate

/-- A property quantum-counting run uses a positive number of queries. -/
theorem query_bound_holds
    (G : InfoGeometry.Arithmetic.GenuineBounds.GenuineQuantumCountingAccuracy) :
    0 < G.queries :=
  G.queries_pos

/-- The estimate satisfies its explicit absolute-error tolerance. -/
theorem counting_accuracy_holds
    (G : InfoGeometry.Arithmetic.GenuineBounds.GenuineQuantumCountingAccuracy) :
    InfoGeometry.Arithmetic.GenuineBounds.CountingWithinError
      G.estimate G.actual G.ε :=
  G.counting_accuracy

/-- The run's failure probability satisfies its explicit Chernoff bound. -/
theorem chernoff_bound_holds
    (G : InfoGeometry.Arithmetic.GenuineBounds.GenuineQuantumCountingAccuracy) :
    2 * Real.exp (-2 * (G.queries : ℝ) * G.ε ^ 2) ≤ G.failure_prob :=
  G.chernoff_bound

end QuantumCountingGate

/-! ## 4. Error-budget certificates for RH-style fluctuation tests -/

/-- Raw coordinates for a finite fluctuation property. -/
abbrev QuantumCountingFluctuationCoordinates :=
  ℝ × (ℝ × (ℝ × (ℝ × ℝ)))

/-- The two property inequalities carried by a fluctuation property. -/
def QuantumCountingFluctuationPredicate
    (p : QuantumCountingFluctuationCoordinates) : Prop :=
  InfoGeometry.Arithmetic.GenuineBounds.CountingWithinError
      p.1 p.2.1 p.2.2.2.1 ∧
    |p.1 - p.2.2.1| + p.2.2.2.1 ≤ p.2.2.2.2

/-- Finite quantum-counting fluctuation evidence as a native subtype. -/
abbrev QuantumCountingFluctuationPacket :=
  {p : QuantumCountingFluctuationCoordinates // QuantumCountingFluctuationPredicate p}

namespace QuantumCountingFluctuationPacket

abbrev estimate (P : QuantumCountingFluctuationPacket) : ℝ := P.1.1
abbrev actual (P : QuantumCountingFluctuationPacket) : ℝ := P.1.2.1
abbrev expected (P : QuantumCountingFluctuationPacket) : ℝ := P.1.2.2.1
abbrev ε (P : QuantumCountingFluctuationPacket) : ℝ := P.1.2.2.2.1
abbrev bound (P : QuantumCountingFluctuationPacket) : ℝ := P.1.2.2.2.2

lemma counting_error (P : QuantumCountingFluctuationPacket) :
    InfoGeometry.Arithmetic.GenuineBounds.CountingWithinError
      P.estimate P.actual P.ε := P.2.1

lemma error_budget (P : QuantumCountingFluctuationPacket) :
    |P.estimate - P.expected| + P.ε ≤ P.bound := P.2.2

/-- Re-export of the property finite fluctuation bound. -/
theorem fluctuation_bound
    (P : QuantumCountingFluctuationPacket) :
    |P.actual - P.expected| ≤ P.bound := by
  have hErr : |P.estimate - P.actual| ≤ P.ε := P.counting_error
  have hBudget : |P.estimate - P.expected| + P.ε ≤ P.bound := P.error_budget
  have htri :
      |P.actual - P.expected| ≤ |P.estimate - P.expected| + |P.estimate - P.actual| := by
    calc
      |P.actual - P.expected|
          = |(P.estimate - P.expected) - (P.estimate - P.actual)| := by ring_nf
      _ ≤ |P.estimate - P.expected| + |P.estimate - P.actual| := by
            simpa [abs_sub_comm] using
              (abs_sub_le (P.estimate - P.expected) 0 (P.estimate - P.actual))
  calc
    |P.actual - P.expected|
        ≤ |P.estimate - P.expected| + |P.estimate - P.actual| := htri
    _ ≤ |P.estimate - P.expected| + P.ε := by
          have h := add_le_add_left hErr |P.estimate - P.expected|
          simpa [add_comm, add_left_comm, add_assoc] using h
    _ ≤ P.bound := hBudget

end QuantumCountingFluctuationPacket

end InfoGeometry.Arithmetic.FinitePrimeGroverOracle
