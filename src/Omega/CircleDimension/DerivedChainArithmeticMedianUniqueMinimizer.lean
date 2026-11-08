import Mathlib.Tactic
import Omega.CircleDimension.SquarefreeMedianDistance
import Omega.CircleDimension.SquarefreeMedianMetricEllipseRealization

namespace Omega.CircleDimension

/-- The concrete squarefree chain used to witness the derived arithmetic median statement. -/
def derivedChainArithmeticCarrier : Finset ℕ :=
  {1, 2, 3, 5, 6, 10, 15, 30}

/-- Three-point support-distance objective for the squarefree chain witness. -/
def derivedChainArithmeticObjective (n : ℕ) : ℕ :=
  squarefreeSupportDistance n 6 + squarefreeSupportDistance n 10 + squarefreeSupportDistance n 15

/-- The same objective transported to the ellipse realization. -/
def derivedChainEllipseObjective (E : SquarefreeEllipse) : ℕ :=
  derivedChainArithmeticObjective E

private theorem omegaPrime_one :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 1 = 0 := by
  simp [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime]

private theorem omegaPrime_two :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 2 = 1 := by
  norm_num [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime,
    Nat.primeFactors, Nat.primeFactorsList]

private theorem omegaPrime_three :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 3 = 1 := by
  norm_num [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime,
    Nat.primeFactors, Nat.primeFactorsList]

private theorem omegaPrime_five :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 5 = 1 := by
  norm_num [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime,
    Nat.primeFactors, Nat.primeFactorsList]

private theorem omegaPrime_six :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 6 = 2 := by
  norm_num [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime,
    Nat.primeFactors, Nat.primeFactorsList]

private theorem omegaPrime_ten :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 10 = 2 := by
  norm_num [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime,
    Nat.primeFactors, Nat.primeFactorsList]

private theorem omegaPrime_fifteen :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 15 = 2 := by
  norm_num [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime,
    Nat.primeFactors, Nat.primeFactorsList]

private theorem omegaPrime_thirty :
    Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime 30 = 3 := by
  norm_num [Omega.CircleDimension.SquarefreeMedianDistance.omegaPrime,
    Nat.primeFactors, Nat.primeFactorsList]

/-- Concrete derived-chain median package: the gcd closed form gives the median `30` for the
triple `(6, 10, 15)`, and this point is the unique minimizer of the corresponding three-point
support-distance sum on the associated squarefree ellipse family.
    thm:derived-chain-arithmetic-median-unique-minimizer -/
theorem paper_derived_chain_arithmetic_median_unique_minimizer :
    squarefreeMedianCenter 6 10 15 = 30 ∧
    squarefreeEllipseMedian (squarefreeEllipseOf 6) (squarefreeEllipseOf 10)
        (squarefreeEllipseOf 15) = squarefreeEllipseOf 30 ∧
    (∀ n ∈ derivedChainArithmeticCarrier,
      derivedChainArithmeticObjective 30 ≤ derivedChainArithmeticObjective n) ∧
    (∀ E ∈ derivedChainArithmeticCarrier.image squarefreeEllipseOf,
      derivedChainEllipseObjective (squarefreeEllipseOf 30) ≤ derivedChainEllipseObjective E) ∧
    (∀ E ∈ derivedChainArithmeticCarrier.image squarefreeEllipseOf,
      derivedChainEllipseObjective E = derivedChainEllipseObjective (squarefreeEllipseOf 30) →
        E = squarefreeEllipseOf 30) := by
  have hcenter : squarefreeMedianCenter 6 10 15 = 30 := by
    norm_num [squarefreeMedianCenter]
  have hmin : ∀ n ∈ derivedChainArithmeticCarrier,
      derivedChainArithmeticObjective 30 ≤ derivedChainArithmeticObjective n := by
    intro n hn
    simp [derivedChainArithmeticCarrier] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [derivedChainArithmeticObjective, squarefreeSupportDistance,
      omegaPrime_one, omegaPrime_two, omegaPrime_three, omegaPrime_five,
      omegaPrime_six, omegaPrime_ten, omegaPrime_fifteen, omegaPrime_thirty]
  have hunique : ∀ n ∈ derivedChainArithmeticCarrier,
      derivedChainArithmeticObjective n = derivedChainArithmeticObjective 30 → n = 30 := by
    intro n hn heq
    simp [derivedChainArithmeticCarrier] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [derivedChainArithmeticObjective, squarefreeSupportDistance,
      omegaPrime_one, omegaPrime_two, omegaPrime_three, omegaPrime_five,
      omegaPrime_six, omegaPrime_ten, omegaPrime_fifteen, omegaPrime_thirty] at heq
    all_goals rfl
  refine ⟨hcenter, ?_, hmin, ?_, ?_⟩
  · simpa [squarefreeEllipseMedian, squarefreeEllipseOf] using hcenter
  · intro E hE
    rcases Finset.mem_image.mp hE with ⟨n, hn, rfl⟩
    simpa [derivedChainEllipseObjective, squarefreeEllipseOf] using hmin n hn
  · intro E hE heq
    rcases Finset.mem_image.mp hE with ⟨n, hn, rfl⟩
    have hEq : derivedChainArithmeticObjective n = derivedChainArithmeticObjective 30 := by
      simpa [derivedChainEllipseObjective, squarefreeEllipseOf] using heq
    have hn30 := hunique n hn hEq
    simpa [squarefreeEllipseOf] using hn30

end Omega.CircleDimension
