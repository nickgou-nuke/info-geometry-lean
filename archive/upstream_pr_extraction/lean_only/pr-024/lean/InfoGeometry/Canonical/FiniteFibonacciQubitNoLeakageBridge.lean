import InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
import InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
import InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage

/-!
# InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakageBridge

Canonical bridge for the finite Fibonacci computational/no-leakage surface.

This file only re-exports theorem-owned finite statements from:

* `FiniteFibonacciComputationalSpace`
* `FiniteFibonacciQubitNoLeakage`

No new algebra.
No analytic continuation.
No fault-tolerance claim.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakageBridge

open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
open InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
open InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage

/-- The finite `N`-qubit computational space is `Fin N → Bool`. -/
theorem computational_vector_def (N : ℕ) :
    ComputationalVector N = (Fin N → Bool) :=
  rfl

/-- The finite `N`-qubit computational space has cardinality `2^N`. -/
theorem computational_vector_card (N : ℕ) :
    Fintype.card (ComputationalVector N) = 2 ^ N :=
  InfoGeometry.Canonical.FiniteFibonacciComputationalSpace.card_computationalVector N

/-- The finite Fibonacci block dimension is the expected Fibonacci number. -/
theorem fibonacci_block_dimension_eq_fib (N : ℕ) :
    fibonacciBlockDimension N = Nat.fib (2 * N + 1) :=
  InfoGeometry.Canonical.FiniteFibonacciComputationalSpace.fibonacciBlockDimension_eq_fib N

/-- The finite non-computational count for one qubit is zero. -/
theorem finite_nonComputationalCount_one :
    nonComputationalCount 1 = 0 :=
  InfoGeometry.Canonical.FiniteFibonacciComputationalSpace.nonComputationalCount_one

/-- The finite non-computational count for two qubits is one. -/
theorem finite_nonComputationalCount_two :
    nonComputationalCount 2 = 1 :=
  InfoGeometry.Canonical.FiniteFibonacciComputationalSpace.nonComputationalCount_two

/-- The finite non-computational count for three qubits is five. -/
theorem finite_nonComputationalCount_three :
    nonComputationalCount 3 = 5 :=
  InfoGeometry.Canonical.FiniteFibonacciComputationalSpace.nonComputationalCount_three

/-- The truncated Fibonacci `q`-dimension identity. -/
theorem tau_inv_sq_truncation {τ : ℚ} (hτ0 : τ ≠ 0) (hτ : τ ^ 2 + τ = 1) :
    τ⁻¹ * τ⁻¹ = 1 + τ⁻¹ + spin2TruncatedDimension :=
  InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage.tau_inv_sq_truncation hτ0 hτ

/-- The first and last one-qubit braid generators have the same diagonal readout. -/
theorem oneQubit_b1_eq_b3 (qNeg4 q3 : ℂ)
    (B : FiniteFibonacciLowAnyonMatrices.BBlockEntries) :
    oneQubitGeneratorMatrix qNeg4 q3 B OneQubitBraidGenerator.b1 =
      oneQubitGeneratorMatrix qNeg4 q3 B OneQubitBraidGenerator.b3 :=
  InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage.oneQubit_b1_eq_b3 qNeg4 q3 B

/-- The `N = 2` block-diagonal action preserves the computational sector. -/
theorem twoQubitNoLeakageAction_preserves_computational
    (k : Fin 2) (f : Bool → Bool) {x : TwoQubitSixAnyonLabel}
    (hx : TwoQubitSixAnyonLabel.IsComputational x) :
    TwoQubitSixAnyonLabel.IsComputational (twoQubitNoLeakageAction k f x) :=
  InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage.twoQubitNoLeakageAction_preserves_computational k f hx

/-- The unique NC state is fixed by every restricted two-qubit action. -/
theorem twoQubitNoLeakageAction_nc
    (k : Fin 2) (f : Bool → Bool) :
    twoQubitNoLeakageAction k f TwoQubitSixAnyonLabel.nc = TwoQubitSixAnyonLabel.nc :=
  InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage.twoQubitNoLeakageAction_nc k f

/-- There are four computational labels in the `N = 2` sector. -/
theorem twoQubit_computational_card :
    Fintype.card (ComputationalVector 2) = 4 :=
  InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage.twoQubit_computational_card

/-- The `N = 2` finite count has one NC label. -/
theorem twoQubit_nc_count :
    nonComputationalCount 2 = 1 :=
  InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage.twoQubit_nc_count

end InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakageBridge
