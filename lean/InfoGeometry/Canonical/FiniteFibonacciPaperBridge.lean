import InfoGeometry.Canonical.FiniteCompassBraidedChain
import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Canonical.FiniteFibonacciAnyonRegister
import InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
import InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks
import InfoGeometry.Canonical.FiniteFibonacciFourPointDualBasis
import InfoGeometry.Canonical.FiniteFibonacciCompassBridge

/-!
# InfoGeometry.Canonical.FiniteFibonacciPaperBridge

Paper-facing bridge for the finite Fibonacci-anyon surface.

This file does not introduce new mathematics.  It gathers the already proved
finite statements that match the paper's introduction:

* Fibonacci fusion rules;
* finite vacuum-channel counts;
* finite `N`-qubit computational subspaces;
* braid-word rewrite invariance for the repo-native monodromy/readout abstraction;
* finite compass-chain braid transport.

No conformal blocks.
No analytic continuation.
No infinite limit.
-/

namespace FiniteFibonacciPaperBridge

open InfoGeometry.Canonical.FiniteCompassBraidedChain
open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Canonical.FiniteFibonacciAnyonRegister
open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
open InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks
open InfoGeometry.Canonical.FiniteFibonacciFourPointDualBasis
open InfoGeometry.Canonical.FiniteFibonacciCompassBridge

/-- The Fibonacci fusion rule `ε × ε = 𝟙 ⊕ ε`. -/
theorem fibonacci_fusion_rule :
    FibonacciCharge.fusion FibonacciCharge.eps FibonacciCharge.eps =
      {FibonacciCharge.one, FibonacciCharge.eps} :=
  FibonacciCharge.eps_fusion_eps

/-- Vacuum-channel dimension for `2N + 2` Fibonacci anyons. -/
theorem fibonacci_vacuum_channel_dimension (N : ℕ) :
    vacuumFusionDimension (2 * N + 2) = Nat.fib (2 * N + 1) :=
  vacuumFusionDimension_two_mul_add_two N

/-- The finite register carried by `2N + 2` Fibonacci anyons has Fibonacci cardinality. -/
theorem fibonacci_register_card (N : ℕ) :
    Fintype.card (FibonacciAnyonRegister N) = Nat.fib (2 * N + 1) :=
  register_card N

/-- The finite `N`-qubit computational vector space has cardinality `2^N`. -/
theorem fibonacci_computational_vector_card (N : ℕ) :
    Fintype.card (ComputationalVector N) = 2 ^ N :=
  card_computationalVector N

/-- The finite Fibonacci block dimension is the expected Fibonacci number. -/
theorem fibonacci_block_dimension_eq_fib (N : ℕ) :
    fibonacciBlockDimension N = Nat.fib (2 * N + 1) :=
  fibonacciBlockDimension_eq_fib N

/-- The finite non-computational count for one qubit is zero. -/
theorem fibonacci_nonComputationalCount_one :
    FiniteFibonacciComputationalSpace.nonComputationalCount 1 = 0 :=
  FiniteFibonacciComputationalSpace.nonComputationalCount_one

/-- The finite non-computational count for two qubits is one. -/
theorem fibonacci_nonComputationalCount_two :
    FiniteFibonacciComputationalSpace.nonComputationalCount 2 = 1 :=
  FiniteFibonacciComputationalSpace.nonComputationalCount_two

/-- The finite non-computational count for three qubits is five. -/
theorem fibonacci_nonComputationalCount_three :
    FiniteFibonacciComputationalSpace.nonComputationalCount 3 = 5 :=
  FiniteFibonacciComputationalSpace.nonComputationalCount_three

/-- The repo-native monodromy/readout abstraction is invariant under the braid rewrite. -/
theorem fibonacci_monodromy_braid_rewrite
    {Gate : Type*} [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    (i : ℕ) (left right : FibonacciBraidWord) :
    monodromy (Gate := Gate) χ readout (left ++ [i, i + 1, i] ++ right) =
      monodromy (Gate := Gate) χ readout (left ++ [i + 1, i, i + 1] ++ right) :=
  monodromy_braid_rewrite χ readout i left right

/-- The repo-native monodromy/readout abstraction is invariant under separated commutation. -/
theorem fibonacci_monodromy_commute_rewrite
    {Gate : Type*} [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    {i j : ℕ} (hsep : i + 1 < j) (left right : FibonacciBraidWord) :
    monodromy (Gate := Gate) χ readout (left ++ [i, j] ++ right) =
      monodromy (Gate := Gate) χ readout (left ++ [j, i] ++ right) :=
  monodromy_commute_rewrite χ readout hsep left right

/-- Fibonacci compass-chain braid transport preserves the elliptic law. -/
theorem fibonacci_compassTransport_elliptic_sq
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (fibonacciCompassTransport w C i).elliptic *
        (fibonacciCompassTransport w C i).elliptic = -1 :=
  fibonacciCompassTransport_elliptic_sq w C i

/-- Fibonacci compass-chain braid transport preserves the hyperbolic law. -/
theorem fibonacci_compassTransport_hyperbolic_sq
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (fibonacciCompassTransport w C i).hyperbolic *
        (fibonacciCompassTransport w C i).hyperbolic = 1 :=
  fibonacciCompassTransport_hyperbolic_sq w C i

/-- Fibonacci compass-chain braid transport preserves the parabolic law. -/
theorem fibonacci_compassTransport_parabolic_sq
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : FibonacciBraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (fibonacciCompassTransport w C i).parabolic *
        (fibonacciCompassTransport w C i).parabolic = 0 :=
  fibonacciCompassTransport_parabolic_sq w C i

/-- Fibonacci compass-chain braid transport is invariant under the braid rewrite. -/
theorem fibonacci_compassTransport_braid_rewrite
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (i : ℕ) (left right : FibonacciBraidWord) (C : CompassChain ℕ Op) :
    fibonacciCompassTransport (left ++ [i, i + 1, i] ++ right) C =
      fibonacciCompassTransport (left ++ [i + 1, i, i + 1] ++ right) C :=
  fibonacciCompassTransport_braid_rewrite i left right C

/-- Fibonacci compass-chain braid transport is invariant under separated commutation. -/
theorem fibonacci_compassTransport_commute_rewrite
    {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    {i j : ℕ} (hsep : i + 1 < j) (left right : FibonacciBraidWord)
    (C : CompassChain ℕ Op) :
    fibonacciCompassTransport (left ++ [i, j] ++ right) C =
    fibonacciCompassTransport (left ++ [j, i] ++ right) C :=
  fibonacciCompassTransport_commute_rewrite hsep left right C

/-- The four-point Fibonacci `Φ` basis has the two finite basis vectors. -/
theorem fibonacci_fourPoint_phi0 :
    phi0 = (1, 0) :=
  rfl

/-- The four-point Fibonacci `Φ` basis has the second finite basis vector. -/
theorem fibonacci_fourPoint_phi1 :
    phi1 = (0, 1) :=
  rfl

/-- In the finite four-point `Φ` basis, `b₁` is diagonal. -/
theorem fibonacci_fourPoint_b1_diagonal (a0 a1 : Units ℂ) :
    b1Action a0 a1 = diagonalBraidAction a0 a1 :=
  rfl

/-- In the finite four-point `Φ` basis, `b₃` is diagonal. -/
theorem fibonacci_fourPoint_b3_diagonal (a0 a1 : Units ℂ) :
    b3Action a0 a1 = diagonalBraidAction a0 a1 :=
  rfl

/-- The finite four-point `Φ` basis sees the same diagonal action for `b₁` and `b₃`. -/
theorem fibonacci_fourPoint_b1_eq_b3 (a0 a1 : Units ℂ) :
    b1Action a0 a1 = b3Action a0 a1 :=
  b1Action_eq_b3Action a0 a1

/-- The third pairing is linearly dependent on the first two. -/
theorem fibonacci_fourPoint_pairing14_23_relation (x : ℂ) :
    pairing14_23 x = x • pairing12_34 + (1 - x) • pairing13_24 :=
  pairing14_23_relation x

/-- The first four-point dual basis vector is the image of `Φ(0)`. -/
theorem fibonacci_fourPoint_theta0 (D : FusionData) :
    FusionData.theta0 D = FusionData.fusionTransform D phi0 :=
  rfl

/-- The second four-point dual basis vector is the image of `Φ(1)`. -/
theorem fibonacci_fourPoint_theta1 (D : FusionData) :
    FusionData.theta1 D = FusionData.fusionTransform D phi1 :=
  rfl

/-- The finite `Φ → Θ → Φ` transport is the identity. -/
theorem fibonacci_fourPoint_phi_to_theta_to_phi (D : FusionData) (v : PhiBasis) :
    FusionData.fusionTransform D (FusionData.fusionTransform D v) = v :=
  FusionData.fusionTransform_involutive D v

end FiniteFibonacciPaperBridge
