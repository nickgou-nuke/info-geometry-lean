import InfoGeometry.Canonical.FiniteFibonacciComputationalQubitPaperBridge
import InfoGeometry.Canonical.FiniteFibonacciFourAnyonHestenesBridge
import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Canonical.SuperBracketHestenesKreinClosure
import InfoGeometry.Krein.HestenesMoebiusClosureBridge

/-!
# InfoGeometry.Canonical.FiniteFibonacciSymmetryClosureBridge

Symmetry-closure bridge for the finite Fibonacci sector.

This file translates the paper-facing Fibonacci register language into the
repo-native closure language:

* computational vectors are finite bit assignments;
* the local register action is block-diagonal and leaves the computational
  sector invariant;
* Hestenes/Krein analyticity is a phase-axis closure condition;
* the superbracket closes in the even/odd graded sectors;
* Möbius/Cayley closure preserves the phase axis and the Hestenes analytic
  symmetry class.

No complex analytic continuation.
No conformal-block function theory.
No explicit braid-matrix derivation.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciSymmetryClosureBridge

open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
open InfoGeometry.Canonical.FiniteFibonacciComputationalQubitPaperBridge
open InfoGeometry.Canonical.FiniteFibonacciFourAnyonHestenesBridge
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.SuperBracketHestenesKreinClosure
open InfoGeometry.Krein.HestenesMoebiusClosureBridge

/-- The computational sector is closed under the local block-diagonal action. -/
theorem computational_sector_closed_under_local_block {N : ℕ} {NC : Type*}
    (k : Fin N) (f : Bool → Bool) (onNonComputational : NC → NC)
    {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (localQubitBlockAction k f onNonComputational x) :=
  local_block_preserves_computational k f onNonComputational hx

/-- The paper's one-qubit computational sector is the finite pail/rope basis. -/
theorem oneQubit_compactified_basis_card :
    Fintype.card (ComputationalVector 1) = 2 :=
  computational_vector_card_one

/-- The two-qubit computational sector is still the tensor-power closure. -/
theorem twoQubit_compactified_basis_card :
    Fintype.card (ComputationalVector 2) = 4 :=
  computational_vector_card_two

/-- The four-anyon diagonal readout is Hestenes-analytic in the finite phase-axis sense. -/
theorem fourAnyon_diagonal_readout_hestenes_closed (q : Units ℂ) :
    IsFourAnyonHestenesAnalytic
      (fun v => InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks.diagonalRAction q v) :=
  fourAnyonHestenesAnalytic q

/-- Hestenes-analytic symmetry generators are closed under commutator. -/
theorem symmetryClosure_commutator
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {A B : (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)}
    (hA : IsHestenesAnalyticSymmetry (E := E) A)
    (hB : IsHestenesAnalyticSymmetry (E := E) B) :
    IsHestenesAnalyticSymmetry (E := E)
      (hestenesSymmetryCommutator (E := E) A B) :=
  hestenesAnalyticSymmetry_commutator (E := E) hA hB

/-- Odd-odd superbrackets return to the even sector. -/
theorem symmetryClosure_odd_odd_to_even
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {K A B : V →ₗ[ℂ] V}
    (hA : IsOdd K A) (hB : IsOdd K B) :
    IsEven K (superBracket (-1) A B) :=
  odd_odd_anticommutator_even hA hB

/-- Möbius reparameterization fixes the Hestenes phase axis. -/
theorem moebius_phase_axis_fixed
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Word : Type*} [Fintype Word] [DecidableEq Word]
    (M : HestenesMoebiusClosureBridge (E := E) Word)
    (g : MoebiusParameter) :
    M.operatorAction g (InfoGeometry.Krein.clockAxis (E := E)) =
      InfoGeometry.Krein.clockAxis (E := E) :=
  M.moebius_phaseAxis_fixed g

/-- Möbius reparameterization preserves the Hestenes analytic symmetry class. -/
theorem moebius_preserves_hestenes_symmetry
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Word : Type*} [Fintype Word] [DecidableEq Word]
    (M : HestenesMoebiusClosureBridge (E := E) Word)
    (g : MoebiusParameter) {A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E}
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E) (M.operatorAction g A) :=
  M.moebius_preserves_hestenesAnalyticSymmetry g hA

/-- The finite computational sector is the closure target used in Section 8. -/
theorem section8_symmetry_closure_target (N : ℕ) :
    Fintype.card (ComputationalVector N) = 2 ^ N :=
  computational_vector_card N

end InfoGeometry.Canonical.FiniteFibonacciSymmetryClosureBridge
