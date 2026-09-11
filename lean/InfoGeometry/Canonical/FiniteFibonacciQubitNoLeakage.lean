import InfoGeometry.Canonical.FiniteFibonacciPailRopeQubits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices

/-!
# InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage

Finite qubit/no-leakage interface for the Fibonacci computational sector.

This file records additional finite content from Section 8:

* the symbolic `q`-dimension truncation identity behind the Fibonacci fusion
  rule, expressed only through the scalar relation `τ² + τ = 1`;
* the one-qubit `B₄` readout uses endpoint `R` actions and a middle `B` action;
* the two-qubit `N = 2` sector has four computational labels plus one NC label;
* the restricted generators act block-diagonally, so computational labels do not
  leak into the NC label.

No quantum-group construction.
No conformal-block construction.
No Solovay--Kitaev or fault-tolerance theorem.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage

open FiniteFibonacciComputationalSpace
open FiniteFibonacciPailRopeQubits
open FiniteFibonacciLowAnyonMatrices

/-- Symbolic quantum-dimension labels used in the truncated `q`-spin picture. -/
inductive TruncatedQSpin where
  /-- Vacuum/q-spin zero sector. -/
  | spin0
  /-- Fibonacci/q-spin one sector. -/
  | spin1
  deriving DecidableEq, Repr, Fintype

/-- Symbolic dimensions `[1]q = 1`, `[3]q = τ⁻¹`, and truncated `[5]q = 0`. -/
noncomputable def truncatedQDimension (τ : ℂ) : TruncatedQSpin → ℂ
  | TruncatedQSpin.spin0 => 1
  | TruncatedQSpin.spin1 => τ⁻¹

/-- The truncated missing `q`-spin-2 sector has symbolic rational dimension zero. -/
def spin2TruncatedDimension : ℚ :=
  0

/-- Fibonacci truncation identity: `τ⁻² = 1 + τ⁻¹ + 0`, from `τ² + τ = 1`. -/
theorem tau_inv_sq_truncation {τ : ℚ} (hτ0 : τ ≠ 0) (hτ : τ ^ 2 + τ = 1) :
    τ⁻¹ * τ⁻¹ = 1 + τ⁻¹ + spin2TruncatedDimension := by
  rw [spin2TruncatedDimension]
  field_simp [hτ0]
  nlinarith [hτ]

/-- The full finite four-anyon one-qubit generator family. -/
inductive OneQubitBraidGenerator where
  /-- First neighboring exchange, diagonal `R`. -/
  | b1
  /-- Middle exchange, non-diagonal `B`. -/
  | b2
  /-- Last neighboring exchange, diagonal `R`. -/
  | b3
  deriving DecidableEq, Repr, Fintype

/-- Matrix readout for the one-qubit `B₄` action on the two-channel basis. -/
noncomputable def oneQubitGeneratorMatrix
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    OneQubitBraidGenerator → Matrix (Fin 2) (Fin 2) ℂ
  | OneQubitBraidGenerator.b1 => !![qNeg4, 0; 0, q3]
  | OneQubitBraidGenerator.b2 => BBlockEntries.matrix B
  | OneQubitBraidGenerator.b3 => !![qNeg4, 0; 0, q3]

/-- The first and last one-qubit braid generators have the same diagonal readout. -/
theorem oneQubit_b1_eq_b3 (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    oneQubitGeneratorMatrix qNeg4 q3 B OneQubitBraidGenerator.b1 =
      oneQubitGeneratorMatrix qNeg4 q3 B OneQubitBraidGenerator.b3 :=
  rfl

/-- Labels for the `N = 2` six-anyon space: four computational vectors and one NC label. -/
inductive TwoQubitSixAnyonLabel where
  /-- Computational label. -/
  | computational : ComputationalVector 2 → TwoQubitSixAnyonLabel
  /-- The unique non-computational label in the six-anyon example. -/
  | nc : TwoQubitSixAnyonLabel
  deriving Repr

noncomputable instance : DecidableEq TwoQubitSixAnyonLabel := by
  classical
  infer_instance

namespace TwoQubitSixAnyonLabel

/-- Predicate selecting the four computational labels, with an explicit bit-vector witness. -/
def IsComputational (x : TwoQubitSixAnyonLabel) : Prop :=
  ∃ α : ComputationalVector 2, x = computational α

@[simp]
theorem isComputational_computational (α : ComputationalVector 2) :
    IsComputational (computational α) :=
  ⟨α, rfl⟩

@[simp]
theorem not_isComputational_nc :
    ¬ IsComputational nc := by
  intro h
  rcases h with ⟨α, hα⟩
  cases hα

end TwoQubitSixAnyonLabel

/-- A two-qubit local action: apply a Boolean map to qubit `k`. -/
def twoQubitLocalAction (k : Fin 2) (f : Bool → Bool) :
    ComputationalVector 2 → ComputationalVector 2 :=
  localQubitAction k f

/-- Block-diagonal action on the `N = 2` six-anyon labels. -/
def twoQubitNoLeakageAction (k : Fin 2) (f : Bool → Bool) :
    TwoQubitSixAnyonLabel → TwoQubitSixAnyonLabel
  | TwoQubitSixAnyonLabel.computational α =>
      TwoQubitSixAnyonLabel.computational (twoQubitLocalAction k f α)
  | TwoQubitSixAnyonLabel.nc => TwoQubitSixAnyonLabel.nc

/-- The `N = 2` block-diagonal action preserves the computational sector. -/
theorem twoQubitNoLeakageAction_preserves_computational
    (k : Fin 2) (f : Bool → Bool) {x : TwoQubitSixAnyonLabel}
    (hx : TwoQubitSixAnyonLabel.IsComputational x) :
    TwoQubitSixAnyonLabel.IsComputational (twoQubitNoLeakageAction k f x) := by
  cases x with
  | computational α =>
      exact ⟨twoQubitLocalAction k f α, rfl⟩
  | nc =>
      rcases hx with ⟨α, hα⟩
      cases hα

/-- The unique NC state is fixed by every such restricted two-qubit action. -/
theorem twoQubitNoLeakageAction_nc
    (k : Fin 2) (f : Bool → Bool) :
    twoQubitNoLeakageAction k f TwoQubitSixAnyonLabel.nc = TwoQubitSixAnyonLabel.nc :=
  rfl

/-- There are four computational labels in the `N = 2` sector. -/
theorem twoQubit_computational_card :
    Fintype.card (ComputationalVector 2) = 4 := by
  norm_num [card_computationalVector]

/-- The `N = 2` finite count has one NC label. -/
theorem twoQubit_nc_count :
    nonComputationalCount 2 = 1 :=
  nonComputationalCount_two

end InfoGeometry.Canonical.FiniteFibonacciQubitNoLeakage
