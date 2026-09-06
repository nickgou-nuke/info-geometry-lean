import InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
import InfoGeometry.Canonical.FiniteFibonacciPailRopeQubits
import InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup
import InfoGeometry.Canonical.FiniteFibonacciRegisterWords

/-!
# InfoGeometry.Canonical.FiniteFibonacciComputationalQubitPaperBridge

Paper-facing bridge for the finite computational-vector and qubit section.

This file records the finite combinatorial content behind Section 8:

* an `N`-qubit computational vector is a bit assignment `Fin N → Bool`;
* the single-qubit basis is the pail/rope pair `|0⟩`, `|1⟩`;
* the finite computational sector has cardinality `2^N`;
* the `N = 2` sector has four computational vectors and one NC label;
* the local block-diagonal qubit actions preserve the computational sector;
* the register-subgroup actions remain finite and no-leakage on computational
  vectors.

This file does not formalize the colex ordering remark or any matrix tensor
product formulas.  It stays on the theorem side of the existing finite
computational-space interface.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciComputationalQubitPaperBridge

open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
open InfoGeometry.Canonical.FiniteFibonacciPailRopeQubits
open InfoGeometry.Canonical.FiniteFibonacciRegisterSubgroup
open InfoGeometry.Canonical.FiniteFibonacciRegisterWords

/-- The finite `N`-qubit computational space is `Fin N → Bool`. -/
theorem computational_vector_def (N : ℕ) :
    ComputationalVector N = (Fin N → Bool) :=
  rfl

/-- The one-qubit pail is the computational `|0⟩` label. -/
theorem oneQubit_zero_label :
    oneQubitZero 0 = PailRope.pail :=
  rfl

/-- The one-qubit rope is the computational `|1⟩` label. -/
theorem oneQubit_one_label :
    oneQubitOne 0 = PailRope.rope :=
  rfl

/-- The `N`-qubit computational sector has cardinality `2^N`. -/
theorem computational_vector_card (N : ℕ) :
    Fintype.card (ComputationalVector N) = 2 ^ N :=
  card_computationalVector N

/-- The single-qubit computational sector has two basis vectors. -/
theorem computational_vector_card_one :
    Fintype.card (ComputationalVector 1) = 2 := by
  simp

/-- The two-qubit computational sector has four basis vectors. -/
theorem computational_vector_card_two :
    Fintype.card (ComputationalVector 2) = 4 := by
  simp

/-- The single-qubit pail/rope sector has two labels. -/
theorem oneQubit_pailRope_card :
    Fintype.card (PailRopeWord 1) = 2 :=
  card_oneQubitPailRope

/-- The `N = 2` finite six-anyon sector has one non-computational label. -/
theorem twoQubit_nc_count :
    nonComputationalCount 2 = 1 :=
  nonComputationalCount_two

/-- A local computational action preserves the computational sector in general. -/
theorem local_block_preserves_computational {N : ℕ} {NC : Type*}
    (k : Fin N) (f : Bool → Bool) (onNonComputational : NC → NC)
    {x : FibonacciBlockLabel N NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (localQubitBlockAction k f onNonComputational x) :=
  localQubitBlockAction_preserves_computational k f onNonComputational hx

/-- The finite register-word action preserves the computational sector. -/
theorem registerWordBlockAction_preserves_computational_readback
    {N : ℕ} {NC : Type*} (r b : Bool → Bool)
    (onNonComputational : NC → NC) (w : RegisterWord N)
    {x : FibonacciBlockLabel (N + 1) NC}
    (hx : FibonacciBlockLabel.IsComputational x) :
    FibonacciBlockLabel.IsComputational
      (registerWordBlockAction r b onNonComputational w x) :=
  InfoGeometry.Canonical.FiniteFibonacciRegisterWords.registerWordBlockAction_preserves_computational
    r b onNonComputational w hx

/-- The finite `N`-qubit computational sector is the combinatorial basis used in Section 8. -/
theorem computational_sector_section8 (N : ℕ) :
    Fintype.card (ComputationalVector N) = 2 ^ N :=
  computational_vector_card N

end InfoGeometry.Canonical.FiniteFibonacciComputationalQubitPaperBridge
