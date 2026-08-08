import proofs.SmithHatIsingDuality
import proofs.ClebschGordanPenroseNonequilibriumSpinGraph

/-!
# Bashore spin-network qubit digest

Theorem-honest formal digest of

Erik Bashore, *Quantum Simulations of Spin Networks From the Perspective of
Loop Quantum Gravity*, Uppsala University project report, 2024.

The report constructs the four-valent `j = 1/2` intertwiner qubit used in
spin-network quantum simulations.  This layer records the finite algebraic core:

* a four-valent spin-`1/2` intertwiner space is represented as a two-state qubit;
* the `s`-channel basis vectors are the singlet--singlet state `|0_I⟩` and the
  triplet-coupled state `|1_I⟩`;
* their rational coefficient skeletons have the expected norm/orthogonality
  bookkeeping before the final `1/√3` normalization of the triplet state.

Actual SU(2) representation theory, Wigner-symbol values, quantum hardware
execution, and LQG transition-amplitude physics remain sockets.
-/

noncomputable section

namespace BashoreSpinNetworkQubit

/-- Four physical qubits encode sixteen computational basis states. -/
def physicalQubitBasisCard : ℕ := 16

/-- A four-valent `j=1/2` intertwiner space is two-dimensional. -/
def intertwinerQubitDimension : ℕ := 2

/-- Computational-basis support used by the two intertwiner states:
`0011,0101,0110,1001,1010,1100` as binary indices. -/
def intertwinerSupport : List ℕ := [3, 5, 6, 9, 10, 12]

/-- Rational coefficients for `|0_I⟩ = 1/2(0101 - 0110 - 1001 + 1010)`. -/
def coeffZeroI : ℕ → ℚ
  | 5 => 1 / 2
  | 6 => -1 / 2
  | 9 => -1 / 2
  | 10 => 1 / 2
  | _ => 0

/-- Rational coefficient skeleton for
`√3 |1_I⟩ = |0011⟩ + |1100⟩ - 1/2(0101+0110+1001+1010)`. -/
def coeffOneIRaw : ℕ → ℚ
  | 3 => 1
  | 12 => 1
  | 5 => -1 / 2
  | 6 => -1 / 2
  | 9 => -1 / 2
  | 10 => -1 / 2
  | _ => 0

/-- Dot product over the finite support. -/
def supportDot (a b : ℕ → ℚ) : ℚ :=
  (intertwinerSupport.map (fun n => a n * b n)).sum

@[simp] theorem physical_qubit_basis_card_eq : physicalQubitBasisCard = 16 := rfl

@[simp] theorem intertwiner_qubit_dimension_eq : intertwinerQubitDimension = 2 := rfl

@[simp] theorem intertwiner_support_length : intertwinerSupport.length = 6 := rfl

/-- `|0_I⟩` is normalized. -/
theorem coeffZeroI_norm : supportDot coeffZeroI coeffZeroI = 1 := by
  norm_num [supportDot, intertwinerSupport, coeffZeroI]

/-- The unnormalized triplet-coupled skeleton has squared norm `3`; multiplying
by `1/√3` gives a normalized `|1_I⟩`. -/
theorem coeffOneIRaw_norm : supportDot coeffOneIRaw coeffOneIRaw = 3 := by
  norm_num [supportDot, intertwinerSupport, coeffOneIRaw]

/-- The two intertwiner basis skeletons are orthogonal. -/
theorem coeffZeroI_coeffOneIRaw_orthogonal :
    supportDot coeffZeroI coeffOneIRaw = 0 := by
  norm_num [supportDot, intertwinerSupport, coeffZeroI, coeffOneIRaw]

/-- The `s,t,u` recoupling channels named in the report. -/
inductive RecouplingChannel where
  | s | t | u
  deriving DecidableEq, Repr

theorem bashore_spin_network_qubit_synthesis :
    physicalQubitBasisCard = 16 ∧
    intertwinerQubitDimension = 2 ∧
    intertwinerSupport.length = 6 ∧
    supportDot coeffZeroI coeffZeroI = 1 ∧
    supportDot coeffOneIRaw coeffOneIRaw = 3 ∧
    supportDot coeffZeroI coeffOneIRaw = 0 ∧
    ClebschGordanPenroseNonequilibriumSpinGraph.CGAllowed
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.jHalf
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.jHalf
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.j0 = true := by
  exact ⟨physical_qubit_basis_card_eq,
    intertwiner_qubit_dimension_eq,
    intertwiner_support_length,
    coeffZeroI_norm,
    coeffOneIRaw_norm,
    coeffZeroI_coeffOneIRaw_orthogonal,
    ClebschGordanPenroseNonequilibriumSpinGraph.half_tensor_half_allows_singlet⟩

end BashoreSpinNetworkQubit

end noncomputable section
