import Mathlib
import proofs.WeakIsospinSU2
import proofs.ClebschGordanPenroseNonequilibriumSpinGraph

/-!
# Quantum spacetime on a quantum simulator

Theorem-honest digest of Li--Li--Han--Lu--Zhou--Ruan--Long--Wan--Lu--Zeng--
Laflamme, "Quantum spacetime on a quantum simulator",
Communications Physics 2, 122 (2019), DOI 10.1038/s42005-019-0218-5.

The paper experimentally prepares four-qubit NMR states representing
spin-1/2 SU(2)-invariant quantum tetrahedra, measures their dihedral
geometry, and uses them to simulate an Ooguri-model spinfoam vertex
amplitude.  Lean records the finite constants and exact algebraic skeleton.
-/

noncomputable section

namespace NMRQuantumSpacetimeSimulator

/-! ## 1. Finite experimental / spin-network constants -/

/-- Number of qubits used for one spin-1/2 quantum tetrahedron. -/
def qubitsPerQuantumTetrahedron : ℕ := 4

/-- Spin label used in the experiment, encoded as twice the spin. -/
def spinHalfTwiceJ : ℕ := 1

/-- Dimension of the fundamental spin-1/2 Hilbert space `H_{1/2} ≃ C²`. -/
def spinHalfHilbertDimension : ℕ := 2

/-- Dimension of `Inv_SU(2)((C²)^⊗4)` for four spin-1/2 legs. -/
def invariantTensorSpaceDimension : ℕ := 2

/-- Number of tetrahedra meeting in the Ooguri spinfoam vertex amplitude. -/
def tetrahedraPerSpinfoamVertex : ℕ := 5

/-- Number of pairwise links among five tetrahedra: `choose(5,2)=10`. -/
def bellLinksPerFiveTetrahedra : ℕ := 10

/-- Number of prepared tetrahedron states reported in the experiment. -/
def preparedQuantumTetrahedra : ℕ := 10

/-- Reported fidelity lower bound, in percent. -/
def reportedFidelityLowerBoundPercent : ℕ := 95

/-- NMR spectrometer frequency reported in the paper, in MHz. -/
def nmrSpectrometerMHz : ℕ := 700

@[simp] theorem qubits_per_quantum_tetrahedron :
    qubitsPerQuantumTetrahedron = 4 := rfl

@[simp] theorem spin_half_twiceJ :
    spinHalfTwiceJ = 1 := rfl

@[simp] theorem spin_half_hilbert_dimension :
    spinHalfHilbertDimension = 2 := rfl

@[simp] theorem invariant_tensor_space_dimension :
    invariantTensorSpaceDimension = 2 := rfl

@[simp] theorem tetrahedra_per_spinfoam_vertex :
    tetrahedraPerSpinfoamVertex = 5 := rfl

@[simp] theorem bell_links_per_five_tetrahedra :
    bellLinksPerFiveTetrahedra = 10 := rfl

@[simp] theorem prepared_quantum_tetrahedra :
    preparedQuantumTetrahedra = 10 := rfl

@[simp] theorem reported_fidelity_lower_bound_percent :
    reportedFidelityLowerBoundPercent = 95 := rfl

@[simp] theorem nmr_spectrometer_mhz :
    nmrSpectrometerMHz = 700 := rfl

/-! ## 2. Minimal spin-1/2 tetrahedron bookkeeping -/

/-- Computational basis labels for one qubit. -/
inductive QubitBit where
  | zero
  | one
  deriving DecidableEq, Repr

/-- The antisymmetric Bell link `|ε⟩=(|01⟩-|10⟩)/√2`, represented by signs. -/
def epsilonBellSign : QubitBit → QubitBit → ℤ
  | .zero, .one => 1
  | .one, .zero => -1
  | _, _ => 0

@[simp] theorem epsilonBell_zero_one :
    epsilonBellSign .zero .one = 1 := rfl

@[simp] theorem epsilonBell_one_zero :
    epsilonBellSign .one .zero = -1 := rfl

@[simp] theorem epsilonBell_zero_zero :
    epsilonBellSign .zero .zero = 0 := rfl

@[simp] theorem epsilonBell_one_one :
    epsilonBellSign .one .one = 0 := rfl

/-- Number of antisymmetric nonzero computational-basis components. -/
def epsilonBellSupportCount : ℕ := 2

@[simp] theorem epsilonBell_support_count :
    epsilonBellSupportCount = 2 := rfl

/-- Pairwise face-gluing links among `n` tetrahedra. -/
def pairwiseLinkCount (n : ℕ) : ℕ := n * (n - 1) / 2

@[simp] theorem pairwiseLinkCount_five :
    pairwiseLinkCount 5 = 10 := by
  norm_num [pairwiseLinkCount]

/-- The vertex amplitude may be read as a transition from `m` tetrahedra to
`5-m` tetrahedra, for `m < 5`. -/
def transitionComplement (m : ℕ) : ℕ := tetrahedraPerSpinfoamVertex - m

theorem transitionComplement_add (m : ℕ) (hm : m ≤ tetrahedraPerSpinfoamVertex) :
    m + transitionComplement m = tetrahedraPerSpinfoamVertex := by
  rw [transitionComplement]
  exact Nat.add_sub_of_le hm

/-! ## 3. Synthesis -/

/-- Capstone synthesis: finite constants and algebraic interfaces compile. -/
theorem nmr_quantum_spacetime_simulator_synthesis :
    qubitsPerQuantumTetrahedron = 4 ∧
    spinHalfTwiceJ = 1 ∧
    spinHalfHilbertDimension = 2 ∧
    invariantTensorSpaceDimension = 2 ∧
    tetrahedraPerSpinfoamVertex = 5 ∧
    bellLinksPerFiveTetrahedra = 10 ∧
    pairwiseLinkCount 5 = 10 ∧
    preparedQuantumTetrahedra = 10 ∧
    reportedFidelityLowerBoundPercent = 95 ∧
    nmrSpectrometerMHz = 700 ∧
    epsilonBellSign .zero .one = 1 ∧
    epsilonBellSign .one .zero = -1 ∧
    epsilonBellSign .zero .zero = 0 ∧
    epsilonBellSign .one .one = 0 ∧
    WeakIsospinSU2.I₁ * WeakIsospinSU2.I₂ - WeakIsospinSU2.I₂ * WeakIsospinSU2.I₁ =
      (2 * Complex.I) • WeakIsospinSU2.I₃ ∧
    ClebschGordanPenroseNonequilibriumSpinGraph.CGAllowed
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.jHalf
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.jHalf
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.j0 = true ∧
    ClebschGordanPenroseNonequilibriumSpinGraph.CGAllowed
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.jHalf
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.jHalf
      ClebschGordanPenroseNonequilibriumSpinGraph.SpinLabel.j1 = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, pairwiseLinkCount_five, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl,
    WeakIsospinSU2.I₁_comm_I₂,
    ClebschGordanPenroseNonequilibriumSpinGraph.half_tensor_half_allows_singlet,
    ClebschGordanPenroseNonequilibriumSpinGraph.half_tensor_half_allows_triplet⟩

#check nmr_quantum_spacetime_simulator_synthesis

end NMRQuantumSpacetimeSimulator
