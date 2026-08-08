import proofs.GaugeLnQTensorNetworkToy

/-!
# Xanadu `all-you-need-is-spin` code digest

Finite theorem-honest digest for
`https://github.com/XanaduAI/all-you-need-is-spin`, the companion code for
East--Alonso-Linaje--Park, *All you need is spin: SU(2) equivariant variational
quantum circuits based on spin networks*.

The repository contains PennyLane scripts for SU(2)-equivariant variational
circuits with two-qubit and three-qubit spin-network/Schur gates, Heisenberg
`J₁-J₂` chains, and Kagome-lattice benchmarks.  The upstream README notes that
its main simulations require a custom `PennyLane-Lightning` branch
(`merge_mat_sparse_adj`), so this Lean layer records only finite code-level
bookkeeping.  Numerical VQE performance and hardware/runtime correctness remain
external sockets.
-/

namespace XanaduSpinNetworkCodeDigest

/-- Repository script inventory used in the digest. -/
inductive XanaduSpinScript where
  | gates
  | heisenberg1d
  | kagomeLattice
  deriving DecidableEq, Repr

/-- Gate families exposed by `python_src/gates.py`. -/
inductive SpinNetworkGate where
  | spin2
  | spin3
  | singletPreparation
  deriving DecidableEq, Repr

/-- Benchmark families in the companion code. -/
inductive XanaduSpinBenchmark where
  | oneDimensionalJ1J2Heisenberg
  | kagomeLattice
  deriving DecidableEq, Repr

/-- Script inventory. -/
def scriptInventory : List XanaduSpinScript := [.gates, .heisenberg1d, .kagomeLattice]

/-- Gate inventory. -/
def gateInventory : List SpinNetworkGate := [.spin2, .spin3, .singletPreparation]

/-- Benchmark inventory. -/
def benchmarkInventory : List XanaduSpinBenchmark :=
  [.oneDimensionalJ1J2Heisenberg, .kagomeLattice]

@[simp] theorem script_inventory_count : scriptInventory.length = 3 := rfl

@[simp] theorem gate_inventory_count : gateInventory.length = 3 := rfl

@[simp] theorem benchmark_inventory_count : benchmarkInventory.length = 2 := rfl

/-- Matrix dimension of the two-qubit Schur gate. -/
def spin2SchurDim : ℕ := 4

/-- Matrix dimension of the three-qubit Schur gate. -/
def spin3SchurDim : ℕ := 8

@[simp] theorem spin2_schur_dim_eq : spin2SchurDim = 4 := rfl

@[simp] theorem spin3_schur_dim_eq : spin3SchurDim = 8 := rfl

/-- Number of Pauli Heisenberg terms in the 1D J1-J2 script: XX,YY,ZZ for
nearest and next-nearest periodic edges. -/
def heisenberg1DTermCount (N : ℕ) : ℕ := 6 * N

/-- Parameter count for two-qubit spin gate blocks in the 1D script. -/
def spin2ParamCount (N blocks : ℕ) : ℕ := 2 * N * blocks

/-- Parameter count for three-qubit spin gate blocks in the 1D script. -/
def spin3ParamCount (N blocks : ℕ) : ℕ := 4 * N * blocks

@[simp] theorem heisenberg_terms_N20 : heisenberg1DTermCount 20 = 120 := rfl

@[simp] theorem spin2_params_N20_L4 : spin2ParamCount 20 4 = 160 := rfl

@[simp] theorem spin3_params_N20_L4 : spin3ParamCount 20 4 = 320 := rfl

/-- Kagome example size from the paper/repository narrative. -/
def kagomeExampleQubits : ℕ := 18

@[simp] theorem kagome_example_qubits_eq : kagomeExampleQubits = 18 := rfl

/-- Capstone: code-level finite bookkeeping compiles. -/
theorem xanadu_spin_network_code_digest_synthesis :
    scriptInventory.length = 3 ∧
    gateInventory.length = 3 ∧
    benchmarkInventory.length = 2 ∧
    spin2SchurDim = 4 ∧
    spin3SchurDim = 8 ∧
    heisenberg1DTermCount 20 = 120 ∧
    spin2ParamCount 20 4 = 160 ∧
    spin3ParamCount 20 4 = 320 ∧
    kagomeExampleQubits = 18 ∧
    EastSU2EquivariantSpinNetworkCircuits.commutantDimensionFromMultiplicities 3 = 5 := by
  exact ⟨script_inventory_count,
    gate_inventory_count,
    benchmark_inventory_count,
    spin2_schur_dim_eq,
    spin3_schur_dim_eq,
    heisenberg_terms_N20,
    spin2_params_N20_L4,
    spin3_params_N20_L4,
    kagome_example_qubits_eq,
    EastSU2EquivariantSpinNetworkCircuits.three_qubit_commutant_dimension⟩

end XanaduSpinNetworkCodeDigest
