import proofs.BashoreSpinNetworkQubit

/-!
# East--Alonso-Linaje--Park SU(2)-equivariant spin-network circuits

Theorem-honest formal digest of

Richard D. P. East, Guillermo Alonso-Linaje, Chae-Yeun Park,
*All you need is spin: SU(2) equivariant variational quantum circuits based on
spin networks*, Quantum Science and Technology 11 (2026) 025025,
DOI 10.1088/2058-9565/ae4cff.

The paper constructs SU(2)-equivariant variational quantum circuits using spin
networks and Schur-basis/Schur--Weyl structure, and benchmarks them on SU(2)
symmetric Heisenberg models.  This Lean layer records the finite algebraic
skeleton:

* the two-qubit Schur basis consists of one singlet and three triplets;
* the raw singlet/triplet coefficient vectors have the expected finite norms
  and orthogonality;
* the Schur block sizes are `1 + 3 = 4`;
* the SU(2) commutant dimensions from multiplicities are `2` for two qubits
  and `5` for three qubits.

Full Schur-gate synthesis, twirling equivalence, generalized-permutation
universality, hardware compilation, and VQE benchmark claims remain outside this finite owner.
-/

noncomputable section

namespace EastSU2EquivariantSpinNetworkCircuits

/-- Two-qubit computational basis labels. -/
def twoQubitBasis : List ℕ := [0, 1, 2, 3]

/-- Raw Schur singlet `|01⟩ - |10⟩`. -/
def singletRaw : ℕ → ℚ
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Triplet `|00⟩`. -/
def tripletPlus : ℕ → ℚ
  | 0 => 1
  | _ => 0

/-- Raw triplet `|01⟩ + |10⟩`. -/
def tripletZeroRaw : ℕ → ℚ
  | 1 => 1
  | 2 => 1
  | _ => 0

/-- Triplet `|11⟩`. -/
def tripletMinus : ℕ → ℚ
  | 3 => 1
  | _ => 0

/-- Dot product over the two-qubit basis. -/
def twoQubitDot (a b : ℕ → ℚ) : ℚ :=
  (twoQubitBasis.map (fun n => a n * b n)).sum

@[simp] theorem two_qubit_basis_length : twoQubitBasis.length = 4 := rfl

@[simp] theorem singlet_raw_norm : twoQubitDot singletRaw singletRaw = 2 := by
  norm_num [twoQubitDot, twoQubitBasis, singletRaw]

@[simp] theorem triplet_plus_norm : twoQubitDot tripletPlus tripletPlus = 1 := by
  norm_num [twoQubitDot, twoQubitBasis, tripletPlus]

@[simp] theorem triplet_zero_raw_norm : twoQubitDot tripletZeroRaw tripletZeroRaw = 2 := by
  norm_num [twoQubitDot, twoQubitBasis, tripletZeroRaw]

@[simp] theorem triplet_minus_norm : twoQubitDot tripletMinus tripletMinus = 1 := by
  norm_num [twoQubitDot, twoQubitBasis, tripletMinus]

@[simp] theorem singlet_triplet_zero_orthogonal :
    twoQubitDot singletRaw tripletZeroRaw = 0 := by
  norm_num [twoQubitDot, twoQubitBasis, singletRaw, tripletZeroRaw]

@[simp] theorem singlet_triplet_plus_orthogonal :
    twoQubitDot singletRaw tripletPlus = 0 := by
  norm_num [twoQubitDot, twoQubitBasis, singletRaw, tripletPlus]

@[simp] theorem singlet_triplet_minus_orthogonal :
    twoQubitDot singletRaw tripletMinus = 0 := by
  norm_num [twoQubitDot, twoQubitBasis, singletRaw, tripletMinus]

/-- Schur block size for the two-qubit total angular momentum sector. -/
def twoQubitSchurBlockSize : ℕ → ℕ
  | 0 => 1   -- J = 0 singlet
  | 1 => 3   -- J = 1 triplet
  | _ => 0

@[simp] theorem two_qubit_schur_block_total :
    twoQubitSchurBlockSize 0 + twoQubitSchurBlockSize 1 = 4 := rfl

/-- Multiplicity of irreducible SU(2) sectors for `n` spin-1/2 qubits, in the
minimal cases needed here.  Labels are doubled spin values: `1` means `J=1/2`,
`2` means `J=1`, `3` means `J=3/2`. -/
def spinMultiplicity (n doubledJ : ℕ) : ℕ :=
  match n, doubledJ with
  | 2, 0 => 1
  | 2, 2 => 1
  | 3, 1 => 2
  | 3, 3 => 1
  | _, _ => 0

/-- Commutant dimension from Schur--Weyl multiplicities: `Σ_J m_J^2`. -/
def commutantDimensionFromMultiplicities (n : ℕ) : ℕ :=
  match n with
  | 2 => spinMultiplicity 2 0 ^ 2 + spinMultiplicity 2 2 ^ 2
  | 3 => spinMultiplicity 3 1 ^ 2 + spinMultiplicity 3 3 ^ 2
  | _ => 0

@[simp] theorem two_qubit_commutant_dimension :
    commutantDimensionFromMultiplicities 2 = 2 := rfl

@[simp] theorem three_qubit_commutant_dimension :
    commutantDimensionFromMultiplicities 3 = 5 := rfl

/-- Variational benchmark families named in the paper. -/
inductive SU2BenchmarkLattice where
  | oneDimensionalTriangular
  | kagome
  deriving DecidableEq, Repr

/-- Capstone synthesis: finite Schur/commutant bookkeeping compiles. -/
theorem east_su2_equivariant_spin_network_circuits_synthesis :
    twoQubitBasis.length = 4 ∧
    twoQubitDot singletRaw singletRaw = 2 ∧
    twoQubitDot tripletPlus tripletPlus = 1 ∧
    twoQubitDot tripletZeroRaw tripletZeroRaw = 2 ∧
    twoQubitDot tripletMinus tripletMinus = 1 ∧
    twoQubitDot singletRaw tripletZeroRaw = 0 ∧
    twoQubitSchurBlockSize 0 + twoQubitSchurBlockSize 1 = 4 ∧
    commutantDimensionFromMultiplicities 2 = 2 ∧
    commutantDimensionFromMultiplicities 3 = 5 ∧
    BashoreSpinNetworkQubit.intertwinerQubitDimension = 2 := by
  exact ⟨two_qubit_basis_length,
    singlet_raw_norm,
    triplet_plus_norm,
    triplet_zero_raw_norm,
    triplet_minus_norm,
    singlet_triplet_zero_orthogonal,
    two_qubit_schur_block_total,
    two_qubit_commutant_dimension,
    three_qubit_commutant_dimension,
    BashoreSpinNetworkQubit.intertwiner_qubit_dimension_eq⟩

end EastSU2EquivariantSpinNetworkCircuits

end noncomputable section
