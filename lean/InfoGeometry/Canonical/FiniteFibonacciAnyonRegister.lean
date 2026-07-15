import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding

/-!
# InfoGeometry.Canonical.FiniteFibonacciAnyonRegister

Finite register bridge for Fibonacci anyons.

This file stays on the theorem side only:

* the finite computational space is the existing `FibonacciComputationalSpace`;
* the finite braid action is the existing projective braid-word readout;
* the register cardinality is the Fibonacci count already proved in the core file.

No analytic conformal-block realization is asserted.
No complex-analytic continuation is used as proof authority.
The intended formal corridor is finite symmetry closure: invariant sectors,
commutator/anticommutator surfaces, and no-leakage block actions.
No fault-tolerance theorem.
-/

namespace FiniteFibonacciAnyonRegister

open FiniteFibonacciAnyonBraiding
open FiniteMajoranaBraiding
open FiniteMajoranaProjectiveBraiding

/-- Finite computational register carried by `2N + 2` Fibonacci anyons. -/
abbrev FibonacciAnyonRegister (N : ℕ) : Type :=
  FibonacciComputationalSpace N

/-- The register cardinality is exactly the Fibonacci count. -/
theorem register_card (N : ℕ) :
    Fintype.card (FibonacciAnyonRegister N) = Nat.fib (2 * N + 1) :=
  card_fibonacciComputationalSpace N

/-! ## Finite computational vectors -/

/-- The bit strings indexing the `N` computational qubits. -/
abbrev FibonacciComputationalVector (N : ℕ) : Type :=
  Fin N → Bool

/-- The finite computational vectors have cardinality `2^N`. -/
theorem computationalVector_card (N : ℕ) :
    Fintype.card (FibonacciComputationalVector N) = 2 ^ N := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Read a computational bit as a Fibonacci intermediate charge. -/
def bitCharge : Bool → FibonacciCharge
  | false => FibonacciCharge.one
  | true => FibonacciCharge.eps

@[simp]
theorem bitCharge_false : bitCharge false = FibonacciCharge.one :=
  rfl

@[simp]
theorem bitCharge_true : bitCharge true = FibonacciCharge.eps :=
  rfl

/--
Finite Bratteli-path shorthand for a computational vector.

For `bits : Fin N → Bool`, this is the finite path
`0, 1, α₁, 1, ..., α_N, 1, 0`, with `false = 0` and `true = 1`.
It is only a finite path code, not a conformal-block construction.
-/
def computationalPath (N : ℕ) (bits : FibonacciComputationalVector N) :
    List FibonacciCharge :=
  [FibonacciCharge.one, FibonacciCharge.eps] ++
    List.flatMap (fun i : Fin N => [bitCharge (bits i), FibonacciCharge.eps])
      (List.finRange N) ++
    [FibonacciCharge.one]

@[simp]
theorem computationalPath_zero (bits : FibonacciComputationalVector 0) :
    computationalPath 0 bits = [FibonacciCharge.one, FibonacciCharge.eps, FibonacciCharge.one] := by
  simp [computationalPath]

/-- A computational path for `N` qubits has the expected finite edge-label length. -/
theorem computationalPath_length (N : ℕ) (bits : FibonacciComputationalVector N) :
    (computationalPath N bits).length = 2 * N + 3 := by
  simp [computationalPath, List.length_flatMap]
  omega

/-- The first label in every computational path is the vacuum charge. -/
theorem computationalPath_head (N : ℕ) (bits : FibonacciComputationalVector N) :
    (computationalPath N bits).head? = some FibonacciCharge.one := by
  simp [computationalPath]

/-- The last label in every computational path is the vacuum charge. -/
theorem computationalPath_last (N : ℕ) (bits : FibonacciComputationalVector N) :
    (computationalPath N bits).getLast? = some FibonacciCharge.one := by
  simp only [computationalPath]
  rw [List.getLast?_append]
  rfl

/-- Number of non-computational finite path labels left after selecting `2^N` bit vectors. -/
def nonComputationalCount (N : ℕ) : ℕ :=
  Nat.fib (2 * N + 1) - 2 ^ N

@[simp]
theorem nonComputationalCount_zero :
    nonComputationalCount 0 = 0 := by
  simp [nonComputationalCount]

/-- For one qubit, the finite computational vectors exhaust the Fibonacci count. -/
theorem nonComputationalCount_one :
    nonComputationalCount 1 = 0 := by
  norm_num [nonComputationalCount]

/-- For two qubits, one finite non-computational path remains. -/
theorem nonComputationalCount_two :
    nonComputationalCount 2 = 1 := by
  norm_num [nonComputationalCount]

/-- For three qubits, five finite non-computational paths remain. -/
theorem nonComputationalCount_three :
    nonComputationalCount 3 = 5 := by
  norm_num [nonComputationalCount]

/-! ## Finite one-qubit computational shorthand -/

/-- Finite shape names for the two one-qubit channel pictures in the paper. -/
inductive FibonacciOneQubitShape where
  /-- The `0`-channel triangular pail shorthand. -/
  | triangularPail
  /-- The `1`-channel double-rope shorthand. -/
  | doubleRope
  deriving DecidableEq, Repr

/-- The graphical one-qubit shape attached to a computational bit. -/
def oneQubitShape : Bool → FibonacciOneQubitShape
  | false => FibonacciOneQubitShape.triangularPail
  | true => FibonacciOneQubitShape.doubleRope

@[simp]
theorem oneQubitShape_false :
    oneQubitShape false = FibonacciOneQubitShape.triangularPail :=
  rfl

@[simp]
theorem oneQubitShape_true :
    oneQubitShape true = FibonacciOneQubitShape.doubleRope :=
  rfl

/-- Number of Fibonacci anyons in the simplified `N`-qubit computational register. -/
def computationalAnyonCount (N : ℕ) : ℕ :=
  2 * N + 2

@[simp]
theorem computationalAnyonCount_one : computationalAnyonCount 1 = 4 := by
  norm_num [computationalAnyonCount]

/-- One finite `(ε α ε)` shorthand block, with `false = 0` and `true = 1`. -/
def computationalBlockTriple (bit : Bool) : List FibonacciCharge :=
  [bitCharge true, bitCharge bit, bitCharge true]

@[simp]
theorem computationalBlockTriple_false :
    computationalBlockTriple false = [bitCharge true, bitCharge false, bitCharge true] :=
  rfl

@[simp]
theorem computationalBlockTriple_true :
    computationalBlockTriple true = [bitCharge true, bitCharge true, bitCharge true] :=
  rfl

/-- Full finite one-qubit path code, including the inert outer vacuum endpoints. -/
def singleQubitFullPath (bit : Bool) : List FibonacciCharge :=
  computationalPath 1 (fun _ => bit)

@[simp]
theorem singleQubitFullPath_false :
    singleQubitFullPath false =
      [bitCharge false, bitCharge true, bitCharge false, bitCharge true, bitCharge false] := by
  simp [singleQubitFullPath, computationalPath, bitCharge, List.finRange]

@[simp]
theorem singleQubitFullPath_true :
    singleQubitFullPath true =
      [bitCharge false, bitCharge true, bitCharge true, bitCharge true, bitCharge false] := by
  simp [singleQubitFullPath, computationalPath, bitCharge, List.finRange]

/-- The finite one-qubit computational basis has two vectors. -/
theorem singleQubit_computationalVector_card :
    Fintype.card (FibonacciComputationalVector 1) = 2 := by
  norm_num [computationalVector_card]

/-! ## Finite four-anyon channel readout -/

/--
The two finite channel labels for the four-Fibonacci-anyon block.  `false` is the
vacuum/OPE channel and `true` is the non-vacuum `ε'` channel.  This is only the
finite channel index, not an analytic conformal block.
-/
abbrev FibonacciFourBlockChannel : Type :=
  Bool

/-- The four-anyon channel space has the expected two finite labels. -/
theorem fourBlockChannel_card :
    Fintype.card FibonacciFourBlockChannel = 2 := by
  simp [FibonacciFourBlockChannel]

/-- Paper-facing names for the two diagonal endpoint braid phases. -/
inductive FibonacciEndpointPhase where
  /-- Symbolic readout for the `q^{-4}` phase in the vacuum channel. -/
  | qNegFour
  /-- Symbolic readout for the `q^3` phase in the non-vacuum channel. -/
  | qThree
  deriving DecidableEq, Repr

/-- The diagonal endpoint phase attached to a four-anyon channel. -/
def fourBlockEndpointPhase : FibonacciFourBlockChannel → FibonacciEndpointPhase
  | false => FibonacciEndpointPhase.qNegFour
  | true => FibonacciEndpointPhase.qThree

@[simp]
theorem fourBlockEndpointPhase_vacuum :
    fourBlockEndpointPhase false = FibonacciEndpointPhase.qNegFour :=
  rfl

@[simp]
theorem fourBlockEndpointPhase_epsilonPrime :
    fourBlockEndpointPhase true = FibonacciEndpointPhase.qThree :=
  rfl

/-- Basis vector for one of the two finite four-anyon channels. -/
def fourBlockBasisVector (p : FibonacciFourBlockChannel) :
    FibonacciFourBlockChannel → ℂ :=
  fun q => if q = p then 1 else 0

@[simp]
theorem fourBlockBasisVector_self (p : FibonacciFourBlockChannel) :
    fourBlockBasisVector p p = 1 := by
  simp [fourBlockBasisVector]

@[simp]
theorem fourBlockBasisVector_ne {p q : FibonacciFourBlockChannel} (hpq : q ≠ p) :
    fourBlockBasisVector p q = 0 := by
  simp [fourBlockBasisVector, hpq]

/-- The one-qubit computational basis vector is the corresponding four-block channel vector. -/
def singleQubitBasisVector (bit : Bool) : FibonacciFourBlockChannel → ℂ :=
  fourBlockBasisVector bit

/-- The one-qubit `|0⟩` vector is the finite `01010`/vacuum-channel four-block basis vector. -/
theorem singleQubitBasisVector_zero_eq_fourBlock :
    singleQubitBasisVector false = fourBlockBasisVector false :=
  rfl

/-- The one-qubit `|1⟩` vector is the finite `01110`/non-vacuum-channel four-block basis vector. -/
theorem singleQubitBasisVector_one_eq_fourBlock :
    singleQubitBasisVector true = fourBlockBasisVector true :=
  rfl

/-- The one-qubit `|0⟩` basis vector has unit coordinate on the vacuum channel. -/
@[simp]
theorem singleQubitBasisVector_zero_self :
    singleQubitBasisVector false false = 1 := by
  simp [singleQubitBasisVector]

/-- The one-qubit `|1⟩` basis vector has unit coordinate on the non-vacuum channel. -/
@[simp]
theorem singleQubitBasisVector_one_self :
    singleQubitBasisVector true true = 1 := by
  simp [singleQubitBasisVector]

/-- The one-qubit `|0⟩` basis vector has zero coordinate on the non-vacuum channel. -/
@[simp]
theorem singleQubitBasisVector_zero_at_one :
    singleQubitBasisVector false true = 0 := by
  simp [singleQubitBasisVector, fourBlockBasisVector]

/-- The one-qubit `|1⟩` basis vector has zero coordinate on the vacuum channel. -/
@[simp]
theorem singleQubitBasisVector_one_at_zero :
    singleQubitBasisVector true false = 0 := by
  simp [singleQubitBasisVector, fourBlockBasisVector]

/-! ## Finite computational tensor-product action -/

/-- Finite amplitudes on the `N`-qubit computational bit sector. -/
abbrev ComputationalAmplitude (N : ℕ) : Type :=
  FibonacciComputationalVector N → ℂ

/-- Set one computational bit, leaving all other bits fixed. -/
def setComputationalBit {N : ℕ}
    (bits : FibonacciComputationalVector N) (i : Fin N) (b : Bool) :
    FibonacciComputationalVector N :=
  fun j => if j = i then b else bits j

@[simp]
theorem setComputationalBit_self
    {N : ℕ} (bits : FibonacciComputationalVector N) (i : Fin N) (b : Bool) :
    setComputationalBit bits i b i = b := by
  simp [setComputationalBit]

@[simp]
theorem setComputationalBit_ne
    {N : ℕ} (bits : FibonacciComputationalVector N) {i j : Fin N}
    (h : j ≠ i) (b : Bool) :
    setComputationalBit bits i b j = bits j := by
  simp [setComputationalBit, h]

/--
Kronecker-style action of a one-qubit `2 × 2` scalar matrix on the `i`-th
computational bit, pointwise on the finite bit-sector amplitudes.
-/
def computationalTensorAction {N : ℕ} (M : Bool → Bool → ℂ) (i : Fin N) :
    ComputationalAmplitude N → ComputationalAmplitude N :=
  fun ψ bits =>
    M (bits i) false * ψ (setComputationalBit bits i false) +
      M (bits i) true * ψ (setComputationalBit bits i true)

/-- Diagonal endpoint `R` matrix on one finite computational bit. -/
def endpointRMatrix (qNeg4 q3 : ℂ) : Bool → Bool → ℂ
  | false, false => qNeg4
  | true, true => q3
  | _, _ => 0

/-- General middle `B` matrix on one finite computational bit. -/
def middleBMatrix (B00 B01 B10 B11 : ℂ) : Bool → Bool → ℂ
  | false, false => B00
  | false, true => B01
  | true, false => B10
  | true, true => B11

/-- The computational-sector endpoint `R` action on qubit `i`. -/
def computationalEndpointR {N : ℕ} (qNeg4 q3 : ℂ) (i : Fin N) :
    ComputationalAmplitude N → ComputationalAmplitude N :=
  computationalTensorAction (endpointRMatrix qNeg4 q3) i

/-- The computational-sector middle `B` action on qubit `i`. -/
def computationalMiddleB {N : ℕ} (B00 B01 B10 B11 : ℂ) (i : Fin N) :
    ComputationalAmplitude N → ComputationalAmplitude N :=
  computationalTensorAction (middleBMatrix B00 B01 B10 B11) i

/-- Endpoint `R` action readback on a `0` bit. -/
theorem computationalEndpointR_apply_zero
    {N : ℕ} (qNeg4 q3 : ℂ) (i : Fin N)
    (ψ : ComputationalAmplitude N) (bits : FibonacciComputationalVector N)
    (h : bits i = false) :
    computationalEndpointR qNeg4 q3 i ψ bits =
      qNeg4 * ψ (setComputationalBit bits i false) := by
  simp [computationalEndpointR, computationalTensorAction, endpointRMatrix, h]

/-- Endpoint `R` action readback on a `1` bit. -/
theorem computationalEndpointR_apply_one
    {N : ℕ} (qNeg4 q3 : ℂ) (i : Fin N)
    (ψ : ComputationalAmplitude N) (bits : FibonacciComputationalVector N)
    (h : bits i = true) :
    computationalEndpointR qNeg4 q3 i ψ bits =
      q3 * ψ (setComputationalBit bits i true) := by
  simp [computationalEndpointR, computationalTensorAction, endpointRMatrix, h]

/-- Colexicographic two-qubit computational order inherited by the recursive basis. -/
def twoQubitColexVector (k : Fin 4) : FibonacciComputationalVector 2 :=
  match k with
  | ⟨0, _⟩ => fun _ => false
  | ⟨1, _⟩ => fun j => if j = (⟨0, by omega⟩ : Fin 2) then true else false
  | ⟨2, _⟩ => fun j => if j = (⟨1, by omega⟩ : Fin 2) then true else false
  | ⟨3, _⟩ => fun _ => true

@[simp]
theorem twoQubitColexVector_zero :
    twoQubitColexVector ⟨0, by omega⟩ = (fun _ : Fin 2 => false) :=
  rfl

/-- The second colex two-qubit vector is `|10⟩`, not lexicographic `|01⟩`. -/
theorem twoQubitColexVector_one_bits :
    twoQubitColexVector ⟨1, by omega⟩ ⟨0, by omega⟩ = true ∧
      twoQubitColexVector ⟨1, by omega⟩ ⟨1, by omega⟩ = false := by
  simp [twoQubitColexVector]

/-- The third colex two-qubit vector is `|01⟩`. -/
theorem twoQubitColexVector_two_bits :
    twoQubitColexVector ⟨2, by omega⟩ ⟨0, by omega⟩ = false ∧
      twoQubitColexVector ⟨2, by omega⟩ ⟨1, by omega⟩ = true := by
  simp [twoQubitColexVector]

@[simp]
theorem twoQubitColexVector_three :
    twoQubitColexVector ⟨3, by omega⟩ = (fun _ : Fin 2 => true) :=
  rfl

/-- Finite computational-sector shadow of `b₁ = R ⊗ I` for two qubits. -/
def twoQubit_b1 (qNeg4 q3 : ℂ) : ComputationalAmplitude 2 → ComputationalAmplitude 2 :=
  computationalEndpointR qNeg4 q3 ⟨0, by omega⟩

/-- Finite computational-sector shadow of `b₂ = B ⊗ I` for two qubits. -/
def twoQubit_b2 (B00 B01 B10 B11 : ℂ) :
    ComputationalAmplitude 2 → ComputationalAmplitude 2 :=
  computationalMiddleB B00 B01 B10 B11 ⟨0, by omega⟩

/-- Finite computational-sector shadow of `b₄ = I ⊗ B` for two qubits. -/
def twoQubit_b4 (B00 B01 B10 B11 : ℂ) :
    ComputationalAmplitude 2 → ComputationalAmplitude 2 :=
  computationalMiddleB B00 B01 B10 B11 ⟨1, by omega⟩

/-- Finite computational-sector shadow of `b₅ = I ⊗ R` for two qubits. -/
def twoQubit_b5 (qNeg4 q3 : ℂ) : ComputationalAmplitude 2 → ComputationalAmplitude 2 :=
  computationalEndpointR qNeg4 q3 ⟨1, by omega⟩

/-- The four two-qubit restricted generators target the expected tensor factors. -/
theorem twoQubit_tensorProduct_readback
    (qNeg4 q3 B00 B01 B10 B11 : ℂ) :
    twoQubit_b1 qNeg4 q3 = computationalEndpointR qNeg4 q3 ⟨0, by omega⟩ ∧
      twoQubit_b2 B00 B01 B10 B11 = computationalMiddleB B00 B01 B10 B11 ⟨0, by omega⟩ ∧
      twoQubit_b4 B00 B01 B10 B11 = computationalMiddleB B00 B01 B10 B11 ⟨1, by omega⟩ ∧
      twoQubit_b5 qNeg4 q3 = computationalEndpointR qNeg4 q3 ⟨1, by omega⟩ := by
  simp [twoQubit_b1, twoQubit_b2, twoQubit_b4, twoQubit_b5]

/-- Finite computational-sector shadow of `b₁ = R ⊗ I ⊗ I` for three qubits. -/
def threeQubit_b1 (qNeg4 q3 : ℂ) : ComputationalAmplitude 3 → ComputationalAmplitude 3 :=
  computationalEndpointR qNeg4 q3 ⟨0, by omega⟩

/-- Finite computational-sector shadow of `b₂ = B ⊗ I ⊗ I` for three qubits. -/
def threeQubit_b2 (B00 B01 B10 B11 : ℂ) :
    ComputationalAmplitude 3 → ComputationalAmplitude 3 :=
  computationalMiddleB B00 B01 B10 B11 ⟨0, by omega⟩

/-- Finite computational-sector shadow of `b₄ = I ⊗ B ⊗ I` for three qubits. -/
def threeQubit_b4 (B00 B01 B10 B11 : ℂ) :
    ComputationalAmplitude 3 → ComputationalAmplitude 3 :=
  computationalMiddleB B00 B01 B10 B11 ⟨1, by omega⟩

/-- Finite computational-sector shadow of `b₆ = I ⊗ I ⊗ B` for three qubits. -/
def threeQubit_b6 (B00 B01 B10 B11 : ℂ) :
    ComputationalAmplitude 3 → ComputationalAmplitude 3 :=
  computationalMiddleB B00 B01 B10 B11 ⟨2, by omega⟩

/-- Finite computational-sector shadow of `b₇ = I ⊗ I ⊗ R` for three qubits. -/
def threeQubit_b7 (qNeg4 q3 : ℂ) : ComputationalAmplitude 3 → ComputationalAmplitude 3 :=
  computationalEndpointR qNeg4 q3 ⟨2, by omega⟩

/-- The five three-qubit restricted generators target the expected tensor factors. -/
theorem threeQubit_tensorProduct_readback
    (qNeg4 q3 B00 B01 B10 B11 : ℂ) :
    threeQubit_b1 qNeg4 q3 = computationalEndpointR qNeg4 q3 ⟨0, by omega⟩ ∧
      threeQubit_b2 B00 B01 B10 B11 = computationalMiddleB B00 B01 B10 B11 ⟨0, by omega⟩ ∧
      threeQubit_b4 B00 B01 B10 B11 = computationalMiddleB B00 B01 B10 B11 ⟨1, by omega⟩ ∧
      threeQubit_b6 B00 B01 B10 B11 = computationalMiddleB B00 B01 B10 B11 ⟨2, by omega⟩ ∧
      threeQubit_b7 qNeg4 q3 = computationalEndpointR qNeg4 q3 ⟨2, by omega⟩ := by
  simp [threeQubit_b1, threeQubit_b2, threeQubit_b4, threeQubit_b6, threeQubit_b7]

/--
Finite no-leakage readback for local tensor actions: applying a local matrix to
an amplitude on computational bit strings returns another amplitude on the same
computational bit-string type.
-/
theorem computationalTensorAction_closed
    {N : ℕ} (M : Bool → Bool → ℂ) (i : Fin N) (ψ : ComputationalAmplitude N) :
    ∃ ψ' : ComputationalAmplitude N, ψ' = computationalTensorAction M i ψ :=
  ⟨computationalTensorAction M i ψ, rfl⟩

/--
Finite `N = 3` NC-sector count readback from the already-defined Fibonacci count:
inside the `d₈ = 13` finite path sector, `2^3 = 8` computational vectors leave five
non-computational labels.
-/
theorem threeQubit_nonComputationalCount :
    nonComputationalCount 3 = 5 :=
  nonComputationalCount_three

/--
Finite diagonal endpoint braid action on the two-channel four-anyon vector space.
The scalar parameters stand for the two phases `q^{-4}` and `q^3`; no analytic
complex-analytic continuation or hypergeometric formula is asserted here; the
formal target remains finite symmetry closure.
-/
def fourBlockEndpointBraid (qNeg4 q3 : ℂ) :
    (FibonacciFourBlockChannel → ℂ) → FibonacciFourBlockChannel → ℂ :=
  fun v p => (if p then q3 else qNeg4) * v p

/-- The vacuum channel is an eigenvector for endpoint braiding with phase `q^{-4}`. -/
theorem fourBlockEndpointBraid_vacuum_basis
    (qNeg4 q3 : ℂ) :
    fourBlockEndpointBraid qNeg4 q3 (fourBlockBasisVector false) =
      fun q => qNeg4 * fourBlockBasisVector false q := by
  funext q
  cases q <;> simp [fourBlockEndpointBraid, fourBlockBasisVector]

/-- The non-vacuum channel is an eigenvector for endpoint braiding with phase `q^3`. -/
theorem fourBlockEndpointBraid_epsilonPrime_basis
    (qNeg4 q3 : ℂ) :
    fourBlockEndpointBraid qNeg4 q3 (fourBlockBasisVector true) =
      fun q => q3 * fourBlockBasisVector true q := by
  funext q
  cases q <;> simp [fourBlockEndpointBraid, fourBlockBasisVector]

/-- Endpoint braiding does not mix the two finite four-anyon channel labels. -/
theorem fourBlockEndpointBraid_no_mixing
    (qNeg4 q3 : ℂ) (p q : FibonacciFourBlockChannel) (hpq : q ≠ p) :
    fourBlockEndpointBraid qNeg4 q3 (fourBlockBasisVector p) q = 0 := by
  simp [fourBlockEndpointBraid, fourBlockBasisVector, hpq]

/-- Both endpoint braidings `b₁` and `b₃` have the same finite diagonal channel readout. -/
def fourBlockEndpointBraidAt (_endpoint : Bool) (qNeg4 q3 : ℂ) :
    (FibonacciFourBlockChannel → ℂ) → FibonacciFourBlockChannel → ℂ :=
  fourBlockEndpointBraid qNeg4 q3

@[simp]
theorem fourBlockEndpointBraidAt_left
    (qNeg4 q3 : ℂ) :
    fourBlockEndpointBraidAt false qNeg4 q3 = fourBlockEndpointBraid qNeg4 q3 :=
  rfl

@[simp]
theorem fourBlockEndpointBraidAt_right
    (qNeg4 q3 : ℂ) :
    fourBlockEndpointBraidAt true qNeg4 q3 = fourBlockEndpointBraid qNeg4 q3 :=
  rfl

/--
Finite endpoint diagonalization summary for the four-anyon block: the vacuum and
non-vacuum channel basis vectors are endpoint-braid eigenvectors with the two
symbolic phase labels from the paper.
-/
theorem fourBlockEndpoint_diagonal_summary :
    fourBlockEndpointPhase false = FibonacciEndpointPhase.qNegFour ∧
      fourBlockEndpointPhase true = FibonacciEndpointPhase.qThree := by
  simp

/-! ## Finite dual basis and fusion action -/

/--
Finite fusion-basis change on the two-channel four-anyon vector space.

With parameters `τ` and `σ`, this is the matrix
`[[τ, σ], [σ, -τ]]` in the `(false, true)` channel basis.  In the paper one
has `σ = sqrt τ`, but this file only proves the finite algebraic consequences
from the explicit equation `τ * τ + σ * σ = 1`.
-/
def fourBlockFusionAction (τ σ : ℂ) :
    (FibonacciFourBlockChannel → ℂ) → FibonacciFourBlockChannel → ℂ :=
  fun v p => if p then σ * v false - τ * v true else τ * v false + σ * v true

/-- The finite dual-channel basis vector, expressed in the original `Φ` channel coordinates. -/
def fourBlockDualBasisVector (τ σ : ℂ) (p : FibonacciFourBlockChannel) :
    FibonacciFourBlockChannel → ℂ :=
  fourBlockFusionAction τ σ (fourBlockBasisVector p)

/-- The finite fusion action is homogeneous. -/
theorem fourBlockFusionAction_smul
    (τ σ c : ℂ) (v : FibonacciFourBlockChannel → ℂ) :
    fourBlockFusionAction τ σ (fun p => c * v p) =
      fun p => c * fourBlockFusionAction τ σ v p := by
  funext p
  cases p <;> simp [fourBlockFusionAction] <;> ring_nf

/--
If `τ² + σ² = 1`, the finite fusion action is involutive, matching the paper's
`F² = 1` statement at the purely finite two-channel algebra level.
-/
theorem fourBlockFusionAction_involutive
    (τ σ : ℂ) (hτ : τ * τ + σ * σ = 1)
    (v : FibonacciFourBlockChannel → ℂ) :
    fourBlockFusionAction τ σ (fourBlockFusionAction τ σ v) = v := by
  funext p
  cases p <;> simp [fourBlockFusionAction]
  · calc
      τ * (τ * v false + σ * v true) + σ * (σ * v false - τ * v true)
          = (τ * τ + σ * σ) * v false := by ring
      _ = v false := by rw [hτ]; ring
  · calc
      σ * (τ * v false + σ * v true) - τ * (σ * v false - τ * v true)
          = (τ * τ + σ * σ) * v true := by ring
      _ = v true := by rw [hτ]; ring

/-- The determinant readout of the finite fusion matrix. -/
def fourBlockFusionDet (τ σ : ℂ) : ℂ :=
  τ * (-τ) - σ * σ

/-- If `τ² + σ² = 1`, the finite fusion determinant is `-1`. -/
theorem fourBlockFusionDet_eq_neg_one
    (τ σ : ℂ) (hτ : τ * τ + σ * σ = 1) :
    fourBlockFusionDet τ σ = -1 := by
  unfold fourBlockFusionDet
  calc
    τ * (-τ) - σ * σ = -(τ * τ + σ * σ) := by ring
    _ = -1 := by rw [hτ]

/--
Middle braid action on the original `Φ` channel coordinates, obtained by changing
to the finite dual basis, applying the diagonal endpoint readout, and changing back.
This is the finite algebraic shadow of `B = F R F`; no complex-analytic continuation is asserted.
-/
def fourBlockMiddleBraid (τ σ qNeg4 q3 : ℂ) :
    (FibonacciFourBlockChannel → ℂ) → FibonacciFourBlockChannel → ℂ :=
  fun v => fourBlockFusionAction τ σ
    (fourBlockEndpointBraid qNeg4 q3 (fourBlockFusionAction τ σ v))

/--
In the finite dual basis, the middle braid has the vacuum-channel eigenvalue `q^{-4}`.
-/
theorem fourBlockMiddleBraid_dual_vacuum_basis
    (τ σ qNeg4 q3 : ℂ) (hτ : τ * τ + σ * σ = 1) :
    fourBlockMiddleBraid τ σ qNeg4 q3 (fourBlockDualBasisVector τ σ false) =
      fun p => qNeg4 * fourBlockDualBasisVector τ σ false p := by
  unfold fourBlockMiddleBraid fourBlockDualBasisVector
  rw [fourBlockFusionAction_involutive τ σ hτ]
  rw [fourBlockEndpointBraid_vacuum_basis]
  rw [fourBlockFusionAction_smul]

/--
In the finite dual basis, the middle braid has the non-vacuum-channel eigenvalue `q^3`.
-/
theorem fourBlockMiddleBraid_dual_epsilonPrime_basis
    (τ σ qNeg4 q3 : ℂ) (hτ : τ * τ + σ * σ = 1) :
    fourBlockMiddleBraid τ σ qNeg4 q3 (fourBlockDualBasisVector τ σ true) =
      fun p => q3 * fourBlockDualBasisVector τ σ true p := by
  unfold fourBlockMiddleBraid fourBlockDualBasisVector
  rw [fourBlockFusionAction_involutive τ σ hτ]
  rw [fourBlockEndpointBraid_epsilonPrime_basis]
  rw [fourBlockFusionAction_smul]

/-- The finite fusion action sends the vacuum channel basis vector to coordinates `(τ, σ)`. -/
theorem fourBlockDualBasisVector_vacuum_coords
    (τ σ : ℂ) :
    fourBlockDualBasisVector τ σ false false = τ ∧
      fourBlockDualBasisVector τ σ false true = σ := by
  simp [fourBlockDualBasisVector, fourBlockFusionAction, fourBlockBasisVector]

/-- The finite fusion action sends the non-vacuum channel basis vector to `(σ, -τ)`. -/
theorem fourBlockDualBasisVector_epsilonPrime_coords
    (τ σ : ℂ) :
    fourBlockDualBasisVector τ σ true false = σ ∧
      fourBlockDualBasisVector τ σ true true = -τ := by
  simp [fourBlockDualBasisVector, fourBlockFusionAction, fourBlockBasisVector]

/-! ## Finite electron-payload independence -/

/--
A finite placeholder for the `3r` electron coordinates/payload variables.  The
braid actions below are pointwise in this payload; no electron correlator or
coordinate analytic structure is asserted.
-/
abbrev FibonacciElectronPayload (r : ℕ) : Type :=
  Fin (3 * r) → ℂ

/-- Four-block channel vectors with an arbitrary extra payload index. -/
abbrev FourBlockPayloadVector (α : Type) : Type :=
  FibonacciFourBlockChannel → α → ℂ

/-- Lift any finite four-block channel action pointwise over an inert payload. -/
def liftFourBlockAction {α : Type}
    (A : (FibonacciFourBlockChannel → ℂ) → FibonacciFourBlockChannel → ℂ)
    (v : FourBlockPayloadVector α) : FourBlockPayloadVector α :=
  fun p z => A (fun q => v q z) p

@[simp]
theorem liftFourBlockAction_apply {α : Type}
    (A : (FibonacciFourBlockChannel → ℂ) → FibonacciFourBlockChannel → ℂ)
    (v : FourBlockPayloadVector α) (p : FibonacciFourBlockChannel) (z : α) :
    liftFourBlockAction A v p z = A (fun q => v q z) p :=
  rfl

/-- Endpoint braid action lifted pointwise over an inert electron/payload index. -/
def fourBlockEndpointBraidWithPayload {α : Type} (qNeg4 q3 : ℂ) :
    FourBlockPayloadVector α → FourBlockPayloadVector α :=
  liftFourBlockAction (fourBlockEndpointBraid qNeg4 q3)

/-- Middle braid action `F R F` lifted pointwise over an inert electron/payload index. -/
def fourBlockMiddleBraidWithPayload {α : Type} (τ σ qNeg4 q3 : ℂ) :
    FourBlockPayloadVector α → FourBlockPayloadVector α :=
  liftFourBlockAction (fourBlockMiddleBraid τ σ qNeg4 q3)

/-- A channel basis vector tensored with an arbitrary payload amplitude. -/
def fourBlockPayloadBasisVector {α : Type}
    (p : FibonacciFourBlockChannel) (amp : α → ℂ) : FourBlockPayloadVector α :=
  fun q z => amp z * fourBlockBasisVector p q

/-- A dual-channel basis vector tensored with an arbitrary payload amplitude. -/
def fourBlockPayloadDualBasisVector {α : Type}
    (τ σ : ℂ) (p : FibonacciFourBlockChannel) (amp : α → ℂ) : FourBlockPayloadVector α :=
  fun q z => amp z * fourBlockDualBasisVector τ σ p q

/-- Endpoint braiding remains diagonal after tensoring with any inert payload. -/
theorem fourBlockEndpointBraidWithPayload_vacuum_basis
    {α : Type} (qNeg4 q3 : ℂ) (amp : α → ℂ) :
    fourBlockEndpointBraidWithPayload qNeg4 q3 (fourBlockPayloadBasisVector false amp) =
      fun p z => qNeg4 * fourBlockPayloadBasisVector false amp p z := by
  funext p z
  cases p <;>
    simp [fourBlockEndpointBraidWithPayload, fourBlockPayloadBasisVector,
      fourBlockEndpointBraid, fourBlockBasisVector]

/-- Endpoint braiding remains diagonal on the non-vacuum channel with any inert payload. -/
theorem fourBlockEndpointBraidWithPayload_epsilonPrime_basis
    {α : Type} (qNeg4 q3 : ℂ) (amp : α → ℂ) :
    fourBlockEndpointBraidWithPayload qNeg4 q3 (fourBlockPayloadBasisVector true amp) =
      fun p z => q3 * fourBlockPayloadBasisVector true amp p z := by
  funext p z
  cases p <;>
    simp [fourBlockEndpointBraidWithPayload, fourBlockPayloadBasisVector,
      fourBlockEndpointBraid, fourBlockBasisVector]

/-- The endpoint braid action is homogeneous. -/
theorem fourBlockEndpointBraid_smul
    (qNeg4 q3 c : ℂ) (v : FibonacciFourBlockChannel → ℂ) :
    fourBlockEndpointBraid qNeg4 q3 (fun p => c * v p) =
      fun p => c * fourBlockEndpointBraid qNeg4 q3 v p := by
  funext p
  cases p <;> simp [fourBlockEndpointBraid] <;> ring_nf

/-- The middle braid action `F R F` is homogeneous. -/
theorem fourBlockMiddleBraid_smul
    (τ σ qNeg4 q3 c : ℂ) (v : FibonacciFourBlockChannel → ℂ) :
    fourBlockMiddleBraid τ σ qNeg4 q3 (fun p => c * v p) =
      fun p => c * fourBlockMiddleBraid τ σ qNeg4 q3 v p := by
  unfold fourBlockMiddleBraid
  rw [fourBlockFusionAction_smul]
  rw [fourBlockEndpointBraid_smul]
  rw [fourBlockFusionAction_smul]

/-- The lifted middle braid is diagonal on the vacuum dual channel for any payload. -/
theorem fourBlockMiddleBraidWithPayload_dual_vacuum_basis
    {α : Type} (τ σ qNeg4 q3 : ℂ) (hτ : τ * τ + σ * σ = 1) (amp : α → ℂ) :
    fourBlockMiddleBraidWithPayload τ σ qNeg4 q3
        (fourBlockPayloadDualBasisVector τ σ false amp) =
      fun p z => qNeg4 * fourBlockPayloadDualBasisVector τ σ false amp p z := by
  funext p z
  simp [fourBlockMiddleBraidWithPayload, fourBlockPayloadDualBasisVector]
  rw [fourBlockMiddleBraid_smul]
  rw [fourBlockMiddleBraid_dual_vacuum_basis τ σ qNeg4 q3 hτ]
  ring

/-- The lifted middle braid is diagonal on the non-vacuum dual channel for any payload. -/
theorem fourBlockMiddleBraidWithPayload_dual_epsilonPrime_basis
    {α : Type} (τ σ qNeg4 q3 : ℂ) (hτ : τ * τ + σ * σ = 1) (amp : α → ℂ) :
    fourBlockMiddleBraidWithPayload τ σ qNeg4 q3
        (fourBlockPayloadDualBasisVector τ σ true amp) =
      fun p z => q3 * fourBlockPayloadDualBasisVector τ σ true amp p z := by
  funext p z
  simp [fourBlockMiddleBraidWithPayload, fourBlockPayloadDualBasisVector]
  rw [fourBlockMiddleBraid_smul]
  rw [fourBlockMiddleBraid_dual_epsilonPrime_basis τ σ qNeg4 q3 hτ]
  ring

/--
Specialization of payload independence to the finite `3r` electron-payload index.
The channel braid action is the same for every `r` because the action is pointwise
in `FibonacciElectronPayload r`.
-/
theorem fourBlockMiddleBraid_electronPayload_r_independent
    (r : ℕ) (τ σ qNeg4 q3 : ℂ) (hτ : τ * τ + σ * σ = 1)
    (amp : FibonacciElectronPayload r → ℂ) :
    fourBlockMiddleBraidWithPayload τ σ qNeg4 q3
        (fourBlockPayloadDualBasisVector τ σ true amp) =
      fun p z => q3 * fourBlockPayloadDualBasisVector τ σ true amp p z :=
  fourBlockMiddleBraidWithPayload_dual_epsilonPrime_basis τ σ qNeg4 q3 hτ amp

/-! ## Finite higher-anyon recursive channel algebra -/

/--
Finite recursive dimension sequence for higher Fibonacci-anyon channel blocks.
It is only the finite Bratteli-path count shadow of `Vₙ = Vₙ₋₂ ⊕ Vₙ₋₁` with
`d₂ = d₃ = 1`; no analytic conformal block is constructed here.
-/
def higherBlockDim : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | n + 4 => higherBlockDim (n + 2) + higherBlockDim (n + 3)

/-- Finite index set for the recursively counted higher-anyon channel basis. -/
abbrev HigherBlockBasis (n : ℕ) : Type :=
  Fin (higherBlockDim n)

/-- The finite recursive basis has cardinality `higherBlockDim n`. -/
theorem higherBlockBasis_card (n : ℕ) :
    Fintype.card (HigherBlockBasis n) = higherBlockDim n := by
  simp [HigherBlockBasis]

@[simp]
theorem higherBlockDim_two : higherBlockDim 2 = 1 :=
  rfl

@[simp]
theorem higherBlockDim_three : higherBlockDim 3 = 1 :=
  rfl

@[simp]
theorem higherBlockDim_four : higherBlockDim 4 = 2 :=
  rfl

/-- The finite higher-block dimensions satisfy the Fibonacci recursion. -/
theorem higherBlockDim_step (n : ℕ) :
    higherBlockDim (n + 4) = higherBlockDim (n + 2) + higherBlockDim (n + 3) :=
  rfl

/-- The direct-sum indexing shape for the recursive step. -/
abbrev HigherBlockRecursiveSum (n : ℕ) : Type :=
  HigherBlockBasis n ⊕ HigherBlockBasis (n + 1)

/-- Cardinality of the recursive direct-sum indexing shape. -/
theorem higherBlockRecursiveSum_card (n : ℕ) :
    Fintype.card (HigherBlockRecursiveSum n) = higherBlockDim n + higherBlockDim (n + 1) := by
  simp [HigherBlockRecursiveSum, HigherBlockBasis]

/-- The recursive direct-sum indexing shape has the next Fibonacci-block cardinality. -/
theorem higherBlockRecursiveSum_card_eq_next (n : ℕ) :
    Fintype.card (HigherBlockRecursiveSum (n + 2)) = higherBlockDim (n + 4) := by
  rw [higherBlockRecursiveSum_card, higherBlockDim_step]

/-- The finite two-anyon braid scalar action. -/
def twoAnyonBraid (qNeg4 : ℂ) : (PUnit → ℂ) → PUnit → ℂ :=
  fun v u => qNeg4 * v u

/-- The finite three-anyon braid scalar action. -/
def threeAnyonBraid (q3 : ℂ) : (PUnit → ℂ) → PUnit → ℂ :=
  fun v u => q3 * v u

@[simp]
theorem twoAnyonBraid_basis (qNeg4 : ℂ) :
    twoAnyonBraid qNeg4 (fun _ : PUnit => 1) = fun _ : PUnit => qNeg4 := by
  funext u
  cases u
  simp [twoAnyonBraid]

@[simp]
theorem threeAnyonBraid_basis (q3 : ℂ) :
    threeAnyonBraid q3 (fun _ : PUnit => 1) = fun _ : PUnit => q3 := by
  funext u
  cases u
  simp [threeAnyonBraid]

/--
Finite local singlet braid rule for the admissible triples in (5.9).  The
entries encode `010 ↦ q^{-4}` and `011, 110 ↦ q^3`; all other triples are not
singlet cases in this finite rule.
-/
def higherBraidSingletPhase (qNeg4 q3 : ℂ) : Bool → Bool → Bool → Option ℂ
  | false, true, false => some qNeg4
  | false, true, true => some q3
  | true, true, false => some q3
  | _, _, _ => none

@[simp]
theorem higherBraidSingletPhase_010 (qNeg4 q3 : ℂ) :
    higherBraidSingletPhase qNeg4 q3 false true false = some qNeg4 :=
  rfl

@[simp]
theorem higherBraidSingletPhase_011 (qNeg4 q3 : ℂ) :
    higherBraidSingletPhase qNeg4 q3 false true true = some q3 :=
  rfl

@[simp]
theorem higherBraidSingletPhase_110 (qNeg4 q3 : ℂ) :
    higherBraidSingletPhase qNeg4 q3 true true false = some q3 :=
  rfl

/-- The finite local doublet action for endpoint labels `1, 1` is the four-block `B = F R F`. -/
abbrev higherBraidDoubletAction (τ σ qNeg4 q3 : ℂ) :
    (FibonacciFourBlockChannel → ℂ) → FibonacciFourBlockChannel → ℂ :=
  fourBlockMiddleBraid τ σ qNeg4 q3

/-- Matrix entry `B₀₀` of the finite local doublet action. -/
theorem higherBraidDoubletAction_basis_false_false
    (τ σ qNeg4 q3 : ℂ) :
    higherBraidDoubletAction τ σ qNeg4 q3 (fourBlockBasisVector false) false =
      τ * qNeg4 * τ + σ * q3 * σ := by
  simp [higherBraidDoubletAction, fourBlockMiddleBraid, fourBlockFusionAction,
    fourBlockEndpointBraid, fourBlockBasisVector]
  ring

/-- Matrix entry `B₁₀` of the finite local doublet action. -/
theorem higherBraidDoubletAction_basis_false_true
    (τ σ qNeg4 q3 : ℂ) :
    higherBraidDoubletAction τ σ qNeg4 q3 (fourBlockBasisVector false) true =
      σ * qNeg4 * τ - τ * q3 * σ := by
  simp [higherBraidDoubletAction, fourBlockMiddleBraid, fourBlockFusionAction,
    fourBlockEndpointBraid, fourBlockBasisVector]
  ring

/-- Matrix entry `B₀₁` of the finite local doublet action. -/
theorem higherBraidDoubletAction_basis_true_false
    (τ σ qNeg4 q3 : ℂ) :
    higherBraidDoubletAction τ σ qNeg4 q3 (fourBlockBasisVector true) false =
      τ * qNeg4 * σ - σ * q3 * τ := by
  simp [higherBraidDoubletAction, fourBlockMiddleBraid, fourBlockFusionAction,
    fourBlockEndpointBraid, fourBlockBasisVector]
  ring

/-- Matrix entry `B₁₁` of the finite local doublet action. -/
theorem higherBraidDoubletAction_basis_true_true
    (τ σ qNeg4 q3 : ℂ) :
    higherBraidDoubletAction τ σ qNeg4 q3 (fourBlockBasisVector true) true =
      σ * qNeg4 * σ + τ * q3 * τ := by
  simp [higherBraidDoubletAction, fourBlockMiddleBraid, fourBlockFusionAction,
    fourBlockEndpointBraid, fourBlockBasisVector]
  ring

/--
Finite local-rule summary for higher anyons: the singlet triples use the scalar
readouts, while the `101/111` doublet is governed by the already proved four-block
middle braid action `F R F`.
-/
theorem higherBraidLocalRule_summary (qNeg4 q3 : ℂ) :
    higherBraidSingletPhase qNeg4 q3 false true false = some qNeg4 ∧
      higherBraidSingletPhase qNeg4 q3 false true true = some q3 ∧
      higherBraidSingletPhase qNeg4 q3 true true false = some q3 := by
  simp

/-! ## Finite general block-action shapes -/

/-- Three-block index shape `α ⊕ β ⊕ α` used by the last-generator formulas. -/
abbrev ThreeBlockIndex (α β : Type) : Type :=
  α ⊕ β ⊕ α

/--
Finite block-diagonal restriction action.  This is the algebraic shape of
`π⁽ⁿ⁾(bᵢ) = π⁽ⁿ⁻²⁾(bᵢ) ⊕ π⁽ⁿ⁻¹⁾(bᵢ)`; it does not assert a global braid-group
representation.
-/
def recursiveDirectSumAction {α β : Type}
    (A : (α → ℂ) → α → ℂ) (B : (β → ℂ) → β → ℂ) :
    ((α ⊕ β) → ℂ) → (α ⊕ β) → ℂ :=
  fun v x => match x with
    | Sum.inl a => A (fun a' => v (Sum.inl a')) a
    | Sum.inr b => B (fun b' => v (Sum.inr b')) b

@[simp]
theorem recursiveDirectSumAction_inl {α β : Type}
    (A : (α → ℂ) → α → ℂ) (B : (β → ℂ) → β → ℂ)
    (v : (α ⊕ β) → ℂ) (a : α) :
    recursiveDirectSumAction A B v (Sum.inl a) = A (fun a' => v (Sum.inl a')) a :=
  rfl

@[simp]
theorem recursiveDirectSumAction_inr {α β : Type}
    (A : (α → ℂ) → α → ℂ) (B : (β → ℂ) → β → ℂ)
    (v : (α ⊕ β) → ℂ) (b : β) :
    recursiveDirectSumAction A B v (Sum.inr b) = B (fun b' => v (Sum.inr b')) b :=
  rfl

/-- Cardinality of the three-block index shape. -/
theorem threeBlockIndex_card (α β : Type) [Fintype α] [Fintype β] :
    Fintype.card (ThreeBlockIndex α β) = Fintype.card α + Fintype.card β + Fintype.card α := by
  simp [ThreeBlockIndex]
  omega

/-- The finite index shape for the last two generator block formulas at recursive offset `n`. -/
abbrev HigherLastGeneratorIndex (n : ℕ) : Type :=
  ThreeBlockIndex (HigherBlockBasis n) (HigherBlockBasis (n + 1))

/-- Cardinality readback for the finite last-generator index shape. -/
theorem higherLastGeneratorIndex_card (n : ℕ) :
    Fintype.card (HigherLastGeneratorIndex n) =
      higherBlockDim n + higherBlockDim (n + 1) + higherBlockDim n := by
  simp [HigherLastGeneratorIndex, ThreeBlockIndex, HigherBlockBasis]
  omega

/--
Finite block form for the last generator: `q^{-4}` on the first summand and
`q^3` on the remaining two summands.
-/
def lastGeneratorBlockAction {α β : Type} (qNeg4 q3 : ℂ) :
    (ThreeBlockIndex α β → ℂ) → ThreeBlockIndex α β → ℂ :=
  fun v x => match x with
    | Sum.inl a => qNeg4 * v (Sum.inl a)
    | Sum.inr (Sum.inl b) => q3 * v (Sum.inr (Sum.inl b))
    | Sum.inr (Sum.inr a) => q3 * v (Sum.inr (Sum.inr a))

@[simp]
theorem lastGeneratorBlockAction_left {α β : Type}
    (qNeg4 q3 : ℂ) (v : ThreeBlockIndex α β → ℂ) (a : α) :
    lastGeneratorBlockAction qNeg4 q3 v (Sum.inl a) = qNeg4 * v (Sum.inl a) :=
  rfl

@[simp]
theorem lastGeneratorBlockAction_middle {α β : Type}
    (qNeg4 q3 : ℂ) (v : ThreeBlockIndex α β → ℂ) (b : β) :
    lastGeneratorBlockAction qNeg4 q3 v (Sum.inr (Sum.inl b)) =
      q3 * v (Sum.inr (Sum.inl b)) :=
  rfl

@[simp]
theorem lastGeneratorBlockAction_right {α β : Type}
    (qNeg4 q3 : ℂ) (v : ThreeBlockIndex α β → ℂ) (a : α) :
    lastGeneratorBlockAction qNeg4 q3 v (Sum.inr (Sum.inr a)) =
      q3 * v (Sum.inr (Sum.inr a)) :=
  rfl

/--
Finite block form for the next-to-last generator, matching the paper's
`[[B₀₀ I, 0, B₀₁ I], [0, q³ I, 0], [B₁₀ I, 0, B₁₁ I]]` shape.
-/
def lastButOneBlockAction {α β : Type} (B00 B01 B10 B11 q3 : ℂ) :
    (ThreeBlockIndex α β → ℂ) → ThreeBlockIndex α β → ℂ :=
  fun v x => match x with
    | Sum.inl a => B00 * v (Sum.inl a) + B01 * v (Sum.inr (Sum.inr a))
    | Sum.inr (Sum.inl b) => q3 * v (Sum.inr (Sum.inl b))
    | Sum.inr (Sum.inr a) => B10 * v (Sum.inl a) + B11 * v (Sum.inr (Sum.inr a))

@[simp]
theorem lastButOneBlockAction_left {α β : Type}
    (B00 B01 B10 B11 q3 : ℂ) (v : ThreeBlockIndex α β → ℂ) (a : α) :
    lastButOneBlockAction B00 B01 B10 B11 q3 v (Sum.inl a) =
      B00 * v (Sum.inl a) + B01 * v (Sum.inr (Sum.inr a)) :=
  rfl

@[simp]
theorem lastButOneBlockAction_middle {α β : Type}
    (B00 B01 B10 B11 q3 : ℂ) (v : ThreeBlockIndex α β → ℂ) (b : β) :
    lastButOneBlockAction B00 B01 B10 B11 q3 v (Sum.inr (Sum.inl b)) =
      q3 * v (Sum.inr (Sum.inl b)) :=
  rfl

@[simp]
theorem lastButOneBlockAction_right {α β : Type}
    (B00 B01 B10 B11 q3 : ℂ) (v : ThreeBlockIndex α β → ℂ) (a : α) :
    lastButOneBlockAction B00 B01 B10 B11 q3 v (Sum.inr (Sum.inr a)) =
      B10 * v (Sum.inl a) + B11 * v (Sum.inr (Sum.inr a)) :=
  rfl

/-! ## Finite symmetry-closure sector algebra -/

/-- Finite endomorphism surface for amplitudes on a sector index type. -/
abbrev FiniteSectorAction (α : Type) : Type :=
  (α → ℂ) → α → ℂ

/-- Commutator of two finite sector actions. -/
def actionCommutator {α : Type} (A B : FiniteSectorAction α) : FiniteSectorAction α :=
  fun v x => A (B v) x - B (A v) x

/-- Anticommutator of two finite sector actions. -/
def actionAnticommutator {α : Type} (A B : FiniteSectorAction α) : FiniteSectorAction α :=
  fun v x => A (B v) x + B (A v) x

@[simp]
theorem actionCommutator_apply {α : Type}
    (A B : FiniteSectorAction α) (v : α → ℂ) (x : α) :
    actionCommutator A B v x = A (B v) x - B (A v) x :=
  rfl

@[simp]
theorem actionAnticommutator_apply {α : Type}
    (A B : FiniteSectorAction α) (v : α → ℂ) (x : α) :
    actionAnticommutator A B v x = A (B v) x + B (A v) x :=
  rfl

/-- Finite parity labels for the superbracket extension. -/
inductive FiniteSuperParity where
  | even
  | odd
  deriving DecidableEq, Repr

/--
Finite superbracket extension: the odd/odd bracket is the anticommutator;
all other parity pairs use the commutator.
-/
def actionSuperbracket {α : Type} (p q : FiniteSuperParity)
    (A B : FiniteSectorAction α) : FiniteSectorAction α :=
  match p, q with
  | FiniteSuperParity.odd, FiniteSuperParity.odd => actionAnticommutator A B
  | _, _ => actionCommutator A B

@[simp]
theorem actionSuperbracket_odd_odd {α : Type} (A B : FiniteSectorAction α) :
    actionSuperbracket FiniteSuperParity.odd FiniteSuperParity.odd A B =
      actionAnticommutator A B :=
  rfl

@[simp]
theorem actionSuperbracket_even_left {α : Type}
    (q : FiniteSuperParity) (A B : FiniteSectorAction α) :
    actionSuperbracket FiniteSuperParity.even q A B = actionCommutator A B := by
  cases q <;> rfl

@[simp]
theorem actionSuperbracket_even_right {α : Type}
    (p : FiniteSuperParity) (A B : FiniteSectorAction α) :
    actionSuperbracket p FiniteSuperParity.even A B = actionCommutator A B := by
  cases p <;> rfl

/-- The outer two summands of a three-block split, with the central sector zeroed. -/
def SupportedOnOuter {α β : Type} (v : ThreeBlockIndex α β → ℂ) : Prop :=
  ∀ b : β, v (Sum.inr (Sum.inl b)) = 0

/-- The central summand of a three-block split, with the two outer sectors zeroed. -/
def SupportedOnMiddle {α β : Type} (v : ThreeBlockIndex α β → ℂ) : Prop :=
  ∀ a : α, v (Sum.inl a) = 0 ∧ v (Sum.inr (Sum.inr a)) = 0

/--
Grade involution for the three-sector split: outer sectors are even and the
middle sector is odd.  This is the finite Cartan/supergrading readback used by
this file; it is not a complex-analytic operation.
-/
def sectorGradeInvolution {α β : Type} :
    (ThreeBlockIndex α β → ℂ) → ThreeBlockIndex α β → ℂ :=
  fun v x => match x with
    | Sum.inl a => v (Sum.inl a)
    | Sum.inr (Sum.inl b) => -v (Sum.inr (Sum.inl b))
    | Sum.inr (Sum.inr a) => v (Sum.inr (Sum.inr a))

@[simp]
theorem sectorGradeInvolution_left {α β : Type}
    (v : ThreeBlockIndex α β → ℂ) (a : α) :
    sectorGradeInvolution v (Sum.inl a) = v (Sum.inl a) :=
  rfl

@[simp]
theorem sectorGradeInvolution_middle {α β : Type}
    (v : ThreeBlockIndex α β → ℂ) (b : β) :
    sectorGradeInvolution v (Sum.inr (Sum.inl b)) = -v (Sum.inr (Sum.inl b)) :=
  rfl

@[simp]
theorem sectorGradeInvolution_right {α β : Type}
    (v : ThreeBlockIndex α β → ℂ) (a : α) :
    sectorGradeInvolution v (Sum.inr (Sum.inr a)) = v (Sum.inr (Sum.inr a)) :=
  rfl

/-- The finite sector grade involution squares to the identity. -/
theorem sectorGradeInvolution_involutive {α β : Type}
    (v : ThreeBlockIndex α β → ℂ) :
    sectorGradeInvolution (sectorGradeInvolution v) = v := by
  funext x
  rcases x with a | b
  · rfl
  · rcases b with b | a
    · simp [sectorGradeInvolution]
    · rfl

/-- The grade involution preserves the outer even sector. -/
theorem sectorGradeInvolution_preserves_outer {α β : Type}
    {v : ThreeBlockIndex α β → ℂ} (hv : SupportedOnOuter v) :
    SupportedOnOuter (sectorGradeInvolution v) := by
  intro b
  rw [sectorGradeInvolution_middle, hv b, neg_zero]

/-- The grade involution preserves the middle odd sector. -/
theorem sectorGradeInvolution_preserves_middle {α β : Type}
    {v : ThreeBlockIndex α β → ℂ} (hv : SupportedOnMiddle v) :
    SupportedOnMiddle (sectorGradeInvolution v) := by
  intro a
  rcases hv a with ⟨hl, hr⟩
  constructor
  · rw [sectorGradeInvolution_left, hl]
  · rw [sectorGradeInvolution_right, hr]

/-- The last-generator block action preserves the outer sector. -/
theorem lastGeneratorBlockAction_preserves_outer {α β : Type} (qNeg4 q3 : ℂ)
    {v : ThreeBlockIndex α β → ℂ} (hv : SupportedOnOuter v) :
    SupportedOnOuter (lastGeneratorBlockAction qNeg4 q3 v) := by
  intro b
  rw [lastGeneratorBlockAction_middle, hv b, mul_zero]

/-- The last-generator block action preserves the middle sector. -/
theorem lastGeneratorBlockAction_preserves_middle {α β : Type} (qNeg4 q3 : ℂ)
    {v : ThreeBlockIndex α β → ℂ} (hv : SupportedOnMiddle v) :
    SupportedOnMiddle (lastGeneratorBlockAction qNeg4 q3 v) := by
  intro a
  rcases hv a with ⟨hl, hr⟩
  constructor
  · rw [lastGeneratorBlockAction_left, hl, mul_zero]
  · rw [lastGeneratorBlockAction_right, hr, mul_zero]

/-- The next-to-last-generator block action preserves the outer sector. -/
theorem lastButOneBlockAction_preserves_outer {α β : Type}
    (B00 B01 B10 B11 q3 : ℂ)
    {v : ThreeBlockIndex α β → ℂ} (hv : SupportedOnOuter v) :
    SupportedOnOuter (lastButOneBlockAction B00 B01 B10 B11 q3 v) := by
  intro b
  rw [lastButOneBlockAction_middle, hv b, mul_zero]

/-- The next-to-last-generator block action preserves the middle sector. -/
theorem lastButOneBlockAction_preserves_middle {α β : Type}
    (B00 B01 B10 B11 q3 : ℂ)
    {v : ThreeBlockIndex α β → ℂ} (hv : SupportedOnMiddle v) :
    SupportedOnMiddle (lastButOneBlockAction B00 B01 B10 B11 q3 v) := by
  intro a
  rcases hv a with ⟨hl, hr⟩
  constructor
  · rw [lastButOneBlockAction_left, hl, hr, mul_zero, mul_zero, add_zero]
  · rw [lastButOneBlockAction_right, hl, hr, mul_zero, mul_zero, add_zero]

/--
Finite determinant-exponent recursion shadow.  Values are integer exponents only;
no root-of-unity quotient such as `q^10 = 1` is assumed here.
-/
def braidDetExponent : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => -4
  | 3 => 3
  | n + 4 => braidDetExponent (n + 2) + braidDetExponent (n + 3)

@[simp]
theorem braidDetExponent_two : braidDetExponent 2 = -4 :=
  rfl

@[simp]
theorem braidDetExponent_three : braidDetExponent 3 = 3 :=
  rfl

/-- Determinant exponents obey the same recursive product law additively. -/
theorem braidDetExponent_step (n : ℕ) :
    braidDetExponent (n + 4) = braidDetExponent (n + 2) + braidDetExponent (n + 3) :=
  rfl

/-! ## Finite computational-word transport -/

/-- A finite word of qubit-local computational moves. -/
abbrev FibonacciComputationalWord (N : ℕ) :=
  List (Fin N)

/-- Update one computational bit through a supplied local Boolean gate. -/
def updateComputationalBit
    {N : ℕ} (localGate : Bool → Bool) (i : Fin N)
    (bits : FibonacciComputationalVector N) : FibonacciComputationalVector N :=
  fun j => if j = i then localGate (bits j) else bits j

@[simp]
theorem updateComputationalBit_self
    {N : ℕ} (localGate : Bool → Bool) (i : Fin N)
    (bits : FibonacciComputationalVector N) :
    updateComputationalBit localGate i bits i = localGate (bits i) := by
  simp [updateComputationalBit]

@[simp]
theorem updateComputationalBit_ne
    {N : ℕ} (localGate : Bool → Bool) {i j : Fin N}
    (hji : j ≠ i) (bits : FibonacciComputationalVector N) :
    updateComputationalBit localGate i bits j = bits j := by
  simp [updateComputationalBit, hji]

/-- Local computational updates on distinct qubits commute. -/
theorem updateComputationalBit_comm_of_ne
    {N : ℕ} (f g : Bool → Bool) {i j : Fin N} (hij : i ≠ j)
    (bits : FibonacciComputationalVector N) :
    updateComputationalBit f i (updateComputationalBit g j bits) =
      updateComputationalBit g j (updateComputationalBit f i bits) := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [updateComputationalBit, hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [updateComputationalBit, hki]
    · simp [updateComputationalBit, hki, hkj]

/-- Two local updates on the same computational bit compose as Boolean maps. -/
theorem updateComputationalBit_same
    {N : ℕ} (f g : Bool → Bool) (i : Fin N)
    (bits : FibonacciComputationalVector N) :
    updateComputationalBit f i (updateComputationalBit g i bits) =
      updateComputationalBit (fun b => f (g b)) i bits := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [updateComputationalBit]
  · simp [updateComputationalBit, hki]

/-- Evaluate a finite word of qubit-local moves on computational vectors. -/
def evalComputationalWord
    {N : ℕ} (localGate : Bool → Bool) :
    FibonacciComputationalWord N → FibonacciComputationalVector N → FibonacciComputationalVector N
  | [], bits => bits
  | i :: w, bits => evalComputationalWord localGate w (updateComputationalBit localGate i bits)

@[simp]
theorem evalComputationalWord_nil
    {N : ℕ} (localGate : Bool → Bool) (bits : FibonacciComputationalVector N) :
    evalComputationalWord localGate ([] : FibonacciComputationalWord N) bits = bits :=
  rfl

@[simp]
theorem evalComputationalWord_cons
    {N : ℕ} (localGate : Bool → Bool) (i : Fin N) (w : FibonacciComputationalWord N)
    (bits : FibonacciComputationalVector N) :
    evalComputationalWord localGate (i :: w) bits =
      evalComputationalWord localGate w (updateComputationalBit localGate i bits) :=
  rfl

/--
Finite no-leakage readback for the computational sector: evaluating any finite
word of qubit-local moves returns another computational vector, hence another
finite computational path of the same length.
-/
theorem evalComputationalWord_path_length
    {N : ℕ} (localGate : Bool → Bool) (w : FibonacciComputationalWord N)
    (bits : FibonacciComputationalVector N) :
    (computationalPath N (evalComputationalWord localGate w bits)).length = 2 * N + 3 := by
  exact computationalPath_length N (evalComputationalWord localGate w bits)

/--
The finite computational sector is closed under any finite word of qubit-local
Boolean moves.  This is the finite combinatorial no-leakage statement only.
-/
theorem evalComputationalWord_closed
    {N : ℕ} (localGate : Bool → Bool) (w : FibonacciComputationalWord N)
    (bits : FibonacciComputationalVector N) :
    ∃ bits' : FibonacciComputationalVector N,
      bits' = evalComputationalWord localGate w bits ∧
        (computationalPath N bits').length = 2 * N + 3 := by
  exact ⟨evalComputationalWord localGate w bits, rfl,
    evalComputationalWord_path_length localGate w bits⟩

/-! ## Finite restricted-subgroup computational action -/

/--
Finite labels for the computationally allowed braid generators from the paper's
subgroup `B₃ × B₂ × ... × B₂ × B₃`.

`leftR` models the left endpoint generator `b₁`, `even i` models `b₂, b₄, ..., b₂N`,
and `rightR` models the right endpoint generator `b₂N+1`.  This is only an index
surface for finite computational action; it is not a matrix representation.
-/
inductive FibonacciSubgroupGenerator (N : ℕ) where
  /-- Left endpoint generator, available for nonempty qubit registers. -/
  | leftR (h : 0 < N)
  /-- Even generator acting on one computational qubit. -/
  | even (i : Fin N)
  /-- Right endpoint generator, available for nonempty qubit registers. -/
  | rightR (h : 0 < N)

/-- A finite word in the restricted computational subgroup generators. -/
abbrev FibonacciSubgroupWord (N : ℕ) :=
  List (FibonacciSubgroupGenerator N)

/-- The computational qubit touched by a restricted-subgroup generator. -/
def subgroupGeneratorQubit {N : ℕ} : FibonacciSubgroupGenerator N → Fin N
  | FibonacciSubgroupGenerator.leftR h => ⟨0, h⟩
  | FibonacciSubgroupGenerator.even i => i
  | FibonacciSubgroupGenerator.rightR h => ⟨N - 1, by omega⟩

@[simp]
theorem subgroupGeneratorQubit_leftR {N : ℕ} (h : 0 < N) :
    subgroupGeneratorQubit (FibonacciSubgroupGenerator.leftR (N := N) h) = ⟨0, h⟩ :=
  rfl

@[simp]
theorem subgroupGeneratorQubit_even {N : ℕ} (i : Fin N) :
    subgroupGeneratorQubit (FibonacciSubgroupGenerator.even i) = i :=
  rfl

@[simp]
theorem subgroupGeneratorQubit_rightR {N : ℕ} (h : 0 < N) :
    subgroupGeneratorQubit (FibonacciSubgroupGenerator.rightR (N := N) h) =
      ⟨N - 1, by omega⟩ :=
  rfl

/--
Choose the one-qubit Boolean readout assigned to a restricted-subgroup generator.
Endpoint generators use `endpointGate`; even generators use `evenGate`.
-/
def subgroupGeneratorGate {N : ℕ} (endpointGate evenGate : Bool → Bool) :
    FibonacciSubgroupGenerator N → Bool → Bool
  | FibonacciSubgroupGenerator.leftR _ => endpointGate
  | FibonacciSubgroupGenerator.even _ => evenGate
  | FibonacciSubgroupGenerator.rightR _ => endpointGate

@[simp]
theorem subgroupGeneratorGate_leftR
    {N : ℕ} (endpointGate evenGate : Bool → Bool) (h : 0 < N) :
    subgroupGeneratorGate endpointGate evenGate
      (FibonacciSubgroupGenerator.leftR (N := N) h) = endpointGate :=
  rfl

@[simp]
theorem subgroupGeneratorGate_even
    {N : ℕ} (endpointGate evenGate : Bool → Bool) (i : Fin N) :
    subgroupGeneratorGate endpointGate evenGate (FibonacciSubgroupGenerator.even i) = evenGate :=
  rfl

@[simp]
theorem subgroupGeneratorGate_rightR
    {N : ℕ} (endpointGate evenGate : Bool → Bool) (h : 0 < N) :
    subgroupGeneratorGate endpointGate evenGate
      (FibonacciSubgroupGenerator.rightR (N := N) h) = endpointGate :=
  rfl

/-- Apply one restricted-subgroup generator to a computational vector. -/
def evalSubgroupGenerator
    {N : ℕ} (endpointGate evenGate : Bool → Bool)
    (g : FibonacciSubgroupGenerator N)
    (bits : FibonacciComputationalVector N) : FibonacciComputationalVector N :=
  updateComputationalBit (subgroupGeneratorGate endpointGate evenGate g)
    (subgroupGeneratorQubit g) bits

/-- A restricted-subgroup generator acts on its target qubit by its assigned local gate. -/
theorem evalSubgroupGenerator_self
    {N : ℕ} (endpointGate evenGate : Bool → Bool)
    (g : FibonacciSubgroupGenerator N) (bits : FibonacciComputationalVector N) :
    evalSubgroupGenerator endpointGate evenGate g bits (subgroupGeneratorQubit g) =
      subgroupGeneratorGate endpointGate evenGate g (bits (subgroupGeneratorQubit g)) := by
  simp [evalSubgroupGenerator]

/-- A restricted-subgroup generator leaves every non-target qubit unchanged. -/
theorem evalSubgroupGenerator_ne
    {N : ℕ} (endpointGate evenGate : Bool → Bool)
    (g : FibonacciSubgroupGenerator N) {j : Fin N}
    (hj : j ≠ subgroupGeneratorQubit g) (bits : FibonacciComputationalVector N) :
    evalSubgroupGenerator endpointGate evenGate g bits j = bits j := by
  simp [evalSubgroupGenerator, hj]

/-- Restricted-subgroup generators with distinct target qubits commute on computational vectors. -/
theorem evalSubgroupGenerator_comm_of_ne
    {N : ℕ} (endpointGate evenGate : Bool → Bool)
    {g h : FibonacciSubgroupGenerator N}
    (hgh : subgroupGeneratorQubit g ≠ subgroupGeneratorQubit h)
    (bits : FibonacciComputationalVector N) :
    evalSubgroupGenerator endpointGate evenGate g
        (evalSubgroupGenerator endpointGate evenGate h bits) =
      evalSubgroupGenerator endpointGate evenGate h
        (evalSubgroupGenerator endpointGate evenGate g bits) := by
  unfold evalSubgroupGenerator
  exact updateComputationalBit_comm_of_ne _ _ hgh bits

/-- Evaluate a finite word in the restricted subgroup on computational vectors. -/
def evalSubgroupWord
    {N : ℕ} (endpointGate evenGate : Bool → Bool) :
    FibonacciSubgroupWord N → FibonacciComputationalVector N → FibonacciComputationalVector N
  | [], bits => bits
  | g :: w, bits => evalSubgroupWord endpointGate evenGate w
      (evalSubgroupGenerator endpointGate evenGate g bits)

@[simp]
theorem evalSubgroupWord_nil
    {N : ℕ} (endpointGate evenGate : Bool → Bool)
    (bits : FibonacciComputationalVector N) :
    evalSubgroupWord endpointGate evenGate ([] : FibonacciSubgroupWord N) bits = bits :=
  rfl

@[simp]
theorem evalSubgroupWord_cons
    {N : ℕ} (endpointGate evenGate : Bool → Bool)
    (g : FibonacciSubgroupGenerator N) (w : FibonacciSubgroupWord N)
    (bits : FibonacciComputationalVector N) :
    evalSubgroupWord endpointGate evenGate (g :: w) bits =
      evalSubgroupWord endpointGate evenGate w
        (evalSubgroupGenerator endpointGate evenGate g bits) :=
  rfl

/-- Two adjacent restricted-subgroup generators with distinct target qubits commute as a word. -/
theorem evalSubgroupWord_pair_comm_of_ne
    {N : ℕ} (endpointGate evenGate : Bool → Bool)
    {g h : FibonacciSubgroupGenerator N}
    (hgh : subgroupGeneratorQubit g ≠ subgroupGeneratorQubit h)
    (bits : FibonacciComputationalVector N) :
    evalSubgroupWord endpointGate evenGate [g, h] bits =
      evalSubgroupWord endpointGate evenGate [h, g] bits := by
  simp [evalSubgroupGenerator_comm_of_ne endpointGate evenGate hgh]

/-- A restricted-subgroup word stays inside the finite computational path sector. -/
theorem evalSubgroupWord_path_length
    {N : ℕ} (endpointGate evenGate : Bool → Bool) (w : FibonacciSubgroupWord N)
    (bits : FibonacciComputationalVector N) :
    (computationalPath N (evalSubgroupWord endpointGate evenGate w bits)).length =
      2 * N + 3 := by
  exact computationalPath_length N (evalSubgroupWord endpointGate evenGate w bits)

/--
Finite restricted-subgroup no-leakage skeleton: any finite word in the allowed
generators maps a computational vector to another computational vector.
-/
theorem evalSubgroupWord_closed
    {N : ℕ} (endpointGate evenGate : Bool → Bool) (w : FibonacciSubgroupWord N)
    (bits : FibonacciComputationalVector N) :
    ∃ bits' : FibonacciComputationalVector N,
      bits' = evalSubgroupWord endpointGate evenGate w bits ∧
        (computationalPath N bits').length = 2 * N + 3 := by
  exact ⟨evalSubgroupWord endpointGate evenGate w bits, rfl,
    evalSubgroupWord_path_length endpointGate evenGate w bits⟩

/--
For a single qubit, the left endpoint, even, and right endpoint labels all target
the unique computational qubit.
-/
theorem subgroupGeneratorQubit_one (g : FibonacciSubgroupGenerator 1) :
    subgroupGeneratorQubit g = ⟨0, by omega⟩ := by
  cases g with
  | leftR h => rfl
  | even i => ext; omega
  | rightR h => rfl

/--
For two qubits, the left endpoint acts on the first computational qubit and the
right endpoint acts on the second computational qubit.
-/
theorem subgroupEndpointQubits_two :
    subgroupGeneratorQubit (FibonacciSubgroupGenerator.leftR (N := 2) (by omega)) =
        ⟨0, by omega⟩ ∧
      subgroupGeneratorQubit (FibonacciSubgroupGenerator.rightR (N := 2) (by omega)) =
        ⟨1, by omega⟩ := by
  constructor <;> rfl

/--
For two qubits, the left and right endpoint generator labels commute on the
finite computational action because they target distinct qubits.
-/
theorem evalSubgroupWord_left_right_comm_two
    (endpointGate evenGate : Bool → Bool) (bits : FibonacciComputationalVector 2) :
    evalSubgroupWord endpointGate evenGate
        [FibonacciSubgroupGenerator.leftR (N := 2) (by omega),
          FibonacciSubgroupGenerator.rightR (N := 2) (by omega)] bits =
      evalSubgroupWord endpointGate evenGate
        [FibonacciSubgroupGenerator.rightR (N := 2) (by omega),
          FibonacciSubgroupGenerator.leftR (N := 2) (by omega)] bits := by
  apply evalSubgroupWord_pair_comm_of_ne
  simp [subgroupGeneratorQubit]

/--
For two qubits, the left endpoint and the even generator on the second qubit
commute on the finite computational action because they target distinct qubits.
-/
theorem evalSubgroupWord_left_even_second_comm_two
    (endpointGate evenGate : Bool → Bool) (bits : FibonacciComputationalVector 2) :
    evalSubgroupWord endpointGate evenGate
        [FibonacciSubgroupGenerator.leftR (N := 2) (by omega),
          FibonacciSubgroupGenerator.even ⟨1, by omega⟩] bits =
      evalSubgroupWord endpointGate evenGate
        [FibonacciSubgroupGenerator.even ⟨1, by omega⟩,
          FibonacciSubgroupGenerator.leftR (N := 2) (by omega)] bits := by
  apply evalSubgroupWord_pair_comm_of_ne
  simp [subgroupGeneratorQubit]

/--
For two qubits, the right endpoint and the even generator on the first qubit
commute on the finite computational action because they target distinct qubits.
-/
theorem evalSubgroupWord_right_even_first_comm_two
    (endpointGate evenGate : Bool → Bool) (bits : FibonacciComputationalVector 2) :
    evalSubgroupWord endpointGate evenGate
        [FibonacciSubgroupGenerator.rightR (N := 2) (by omega),
          FibonacciSubgroupGenerator.even ⟨0, by omega⟩] bits =
      evalSubgroupWord endpointGate evenGate
        [FibonacciSubgroupGenerator.even ⟨0, by omega⟩,
          FibonacciSubgroupGenerator.rightR (N := 2) (by omega)] bits := by
  apply evalSubgroupWord_pair_comm_of_ne
  simp [subgroupGeneratorQubit]

/--
Paper-facing monodromy readout for Fibonacci braid words.

This is the finite projective braid-word action already supported by the
Majorana braid layer and specialized to the Fibonacci phase surface.
-/
def monodromy {Gate : Type*} [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate) :
    FibonacciBraidWord → Gate :=
  fibonacciProjectiveGate Gate (fibonacciPhaseOfEval χ) readout

/-- The Fibonacci monodromy readout is invariant under the adjacent braid rewrite. -/
theorem monodromy_braid_rewrite
    {Gate : Type*} [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    (i : ℕ) (left right : FibonacciBraidWord) :
    monodromy (Gate := Gate) χ readout (left ++ [i, i + 1, i] ++ right) =
      monodromy (Gate := Gate) χ readout (left ++ [i + 1, i, i + 1] ++ right) := by
  exact fibonacciProjectiveGate_braid_rewrite_of_evalPhase Gate χ readout i left right

/-- The Fibonacci monodromy readout is invariant under separated commutation. -/
theorem monodromy_commute_rewrite
    {Gate : Type*} [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    {i j : ℕ} (hsep : i + 1 < j) (left right : FibonacciBraidWord) :
    monodromy (Gate := Gate) χ readout (left ++ [i, j] ++ right) =
      monodromy (Gate := Gate) χ readout (left ++ [j, i] ++ right) := by
  exact fibonacciProjectiveGate_commute_rewrite_of_evalPhase Gate χ readout hsep left right

end FiniteFibonacciAnyonRegister
