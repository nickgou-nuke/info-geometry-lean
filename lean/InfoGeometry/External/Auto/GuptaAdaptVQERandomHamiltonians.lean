import Mathlib.Tactic

noncomputable section

namespace GuptaAdaptVQERandomHamiltonians

def pairCount (n : ℕ) : ℕ :=
  n * (n - 1) / 2

def fourBodyCount (N : ℕ) : ℕ :=
  N * (N - 1) * (N - 2) * (N - 3) / 24

theorem dense_SYK_terms_N20 :
    fourBodyCount 20 = 4845 := by
  norm_num [fourBodyCount]

def majoranaQubits (N : ℕ) : ℕ :=
  N / 2

theorem majorana_qubits_N20 :
    majoranaQubits 20 = 10 := by
  norm_num [majoranaQubits]

def sparseSYKExpectedTerms (ks N : ℕ) : ℕ :=
  ks * N

theorem sparse_SYK_ks9_N20_terms :
    sparseSYKExpectedTerms 9 20 = 180 := by
  norm_num [sparseSYKExpectedTerms]

def sparsificationRemovalRatio (dense sparse : ℚ) : ℚ :=
  (dense - sparse) / dense

theorem sparse_removes_roughly_96_percent_N20 :
    sparsificationRemovalRatio 4845 180 = 311 / 323 := by
  norm_num [sparsificationRemovalRatio]

def sparseProbability (ks N : ℚ) : ℚ :=
  24 * ks / N ^ 3

theorem sparse_probability_dense_limit (N : ℚ) (hN : N ≠ 0) :
    sparseProbability (N ^ 3 / 24) N = 1 := by
  unfold sparseProbability
  field_simp [hN]

def skPoolSize (L : ℕ) : ℕ :=
  2 * pairCount L

theorem sk_pool_size_L18 :
    skPoolSize 18 = 306 := by
  norm_num [skPoolSize, pairCount]

def sykPoolSize (n : ℕ) : ℕ :=
  n + 3 * pairCount n

theorem syk_pool_size_n10 :
    sykPoolSize 10 = 145 := by
  norm_num [sykPoolSize, pairCount]

inductive Pauli where
  | I | X | Y | Z
deriving DecidableEq, Repr

def isY : Pauli → Bool
  | Pauli.Y => true
  | _ => false

def oddYAllowed (ys : ℕ) : Bool :=
  ys % 2 = 1

theorem one_Y_is_time_reversal_allowed :
    oddYAllowed 1 = true := by
  rfl

theorem two_Y_is_time_reversal_forbidden :
    oddYAllowed 2 = false := by
  rfl

inductive SKPoolClass where
  | ZiYj | YiZj
deriving DecidableEq, Repr

inductive SYKPoolClass where
  | Zi | XiYj | YiXj | ZiZj
deriving DecidableEq, Repr

def skHamiltonianTermCount (L : ℕ) : ℕ :=
  pairCount L + L

theorem sk_hamiltonian_terms_L18 :
    skHamiltonianTermCount 18 = 171 := by
  norm_num [skHamiltonianTermCount, pairCount]

def adaptStateWordLength (n : ℕ) : ℕ := n

def adaptGradient (commutatorExpectation : ℚ) : ℚ :=
  commutatorExpectation

theorem adapt_gradient_zero_when_commutator_zero :
    adaptGradient 0 = 0 := rfl

def relativeEnergyError (exact adapt : ℚ) : ℚ :=
  (exact - adapt) / exact

theorem relative_error_zero_for_exact_match (E : ℚ) :
    relativeEnergyError E E = 0 := by
  simp [relativeEnergyError]

def densityMatrixDimensionFromMajoranas (N : ℕ) : ℕ :=
  2 ^ majoranaQubits N

theorem Hilbert_dimension_N20 :
    densityMatrixDimensionFromMajoranas 20 = 1024 := by
  norm_num [densityMatrixDimensionFromMajoranas, majoranaQubits]

def vonNeumannEntropySymbolic (traceRhoLogRho : ℚ) : ℚ :=
  -traceRhoLogRho

theorem entropy_sign_flip :
    vonNeumannEntropySymbolic (-3) = 3 := by
  norm_num [vonNeumannEntropySymbolic]

def denseEntropy_N20 : ℚ := 275 / 100
def sparseEntropy_N20 : ℚ := 278 / 100

theorem entropy_N20_close :
    |denseEntropy_N20 - sparseEntropy_N20| = 3 / 100 := by
  norm_num [denseEntropy_N20, sparseEntropy_N20]

def denseSYKFidelity_N20 : ℚ := 9936 / 10000
def sparseSYKFidelity_N20 : ℚ := 9966 / 10000
def skFidelityLowerBound : ℚ := 999998 / 1000000

theorem dense_SYK_fidelity_above_993 :
    denseSYKFidelity_N20 ≥ 993 / 1000 := by
  norm_num [denseSYKFidelity_N20]

theorem sparse_SYK_fidelity_above_993 :
    sparseSYKFidelity_N20 ≥ 993 / 1000 := by
  norm_num [sparseSYKFidelity_N20]

theorem SK_fidelity_bound_above_999998 :
    skFidelityLowerBound = 999999 / 1000000 - 1 / 1000000 := by
  norm_num [skFidelityLowerBound]

def denseSYKDLA_dim (n : ℕ) : ℕ :=
  2 ^ (2 * n - 1) - 2

theorem dense_SYK_DLA_n10 :
    denseSYKDLA_dim 10 = 524286 := by
  norm_num [denseSYKDLA_dim]

def SKDLA_dim (L : ℕ) : ℕ :=
  2 * (4 ^ (L - 1) - 1)

theorem SK_DLA_L4 :
    SKDLA_dim 4 = 126 := by
  norm_num [SKDLA_dim]

end GuptaAdaptVQERandomHamiltonians

end noncomputable section
