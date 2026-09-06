import proofs.EastSU2EquivariantSpinNetworkCircuits

/-!
# Quaternion / quantics tensor-train backend digest

Theorem-honest computational-backend digest for two software repositories supplied
as external witnesses:

* `https://github.com/vleplat/QuatIca` — quaternion numerical linear algebra,
  cited as Leplat et al., *QuatIca: Advanced Numerical Linear Algebra and
  Optimization for Quaternionic Matrices in Python*, arXiv:2603.24074.
* `https://github.com/fh-igd-iet/trainsum` — quantics tensor trains, citing
  arXiv:2602.20226.

This file does **not** certify the numerical software.  It records finite shape
bookkeeping useful for connecting these packages to external audit/computation
layers:

* a quaternion scalar has four real components;
* an `m × n` quaternion matrix has `4mn` real scalar components;
* the standard complex adjoint/doubling representation of an `m × n` quaternion
  matrix has shape `(2m) × (2n)` and therefore also `4mn` complex entries;
* a uniform tensor train with `d` cores, physical dimension `p`, and internal
  rank `r` has storage `2pr + (d-2)pr²` for `d ≥ 2`;
* quantics with base `b` and `k` digits represents a full dimension `b^k`.

-/

namespace QuaternionQuanticsBackendDigest

/-- Number of real coordinates of one quaternion scalar. -/
def quaternionRealComponents : ℕ := 4

/-- Real scalar storage for an `m × n` quaternion matrix. -/
def quaternionMatrixRealStorage (m n : ℕ) : ℕ :=
  quaternionRealComponents * m * n

/-- Complex-adjoint row count for an `m × n` quaternion matrix. -/
def complexAdjointRows (m : ℕ) : ℕ := 2 * m

/-- Complex-adjoint column count for an `m × n` quaternion matrix. -/
def complexAdjointCols (n : ℕ) : ℕ := 2 * n

/-- Entry count in the standard complex-adjoint/doubling representation. -/
def complexAdjointEntries (m n : ℕ) : ℕ :=
  complexAdjointRows m * complexAdjointCols n

@[simp] theorem quaternion_scalar_has_four_real_components :
    quaternionRealComponents = 4 := rfl

@[simp] theorem quaternion_matrix_real_storage_eq (m n : ℕ) :
    quaternionMatrixRealStorage m n = 4 * m * n := rfl

@[simp] theorem complex_adjoint_entries_eq_real_storage (m n : ℕ) :
    complexAdjointEntries m n = quaternionMatrixRealStorage m n := by
  simp [complexAdjointEntries, complexAdjointRows, complexAdjointCols,
    quaternionMatrixRealStorage, quaternionRealComponents]
  ac_rfl

/-- Simple finite feature labels observed in QuatIca. -/
inductive QuatIcaFeature where
  | quaternionHermitianAdjoint
  | quaternionMatrixMultiply
  | realOrComplexExpansion
  | svdPseudoinverse
  | newtonSchulzPseudoinverse
  | qgmres
  | quaternionTensorUnfoldFold
  | qslstImageRestoration
  | quaternionSDPBarrier
  deriving DecidableEq, Repr

/-- Simple finite feature labels observed in trainsum. -/
inductive TrainSumFeature where
  | tensorTrain
  | quanticsDimension
  | einsum
  | qft
  | wavelet
  | svdQrTruncation
  | linearSolver
  | eigenSolver
  | crossInterpolation
  | backendNumpyTorchCupy
  deriving DecidableEq, Repr

/-- Canonical finite feature lists for audit inventory. -/
def quatIcaFeatureList : List QuatIcaFeature :=
  [.quaternionHermitianAdjoint, .quaternionMatrixMultiply, .realOrComplexExpansion,
   .svdPseudoinverse, .newtonSchulzPseudoinverse, .qgmres,
   .quaternionTensorUnfoldFold, .qslstImageRestoration, .quaternionSDPBarrier]

/-- Canonical finite feature lists for audit inventory. -/
def trainSumFeatureList : List TrainSumFeature :=
  [.tensorTrain, .quanticsDimension, .einsum, .qft, .wavelet, .svdQrTruncation,
   .linearSolver, .eigenSolver, .crossInterpolation, .backendNumpyTorchCupy]

@[simp] theorem quatIca_feature_count : quatIcaFeatureList.length = 9 := rfl

@[simp] theorem trainSum_feature_count : trainSumFeatureList.length = 10 := rfl

/-- Quantics full dimension from base and digit count. -/
def quanticsFullDimension (base digits : ℕ) : ℕ := base ^ digits

@[simp] theorem binary_quantics_dimension_three_digits :
    quanticsFullDimension 2 3 = 8 := rfl

@[simp] theorem binary_quantics_dimension_ten_digits :
    quanticsFullDimension 2 10 = 1024 := rfl

/-- Uniform tensor-train storage for `cores` cores, physical dimension `phys`,
and internal rank `rank`, with boundary ranks one. -/
def uniformTTStorage (cores phys rank : ℕ) : ℕ :=
  match cores with
  | 0 => 0
  | 1 => phys
  | d + 2 => 2 * phys * rank + d * phys * rank * rank

@[simp] theorem uniform_tt_storage_two_cores (phys rank : ℕ) :
    uniformTTStorage 2 phys rank = 2 * phys * rank := by
  simp [uniformTTStorage]

@[simp] theorem uniform_tt_storage_three_cores (phys rank : ℕ) :
    uniformTTStorage 3 phys rank = 2 * phys * rank + phys * rank * rank := by
  simp [uniformTTStorage]

@[simp] theorem uniform_tt_storage_binary_rank_two_four_cores :
    uniformTTStorage 4 2 2 = 24 := by
  norm_num [uniformTTStorage]

/-- Full tensor storage for a uniform `cores`-way tensor with physical dimension
`phys` on each leg. -/
def fullTensorStorage (cores phys : ℕ) : ℕ := phys ^ cores

@[simp] theorem full_binary_tensor_storage_four_cores :
    fullTensorStorage 4 2 = 16 := rfl

/-- Capstone: finite storage/shape bookkeeping compiles. -/
theorem quaternion_quantics_backend_digest_synthesis :
    quaternionRealComponents = 4 ∧
    (∀ m n : ℕ, complexAdjointEntries m n = quaternionMatrixRealStorage m n) ∧
    quatIcaFeatureList.length = 9 ∧
    trainSumFeatureList.length = 10 ∧
    quanticsFullDimension 2 10 = 1024 ∧
    uniformTTStorage 4 2 2 = 24 ∧
    fullTensorStorage 4 2 = 16 ∧
    EastSU2EquivariantSpinNetworkCircuits.commutantDimensionFromMultiplicities 3 = 5 := by
  exact ⟨quaternion_scalar_has_four_real_components,
    complex_adjoint_entries_eq_real_storage,
    quatIca_feature_count,
    trainSum_feature_count,
    binary_quantics_dimension_ten_digits,
    uniform_tt_storage_binary_rank_two_four_cores,
    full_binary_tensor_storage_four_cores,
    EastSU2EquivariantSpinNetworkCircuits.three_qubit_commutant_dimension⟩

end QuaternionQuanticsBackendDigest
