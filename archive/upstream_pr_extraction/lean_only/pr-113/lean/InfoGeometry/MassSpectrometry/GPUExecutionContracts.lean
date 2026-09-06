import Mathlib
import InfoGeometry.MassSpectrometry.MellinMassEncoding
import InfoGeometry.MassSpectrometry.SinkhornAssignment
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling
import InfoGeometry.MassSpectrometry.ValuedFragmentationDAG
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration
import InfoGeometry.Clifford.SpinorRep

/-!
# Tensor-execution contracts for mass spectrometry

This file isolates the mathematically verifiable part of a GPU implementation.
It does not model CUDA, Triton, PyTorch allocation behavior, tensor-core
throughput, shared-memory capacity, device latency, or benchmark numbers.

Instead it proves that the finite operations used by an implementation have
native tensor/matrix realizations with the same algebraic invariants:

* Mellin/log-mass phases are 2D rotations preserving quadratic norm;
* a certified Sinkhorn balance lands in Mathlib's Birkhoff polytope;
* the doubled directed operator satisfies the grading conjugation law batchwise;
* rank- and mass-masked kernels cannot contain forbidden directed transitions;
* the repository's native split Clifford tower has a 4096-dimensional `Cl(6,6)`
  stage and a 64-coordinate spinor carrier;
* executable implementations can be related to specifications by an explicit
  extensional refinement contract.

The `Cl(6,6)` results below use the repository's native Mathlib Clifford tower.
They do not assert hardware residency or performance properties.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix
open scoped BigOperators

/-! ## Generic batched tensor carriers -/

/-- Batched sequence tensor with shape `B × N × d`. -/
abbrev SequenceTensor (B N d : ℕ) :=
  Fin B → Fin N → Fin d → ℝ

/-- Batched square matrix tensor with shape `B × N × N`. -/
abbrev BatchedSquareMatrix (B N : ℕ) :=
  Fin B → Matrix (Fin N) (Fin N) ℝ

/-- Batched doubled square matrix tensor with shape `B × (2N) × (2N)`,
represented by the same sum-index carrier used by `doubledOperator`. -/
abbrev BatchedDoubledMatrix (B N : ℕ) :=
  Fin B → Matrix (DoubledIndex N) (DoubledIndex N) ℝ

/-! ## Mellin pair rotation -/

/-- Two-coordinate Givens rotation. This is the scalar primitive used by a
RoPE-style implementation of a Mellin phase. -/
def givensRotate (θ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 * Real.cos θ - x.2 * Real.sin θ,
   x.1 * Real.sin θ + x.2 * Real.cos θ)

/-- Squared Euclidean norm of a real coordinate pair. -/
def pairNormSq (x : ℝ × ℝ) : ℝ :=
  x.1 ^ 2 + x.2 ^ 2

/-- A Givens/Mellin pair rotation preserves the quadratic norm exactly. -/
theorem pairNormSq_givensRotate (θ : ℝ) (x : ℝ × ℝ) :
    pairNormSq (givensRotate θ x) = pairNormSq x := by
  unfold pairNormSq givensRotate
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Relative Mellin phase angle. -/
def mellinAngle (ω m m₀ : ℝ) : ℝ :=
  ω * logMass m m₀

/-- Common nonzero scaling of mass and reference mass leaves the phase angle
unchanged. -/
theorem mellinAngle_common_scale
    {ω scale m m₀ : ℝ} (hscale : scale ≠ 0) (hm₀ : m₀ ≠ 0) :
    mellinAngle ω (scale * m) (scale * m₀) = mellinAngle ω m m₀ := by
  simp [mellinAngle, logMass_common_scale hscale hm₀]

/-- Consequently the corresponding 2D rotation is common-scale invariant. -/
theorem givensRotate_mellin_common_scale
    {ω scale m m₀ : ℝ} (hscale : scale ≠ 0) (hm₀ : m₀ ≠ 0)
    (x : ℝ × ℝ) :
    givensRotate (mellinAngle ω (scale * m) (scale * m₀)) x =
      givensRotate (mellinAngle ω m m₀) x := by
  rw [mellinAngle_common_scale hscale hm₀]

/-! ## Certified Sinkhorn/Birkhoff execution handoff -/

/-- A proof-carrying balanced assignment is the theorem-level output type of a
numerical Sinkhorn backend. -/
def CertifiedBalancedAssignment {n : ℕ}
    {M : SinkhornAssignment.SinkhornMatrix n}
    (cert : SinkhornAssignment.BalanceCertificate M) :
    {A : AssignmentMatrix n // IsSoftAssignment A} :=
  ⟨SinkhornAssignment.balancedMatrix cert,
    SinkhornAssignment.balancedMatrix_isSoftAssignment cert⟩

/-- Every certified numerical balance therefore admits an exact
Birkhoff-von Neumann decomposition. -/
theorem certifiedBalancedAssignment_decomposes
    {n : ℕ} {M : SinkhornAssignment.SinkhornMatrix n}
    (cert : SinkhornAssignment.BalanceCertificate M) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = SinkhornAssignment.balancedMatrix cert := by
  exact SinkhornAssignment.balancedMatrix_birkhoff_decomposition cert

/-! ## Batched directed doubling -/

/-- Batchwise application of the theorem-owned doubled operator. -/
def batchedDoubledOperator {B n : ℕ}
    (K : BatchedSquareMatrix B n) : BatchedDoubledMatrix B n :=
  fun b => doubledOperator (K b)

/-- The full grading conjugation law holds independently for every batch item. -/
theorem batchedDoubledOperator_grading_conjugation
    {B n : ℕ} (K : BatchedSquareMatrix B n) (b : Fin B) :
    gradingMatrix n * batchedDoubledOperator K b * gradingMatrix n =
      -batchedDoubledOperator K b := by
  exact grading_conjugates_doubledOperator_to_neg (K b)

/-- The batchwise doubled operator is symmetric, even when each directed input
matrix is not symmetric. -/
theorem batchedDoubledOperator_transpose
    {B n : ℕ} (K : BatchedSquareMatrix B n) (b : Fin B) :
    (batchedDoubledOperator K b).transpose = batchedDoubledOperator K b := by
  exact doubledOperator_transpose (K b)

/-! ## Causality masks -/

/-- Mask a square kernel by the abstract rank order of a fragmentation DAG. -/
def rankMaskedKernel {n : ℕ} (D : FragmentationDAG n)
    (K : AssignmentMatrix n) : AssignmentMatrix n :=
  fun u v => if D.rank v < D.rank u then K u v else 0

/-- Any nonzero entry surviving the rank mask is a strictly rank-decreasing
transition. -/
theorem rankMaskedKernel_support_decreases
    {n : ℕ} (D : FragmentationDAG n) (K : AssignmentMatrix n)
    {u v : Fin n} (h : rankMaskedKernel D K u v ≠ 0) :
    D.rank v < D.rank u := by
  by_contra hnot
  have hz : rankMaskedKernel D K u v = 0 := by
    simp [rankMaskedKernel, hnot]
  exact h hz

/-- Mask a square kernel by the physical mass order of a valued fragmentation
DAG. -/
def massMaskedKernel {n : ℕ} (D : ValuedFragmentationDAG n)
    (K : AssignmentMatrix n) : AssignmentMatrix n :=
  fun u v => if D.massOf v < D.massOf u then K u v else 0

/-- Any nonzero entry surviving the physical mask strictly decreases mass. -/
theorem massMaskedKernel_support_decreases
    {n : ℕ} (D : ValuedFragmentationDAG n) (K : AssignmentMatrix n)
    {u v : Fin n} (h : massMaskedKernel D K u v ≠ 0) :
    D.massOf v < D.massOf u := by
  by_contra hnot
  have hz : massMaskedKernel D K u v = 0 := by
    simp [massMaskedKernel, hnot]
  exact h hz

/-- A nonzero mass-masked transition has positive endpoint neutral loss. -/
theorem massMaskedKernel_deltaMass_pos
    {n : ℕ} (D : ValuedFragmentationDAG n) (K : AssignmentMatrix n)
    {u v : Fin n} (h : massMaskedKernel D K u v ≠ 0) :
    0 < D.deltaMass u v := by
  exact sub_pos.mpr (massMaskedKernel_support_decreases D K h)

/-! ## Native split `Cl(6,6)` execution dimensions -/

namespace Cl66Execution

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- Native repository carrier for the split real `Cl(6,6)` stage. -/
abbrev Cl66 := SplitClNNAlg 6

/-- Native recursive spinor coordinate carrier for the sixth split stage. -/
abbrev Spinor64 := SpinorSpace 6

/-- Native matrix carrier acting on the 64-coordinate spinor space. -/
abbrev SpinorMatrix64 := SpinorMatrix 6

/-- The sixth split Clifford stage has real vector-space dimension `4096`. -/
theorem cl66_finrank :
    Module.finrank ℝ Cl66 = 4096 := by
  calc
    Module.finrank ℝ Cl66 = 4 * Module.finrank ℝ (SplitClNNAlg 5) := by
      simpa [Cl66] using splitClNNAlg_finrank_succ 5
    _ = 4096 := by
      rw [splitClNNAlg_finrank_five]

/-- The recursive split spinor carrier at stage six has `64` real coordinates. -/
theorem spinor64_finrank :
    Module.finrank ℝ Spinor64 = 64 := by
  simp [Spinor64, SpinorSpace, Module.finrank_fintype_fun_eq_card]

/-- Endomorphism matrices on the 64-coordinate spinor carrier have `4096`
real coordinates. -/
theorem spinorMatrix64_finrank :
    Module.finrank ℝ SpinorMatrix64 = 4096 := by
  simp [SpinorMatrix64, SpinorMatrix, Module.finrank_matrix]

/-- Arithmetic consistency of the compact matrix readout: `64² = 4096`. -/
theorem spinorMatrix64_coordinate_count :
    (64 : ℕ) * 64 = 4096 := by
  norm_num

/-- The sixth stage is one native split Bott step over the fifth stage. -/
noncomputable abbrev cl66SplitBottStep :=
  InfoGeometry.Clifford.BottPeriodicity.splitBottStep 5

/-- The generic recursive gamma representation exists at stage six and is
surjective onto the 64×64 matrix carrier. -/
theorem spinorRepresentation6_surjective :
    Function.Surjective (spinorRepresentation 6) :=
  splitSpinorRepresentation_surjective_of_gammaTensor 6

end Cl66Execution

/-! ## Backend refinement contracts -/

/-- Extensional correctness contract between an executable backend function and
its theorem-level specification. This is the interface appropriate for a
PyTorch/JAX/Triton implementation to satisfy outside the prover. -/
structure KernelRefinement (Input Output : Type*) where
  specification : Input → Output
  implementation : Input → Output
  correct : ∀ x, implementation x = specification x

namespace KernelRefinement

variable {A B C : Type*}

/-- A certified backend evaluates exactly to its mathematical specification. -/
theorem implementation_eq_specification
    (K : KernelRefinement A B) (x : A) :
    K.implementation x = K.specification x :=
  K.correct x

/-- Correct kernel refinements compose. -/
def comp (K₁ : KernelRefinement A B) (K₂ : KernelRefinement B C) :
    KernelRefinement A C where
  specification := K₂.specification ∘ K₁.specification
  implementation := K₂.implementation ∘ K₁.implementation
  correct := by
    intro x
    simp [Function.comp_def, K₁.correct x, K₂.correct (K₁.specification x)]

/-- Composition preserves extensional correctness. -/
theorem comp_correct (K₁ : KernelRefinement A B) (K₂ : KernelRefinement B C)
    (x : A) :
    (K₁.comp K₂).implementation x = (K₁.comp K₂).specification x :=
  (K₁.comp K₂).correct x

end KernelRefinement

end InfoGeometry.MassSpectrometry
