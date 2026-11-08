import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.MD20250430071017MatrixStatistics

/-!
# Repaired MD 20250430070955: finite partition/covariance bridge

Source: `github-nick:nickgou-nuke/MD`, file
`!!!!!!!!!!!!20250430070955.md`.

The source is a broad report on partition functions as a bridge between
information geometry, quantum-state geometry, and spacetime geometry.  Most of
its continuum, QFT, GR, Kähler-Fisher, and emergence claims are stated as
background, analogy, conjecture, hypothesis, or open research program.  This
file extracts the finite theorem-safe core:

* a finite partition function is just a finite sum of nonzero-normalized
  weights;
* normalized finite weights sum to one;
* the partition function of independent finite subsystems factorizes;
* finite expectations and centered observables are defined from the normalized
  weights;
* the finite covariance/Fisher shadow is symmetric;
* a constant observable has zero centered statistic and zero covariance;
* the matrix-valued statistic bridge from `MD20250430071017MatrixStatistics`
  is explicitly reused as the local-configuration surface.

No path integral, differentiability theorem for `log Z`, Kähler-Fisher
realization theorem, Einstein equation, quantum-gravity partition function, or
emergent-spacetime theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.MD20250430070955FinitePartition

open BigOperators

/-- Finite partition function for arbitrary complex weights. -/
def finitePartition {ι : Type} [Fintype ι] (w : ι → ℂ) : ℂ :=
  ∑ i, w i

/-- Normalized finite Gibbs/softmax-like weight, relative to `finitePartition`. -/
def normalizedWeight {ι : Type} [Fintype ι] (w : ι → ℂ) (i : ι) : ℂ :=
  w i / finitePartition w

/-- Finite expectation of a scalar observable under normalized weights. -/
def finiteMean {ι : Type} [Fintype ι] (w : ι → ℂ) (O : ι → ℂ) : ℂ :=
  ∑ i, normalizedWeight w i * O i

/-- Centered scalar observable. -/
def centeredObservable {ι : Type} [Fintype ι]
    (w : ι → ℂ) (O : ι → ℂ) (i : ι) : ℂ :=
  O i - finiteMean w O

/-- Finite covariance/Fisher-shadow bilinear readout. -/
def finiteCovariance {ι : Type} [Fintype ι]
    (w : ι → ℂ) (O P : ι → ℂ) : ℂ :=
  ∑ i, normalizedWeight w i * centeredObservable w O i * centeredObservable w P i

/-- Normalized finite weights sum to one whenever the partition function is nonzero. -/
theorem normalizedWeight_sum_one {ι : Type} [Fintype ι]
    (w : ι → ℂ) (hZ : finitePartition w ≠ 0) :
    ∑ i, normalizedWeight w i = 1 := by
  unfold normalizedWeight finitePartition
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hZ

/-- Independent finite subsystem partition functions factorize. -/
theorem finitePartition_product {ι κ : Type} [Fintype ι] [Fintype κ]
    (w : ι → ℂ) (v : κ → ℂ) :
    finitePartition (fun p : ι × κ => w p.1 * v p.2) =
      finitePartition w * finitePartition v := by
  unfold finitePartition
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum]

/-- The finite covariance/Fisher-shadow matrix is symmetric. -/
theorem finiteCovariance_symmetric {ι : Type} [Fintype ι]
    (w : ι → ℂ) (O P : ι → ℂ) :
    finiteCovariance w O P = finiteCovariance w P O := by
  unfold finiteCovariance
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A constant observable has zero centered statistic after normalization. -/
theorem centeredObservable_zero_of_constant {ι : Type} [Fintype ι]
    (w : ι → ℂ) (hZ : finitePartition w ≠ 0) (c : ℂ) (i : ι) :
    centeredObservable w (fun _ => c) i = 0 := by
  unfold centeredObservable finiteMean
  rw [← Finset.sum_mul]
  rw [normalizedWeight_sum_one w hZ]
  ring

/-- A constant left observable has zero finite covariance. -/
theorem finiteCovariance_zero_left_of_constant {ι : Type} [Fintype ι]
    (w : ι → ℂ) (hZ : finitePartition w ≠ 0) (c : ℂ) (P : ι → ℂ) :
    finiteCovariance w (fun _ => c) P = 0 := by
  simp [finiteCovariance, centeredObservable_zero_of_constant (w := w) hZ c]

/-- A constant right observable has zero finite covariance. -/
theorem finiteCovariance_zero_right_of_constant {ι : Type} [Fintype ι]
    (w : ι → ℂ) (hZ : finitePartition w ≠ 0) (O : ι → ℂ) (c : ℂ) :
    finiteCovariance w O (fun _ => c) = 0 := by
  rw [finiteCovariance_symmetric]
  exact finiteCovariance_zero_left_of_constant w hZ c O

/--
Repaired finite packet for the MD partition-function manuscript.

The last conjunct explicitly carries the previous MD matrix-statistics local
configuration surface forward: Pauli recomposition remains the finite local
matrix-statistic readback used by the pre-geometric ensemble narrative.
-/
theorem repaired_MD20250430070955_finite_partition_packet
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (w : ι → ℂ) (v : κ → ℂ) (hZ : finitePartition w ≠ 0)
    (O P : ι → ℂ) (c : ℂ)
    (q : ι → MD20250430071017MatrixStatistics.LocalMatrixConfig) :
    (∑ i, normalizedWeight w i = 1) ∧
    (finitePartition (fun p : ι × κ => w p.1 * v p.2) =
      finitePartition w * finitePartition v) ∧
    (finiteCovariance w O P = finiteCovariance w P O) ∧
    (finiteCovariance w (fun _ => c) P = 0) ∧
    (∀ i, Section33PauliBiquaternionCompletion.pauliRecompose (q i) = q i) := by
  exact ⟨normalizedWeight_sum_one w hZ,
    finitePartition_product w v,
    finiteCovariance_symmetric w O P,
    finiteCovariance_zero_left_of_constant w hZ c P,
    fun i => MD20250430071017MatrixStatistics.localMatrix_recompose (q i)⟩

end InfoGeometry.Physics.MD20250430070955FinitePartition

end noncomputable section
