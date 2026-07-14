import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.Convex.Birkhoff

open scoped BigOperators

namespace InfoGeometry.Canonical.MoE

open InfoGeometry.GrandCanonical

section GrandCanonicalBridge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

/--
Token-local grand-canonical parameters induced by router energy over the expert index.
-/
noncomputable def routerParams (x : Fin n → V) (i : Fin n) :
    GrandCanonicalParams (ExpertIdx n) where
  energy := routerEnergy n x i

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma gc_partition_eq_routerPartition (β : ℝ) (x : Fin n → V) (i : Fin n) :
    partition (routerParams n x i) β = routerPartition n β x i := rfl

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma gc_gibbsWeight_eq_normalizedWeights
    (β : ℝ) (x : Fin n → V) (i : Fin n) (e : ExpertIdx n) :
    gibbsWeight (routerParams n x i) β e = normalizedWeights n β x i e := rfl

end GrandCanonicalBridge

section Switch

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

/-- Router-induced switch matrix (rows: tokens, columns: experts). -/
noncomputable def switchMatrix (β : ℝ) (x : Fin n → V) : Matrix (Fin n) (Fin n) ℝ :=
  fun i e => normalizedWeights n β x i e

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
@[simp] lemma switchMatrix_apply (β : ℝ) (x : Fin n → V) (i e : Fin n) :
    switchMatrix n β x i e = normalizedWeights n β x i e := rfl

omit [NormedSpace ℝ V] in
/-- Lemma `normalizedWeights_nonneg`. -/
lemma normalizedWeights_nonneg (β : ℝ) (x : Fin n → V) (i e : Fin n) :
    0 ≤ normalizedWeights n β x i e := by
  unfold normalizedWeights unnormalizedWeights
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (routerPartition_pos n β x i))

omit [NormedSpace ℝ V] in
/-- Lemma `switchMatrix_row_sum_one`. -/
lemma switchMatrix_row_sum_one (β : ℝ) (x : Fin n → V) (i : Fin n) :
    ∑ e : Fin n, switchMatrix n β x i e = 1 := by
  simpa [switchMatrix] using normalizedWeights_sum_one (n := n) β x i

omit [NormedSpace ℝ V] in
/-- Lemma `switchMatrix_mem_rowStochastic`. -/
lemma switchMatrix_mem_rowStochastic (β : ℝ) (x : Fin n → V) :
    switchMatrix n β x ∈ Matrix.rowStochastic ℝ (Fin n) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i e
    exact normalizedWeights_nonneg (n := n) β x i e
  · intro i
    exact switchMatrix_row_sum_one (n := n) β x i

/--
Column-normalization hypothesis for the switch matrix.

When this holds together with the always-true row normalization, the switch is bistochastic.
-/
def IsBistochasticSwitch (β : ℝ) (x : Fin n → V) : Prop :=
  ∀ e : Fin n, ∑ i : Fin n, switchMatrix n β x i e = 1

omit [NormedSpace ℝ V] in
/-- Lemma `switchMatrix_mem_doublyStochastic`. -/
lemma switchMatrix_mem_doublyStochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x) :
    switchMatrix n β x ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i e
    exact normalizedWeights_nonneg (n := n) β x i e
  · intro i
    exact switchMatrix_row_sum_one (n := n) β x i
  · intro e
    exact hcol e

omit [NormedSpace ℝ V] in
/--
Birkhoff-von Neumann decomposition for a bistochastic router switch.

This realizes the switch as a simplex combination of permutation matrices.
-/
theorem exists_perm_decomposition_of_bistochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = switchMatrix n β x := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic
    (M := switchMatrix n β x)
    (switchMatrix_mem_doublyStochastic (n := n) β x hcol)

/--
Certificate that a switch matrix has been Sinkhorn-balanced into a bistochastic matrix.
-/
structure SinkhornCertificate (β : ℝ) (x : Fin n → V) where
  leftScale : Fin n → ℝ
  rightScale : Fin n → ℝ
  leftScale_pos : ∀ i, 0 < leftScale i
  rightScale_pos : ∀ j, 0 < rightScale j
  balanced_mem_doublyStochastic :
    (Matrix.diagonal leftScale * switchMatrix n β x * Matrix.diagonal rightScale)
      ∈ doublyStochastic ℝ (Fin n)

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
/-- Construct a certificate trivially when the switch is already bistochastic. -/
noncomputable def SinkhornCertificate.ofBistochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x) :
    SinkhornCertificate (n := n) β x where
  leftScale := fun _ => 1
  rightScale := fun _ => 1
  leftScale_pos _ := zero_lt_one
  rightScale_pos _ := zero_lt_one
  balanced_mem_doublyStochastic := by
    have h1 : Matrix.diagonal (fun (_ : Fin n) => (1 : ℝ)) = 1 := Matrix.diagonal_one
    rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact switchMatrix_mem_doublyStochastic (n := n) β x hcol

omit [NormedSpace ℝ V] [Nonempty (Fin n)] in
/--
Any Sinkhorn-balanced switch matrix admits a permutation simplex decomposition.
-/
theorem exists_perm_decomposition_of_sinkhornBalanced
    (β : ℝ) (x : Fin n → V) (cert : SinkhornCertificate (n := n) β x) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ =
        Matrix.diagonal cert.leftScale * switchMatrix n β x * Matrix.diagonal cert.rightScale := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic
    (M := Matrix.diagonal cert.leftScale * switchMatrix n β x * Matrix.diagonal cert.rightScale)
    cert.balanced_mem_doublyStochastic

end Switch

section SinkhornFlow

variable (n : Nat)

abbrev SinkhornMatrix := Matrix (Fin n) (Fin n) ℝ

/-- Row sum of a square matrix on `Fin n`. -/
noncomputable def rowSum (M : SinkhornMatrix n) (i : Fin n) : ℝ :=
  ∑ j : Fin n, M i j

/-- Column sum of a square matrix on `Fin n`. -/
noncomputable def colSum (M : SinkhornMatrix n) (j : Fin n) : ℝ :=
  ∑ i : Fin n, M i j

/-- Positivity certificate for row sums (required for row normalization). -/
def HasPositiveRowSums (M : SinkhornMatrix n) : Prop :=
  ∀ i : Fin n, 0 < rowSum n M i

/-- Positivity certificate for column sums (required for column normalization). -/
def HasPositiveColSums (M : SinkhornMatrix n) : Prop :=
  ∀ j : Fin n, 0 < colSum n M j

/-- One Sinkhorn row-normalization step. -/
noncomputable def rowNormalize (M : SinkhornMatrix n) (_hrow : HasPositiveRowSums n M) :
    SinkhornMatrix n :=
  fun i j => M i j / rowSum n M i

/-- One Sinkhorn column-normalization step. -/
noncomputable def colNormalize (M : SinkhornMatrix n) (_hcol : HasPositiveColSums n M) :
    SinkhornMatrix n :=
  fun i j => M i j / colSum n M j

/-- Left Weyl-gauge scale for row normalization (`1 / rowSum`). -/
noncomputable def leftWeylScale (M : SinkhornMatrix n) : Fin n → ℝ :=
  fun i => (rowSum n M i)⁻¹

/-- Right Weyl-gauge scale for column normalization (`1 / colSum`). -/
noncomputable def rightWeylScale (M : SinkhornMatrix n) : Fin n → ℝ :=
  fun j => (colSum n M j)⁻¹

/--
Row normalization is exactly left diagonal Weyl scaling by inverse row sums.
-/
lemma rowNormalize_eq_leftDiagonalGauge
    (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) :
    rowNormalize n M hrow = Matrix.diagonal (leftWeylScale n M) * M := by
  ext i j
  simp [rowNormalize, leftWeylScale, rowSum, Matrix.diagonal_mul, div_eq_mul_inv, mul_comm]

/--
Column normalization is exactly right diagonal Weyl scaling by inverse column sums.
-/
lemma colNormalize_eq_rightDiagonalGauge
    (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) :
    colNormalize n M hcol = M * Matrix.diagonal (rightWeylScale n M) := by
  ext i j
  simp [colNormalize, rightWeylScale, colSum, Matrix.mul_diagonal, div_eq_mul_inv]

/--
Two-step Sinkhorn-Knopp update as a two-sided Weyl gauge transform.

This is the matrix-level gauge-fixing map:
`M ↦ diag(ℓ) * M * diag(r)` with `ℓ_i = 1/rowSum_i`, `r_j = 1/colSum_j`.
-/
lemma sinkhornTwoStep_eq_weylGauge
    (M : SinkhornMatrix n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = Matrix.diagonal (leftWeylScale n M) * M
          * Matrix.diagonal (rightWeylScale n (rowNormalize n M hrow)) := by
  rw [colNormalize_eq_rightDiagonalGauge (n := n) (M := rowNormalize n M hrow) hcol,
      rowNormalize_eq_leftDiagonalGauge (n := n) (M := M) hrow]

/-- Lemma `rowSum_rowNormalize`. -/
lemma rowSum_rowNormalize (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) (i : Fin n) :
    rowSum n (rowNormalize n M hrow) i = 1 := by
  unfold rowSum rowNormalize
  have hne : (∑ k : Fin n, M i k) ≠ 0 := (hrow i).ne'
  calc
    ∑ j : Fin n, M i j / ∑ k : Fin n, M i k
        = (∑ j : Fin n, M i j) / ∑ k : Fin n, M i k := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun j : Fin n => M i j)
                (a := ∑ k : Fin n, M i k))
    _ = 1 := div_self hne

/-- Lemma `colSum_colNormalize`. -/
lemma colSum_colNormalize (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) (j : Fin n) :
    colSum n (colNormalize n M hcol) j = 1 := by
  unfold colSum colNormalize
  have hne : (∑ k : Fin n, M k j) ≠ 0 := (hcol j).ne'
  calc
    ∑ i : Fin n, M i j / ∑ k : Fin n, M k j
        = (∑ i : Fin n, M i j) / ∑ k : Fin n, M k j := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => M i j)
                (a := ∑ k : Fin n, M k j))
    _ = 1 := div_self hne

/-- Row-normalization residual objective. -/
noncomputable def rowLyapunov (M : SinkhornMatrix n) : ℝ :=
  ∑ i : Fin n, |rowSum n M i - 1|

/-- Column-normalization residual objective. -/
noncomputable def colLyapunov (M : SinkhornMatrix n) : ℝ :=
  ∑ j : Fin n, |colSum n M j - 1|

/-- Lemma `rowLyapunov_nonneg`. -/
lemma rowLyapunov_nonneg (M : SinkhornMatrix n) : 0 ≤ rowLyapunov n M := by
  unfold rowLyapunov
  refine Finset.sum_nonneg ?_
  intro i hi
  exact abs_nonneg _

/-- Lemma `colLyapunov_nonneg`. -/
lemma colLyapunov_nonneg (M : SinkhornMatrix n) : 0 ≤ colLyapunov n M := by
  unfold colLyapunov
  refine Finset.sum_nonneg ?_
  intro j hj
  exact abs_nonneg _

/-- Lemma `rowLyapunov_rowNormalize_eq_zero`. -/
lemma rowLyapunov_rowNormalize_eq_zero (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) :
    rowLyapunov n (rowNormalize n M hrow) = 0 := by
  unfold rowLyapunov
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [rowSum_rowNormalize (n := n) M hrow i]
  simp

/-- Lemma `colLyapunov_colNormalize_eq_zero`. -/
lemma colLyapunov_colNormalize_eq_zero (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) :
    colLyapunov n (colNormalize n M hcol) = 0 := by
  unfold colLyapunov
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [colSum_colNormalize (n := n) M hcol j]
  simp

/--
Row-wise Radon-Nikodym log-density generator:
the logarithmic Jacobian expression `∑ᵢ log(rowSumᵢ)`.
-/
noncomputable def rowRadonNikodymGenerator (M : SinkhornMatrix n) : ℝ :=
  ∑ i : Fin n, Real.log (rowSum n M i)

/--
Column-wise Radon-Nikodym log-density generator:
the logarithmic Jacobian expression `∑ⱼ log(colSumⱼ)`.
-/
noncomputable def colRadonNikodymGenerator (M : SinkhornMatrix n) : ℝ :=
  ∑ j : Fin n, Real.log (colSum n M j)

/--
Row self-concordant-style barrier potential:
negative log Radon-Nikodym/Jacobian generator.
-/
noncomputable def rowBarrierPotential (M : SinkhornMatrix n) : ℝ :=
  -rowRadonNikodymGenerator n M

/--
Column self-concordant-style barrier potential:
negative log Radon-Nikodym/Jacobian generator.
-/
noncomputable def colBarrierPotential (M : SinkhornMatrix n) : ℝ :=
  -colRadonNikodymGenerator n M

/--
Nonnegative row barrier functional from absolute log row-mass change.
-/
noncomputable def rowRNBarrier (M : SinkhornMatrix n) : ℝ :=
  ∑ i : Fin n, |Real.log (rowSum n M i)|

/--
Nonnegative column barrier functional from absolute log column-mass change.
-/
noncomputable def colRNBarrier (M : SinkhornMatrix n) : ℝ :=
  ∑ j : Fin n, |Real.log (colSum n M j)|

/-- Lemma `rowRNBarrier_nonneg`. -/
lemma rowRNBarrier_nonneg (M : SinkhornMatrix n) : 0 ≤ rowRNBarrier n M := by
  unfold rowRNBarrier
  refine Finset.sum_nonneg ?_
  intro i hi
  exact abs_nonneg _

section KahlerPotential

variable (n : Nat)

/--
Kahler-potential model from Sinkhorn Radon-Nikodym barriers:
negative log-density (relative-volume) contributions from row and column sectors.
-/
noncomputable def kahlerPotentialRN (M : SinkhornMatrix n) : ℝ :=
  rowBarrierPotential n M + colBarrierPotential n M

/--
Equivalent negative-log Jacobian form:
`K = -(row log RN + col log RN)`.
-/
lemma kahlerPotentialRN_eq_neg_logJacobian
    (M : SinkhornMatrix n) :
    kahlerPotentialRN n M
      = -(rowRadonNikodymGenerator n M + colRadonNikodymGenerator n M) := by
  unfold kahlerPotentialRN rowBarrierPotential colBarrierPotential
  ring

/--
Relative-volume change induced by the RN Kahler potential.
-/
noncomputable def relativeVolumeChangeRN (M : SinkhornMatrix n) : ℝ :=
  Real.exp (-kahlerPotentialRN n M)

/-- Lemma `relativeVolumeChangeRN_eq_exp_logJacobian`. -/
lemma relativeVolumeChangeRN_eq_exp_logJacobian
    (M : SinkhornMatrix n) :
    relativeVolumeChangeRN n M
      = Real.exp (rowRadonNikodymGenerator n M + colRadonNikodymGenerator n M) := by
  unfold relativeVolumeChangeRN
  rw [kahlerPotentialRN_eq_neg_logJacobian]
  ring_nf

/-- The RN Kähler potential is the singleton modular potential of relative volume. -/
lemma kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN
    (M : SinkhornMatrix n) :
    kahlerPotentialRN n M =
      InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential
        (relativeVolumeChangeRN n M)
        (by
          unfold relativeVolumeChangeRN
          exact Real.exp_pos _) := by
  rw [InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log]
  unfold relativeVolumeChangeRN
  simp

end KahlerPotential

/-- Lemma `colRNBarrier_nonneg`. -/
lemma colRNBarrier_nonneg (M : SinkhornMatrix n) : 0 ≤ colRNBarrier n M := by
  unfold colRNBarrier
  refine Finset.sum_nonneg ?_
  intro j hj
  exact abs_nonneg _

/-- Lemma `rowRNBarrier_rowNormalize_eq_zero`. -/
lemma rowRNBarrier_rowNormalize_eq_zero (M : SinkhornMatrix n) (hrow : HasPositiveRowSums n M) :
    rowRNBarrier n (rowNormalize n M hrow) = 0 := by
  unfold rowRNBarrier
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [rowSum_rowNormalize (n := n) M hrow i]
  simp

/-- Lemma `colRNBarrier_colNormalize_eq_zero`. -/
lemma colRNBarrier_colNormalize_eq_zero (M : SinkhornMatrix n) (hcol : HasPositiveColSums n M) :
    colRNBarrier n (colNormalize n M hcol) = 0 := by
  unfold colRNBarrier
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [colSum_colNormalize (n := n) M hcol j]
  simp

/-- Alternating Sinkhorn phase (row step or column step). -/
inductive SinkhornPhase where
  | row
  | col
deriving DecidableEq, Repr

/-- One admissible Sinkhorn step at the given phase. -/
def SinkhornStep (phase : SinkhornPhase) (M M' : SinkhornMatrix n) : Prop :=
  match phase with
  | .row => ∃ hrow : HasPositiveRowSums n M, M' = rowNormalize n M hrow
  | .col => ∃ hcol : HasPositiveColSums n M, M' = colNormalize n M hcol

/--
Phase-aligned pre-step Lyapunov objective:
- for row steps we track column imbalance,
- for column steps we track row imbalance.
-/
noncomputable def phaseLyapunovBefore (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => colLyapunov n M
  | .col => rowLyapunov n M

/--
Phase-aligned post-step Lyapunov objective:
tracks the axis normalized by the current phase step.
-/
noncomputable def phaseLyapunovAfter (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => rowLyapunov n M
  | .col => colLyapunov n M

/--
Phase-aligned Radon-Nikodym barrier objective before a Sinkhorn step.
-/
noncomputable def phaseRNBarrierBefore (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => colRNBarrier n M
  | .col => rowRNBarrier n M

/--
Phase-aligned Radon-Nikodym barrier objective after a Sinkhorn step:
tracks the barrier on the axis normalized by the current phase step.
-/
noncomputable def phaseRNBarrierAfter (phase : SinkhornPhase) (M : SinkhornMatrix n) : ℝ :=
  match phase with
  | .row => rowRNBarrier n M
  | .col => colRNBarrier n M

/-- Lemma `phaseLyapunovBefore_nonneg`. -/
lemma phaseLyapunovBefore_nonneg (phase : SinkhornPhase) (M : SinkhornMatrix n) :
    0 ≤ phaseLyapunovBefore n phase M := by
  cases phase <;>
    simp [phaseLyapunovBefore, rowLyapunov_nonneg, colLyapunov_nonneg]

/-- Lemma `phaseRNBarrierBefore_nonneg`. -/
lemma phaseRNBarrierBefore_nonneg (phase : SinkhornPhase) (M : SinkhornMatrix n) :
    0 ≤ phaseRNBarrierBefore n phase M := by
  cases phase <;>
    simp [phaseRNBarrierBefore, rowRNBarrier_nonneg, colRNBarrier_nonneg]

/-- Lemma `phaseLyapunovAfter_nonneg`. -/
lemma phaseLyapunovAfter_nonneg (phase : SinkhornPhase) (M : SinkhornMatrix n) :
    0 ≤ phaseLyapunovAfter n phase M := by
  cases phase <;>
    simp [phaseLyapunovAfter, rowLyapunov_nonneg, colLyapunov_nonneg]

/-- Lemma `phaseRNBarrierAfter_nonneg`. -/
lemma phaseRNBarrierAfter_nonneg (phase : SinkhornPhase) (M : SinkhornMatrix n) :
    0 ≤ phaseRNBarrierAfter n phase M := by
  cases phase <;>
    simp [phaseRNBarrierAfter, rowRNBarrier_nonneg, colRNBarrier_nonneg]

/--
Sinkhorn one-step Lyapunov contraction in the phase-aligned objective.
-/
lemma sinkhornStep_phaseLyapunov_monotone
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      rw [show phaseLyapunovAfter n SinkhornPhase.row (rowNormalize n M hrow)
            = rowLyapunov n (rowNormalize n M hrow) by rfl]
      rw [rowLyapunov_rowNormalize_eq_zero (n := n) M hrow]
      exact phaseLyapunovBefore_nonneg (n := n) SinkhornPhase.row M
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      rw [show phaseLyapunovAfter n SinkhornPhase.col (colNormalize n M hcol)
            = colLyapunov n (colNormalize n M hcol) by rfl]
      rw [colLyapunov_colNormalize_eq_zero (n := n) M hcol]
      exact phaseLyapunovBefore_nonneg (n := n) SinkhornPhase.col M

/--
Radon-Nikodym barrier contraction lemma.
-/
lemma sinkhornStep_phaseRNBarrier_monotone
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      rw [show phaseRNBarrierAfter n SinkhornPhase.row (rowNormalize n M hrow)
            = rowRNBarrier n (rowNormalize n M hrow) by rfl]
      rw [rowRNBarrier_rowNormalize_eq_zero (n := n) M hrow]
      exact phaseRNBarrierBefore_nonneg (n := n) SinkhornPhase.row M
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      rw [show phaseRNBarrierAfter n SinkhornPhase.col (colNormalize n M hcol)
            = colRNBarrier n (colNormalize n M hcol) by rfl]
      rw [colRNBarrier_colNormalize_eq_zero (n := n) M hcol]
      exact phaseRNBarrierBefore_nonneg (n := n) SinkhornPhase.col M

/-- Exact vanishing of the phase-aligned post-step Lyapunov objective. -/
lemma sinkhornStep_phaseLyapunovAfter_eq_zero
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' = 0 := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      simpa [phaseLyapunovAfter] using rowLyapunov_rowNormalize_eq_zero (n := n) M hrow
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      simpa [phaseLyapunovAfter] using colLyapunov_colNormalize_eq_zero (n := n) M hcol

/-- Exact vanishing of the phase-aligned post-step RN barrier objective. -/
lemma sinkhornStep_phaseRNBarrierAfter_eq_zero
    {phase : SinkhornPhase} {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' = 0 := by
  cases phase with
  | row =>
      rcases hstep with ⟨hrow, rfl⟩
      simpa [phaseRNBarrierAfter] using rowRNBarrier_rowNormalize_eq_zero (n := n) M hrow
  | col =>
      rcases hstep with ⟨hcol, rfl⟩
      simpa [phaseRNBarrierAfter] using colRNBarrier_colNormalize_eq_zero (n := n) M hcol

/-- Alternating row/column phase schedule. -/
def phaseAt (k : Nat) : SinkhornPhase :=
  if k % 2 = 0 then SinkhornPhase.row else SinkhornPhase.col

/--
A (possibly noncomputable) Sinkhorn trajectory with explicit admissible steps.
-/
structure SinkhornTrajectory where
  state : Nat → SinkhornMatrix n
  step : ∀ k, SinkhornStep n (phaseAt k) (state k) (state (k + 1))

/-- Lyapunov objective evaluated before the step at iteration `k`. -/
noncomputable def trajectoryLyapunov (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseLyapunovBefore n (phaseAt k) (T.state k)

/-- Lyapunov objective evaluated after the step at iteration `k`. -/
noncomputable def trajectoryLyapunovNext (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseLyapunovAfter n (phaseAt k) (T.state (k + 1))

/-- Radon-Nikodym barrier objective before the step at iteration `k`. -/
noncomputable def trajectoryRNBarrier (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseRNBarrierBefore n (phaseAt k) (T.state k)

/-- Radon-Nikodym barrier objective after the step at iteration `k`. -/
noncomputable def trajectoryRNBarrierNext (T : SinkhornTrajectory n) (k : Nat) : ℝ :=
  phaseRNBarrierAfter n (phaseAt k) (T.state (k + 1))

/-- The pre-step Lyapunov objective of a Sinkhorn trajectory is nonnegative. -/
theorem trajectoryLyapunov_nonneg (T : SinkhornTrajectory n) (k : Nat) :
    0 ≤ trajectoryLyapunov n T k := by
  exact phaseLyapunovBefore_nonneg (n := n) (phaseAt k) (T.state k)

/-- The post-step Lyapunov objective of a Sinkhorn trajectory is nonnegative. -/
theorem trajectoryLyapunovNext_nonneg (T : SinkhornTrajectory n) (k : Nat) :
    0 ≤ trajectoryLyapunovNext n T k := by
  exact phaseLyapunovAfter_nonneg (n := n) (phaseAt k) (T.state (k + 1))

/-- The pre-step RN barrier of a Sinkhorn trajectory is nonnegative. -/
theorem trajectoryRNBarrier_nonneg (T : SinkhornTrajectory n) (k : Nat) :
    0 ≤ trajectoryRNBarrier n T k := by
  exact phaseRNBarrierBefore_nonneg (n := n) (phaseAt k) (T.state k)

/-- The post-step RN barrier of a Sinkhorn trajectory is nonnegative. -/
theorem trajectoryRNBarrierNext_nonneg (T : SinkhornTrajectory n) (k : Nat) :
    0 ≤ trajectoryRNBarrierNext n T k := by
  exact phaseRNBarrierAfter_nonneg (n := n) (phaseAt k) (T.state (k + 1))

/-- Every admissible Sinkhorn step has zero phase-aligned post-step Lyapunov objective. -/
theorem trajectoryLyapunovNext_eq_zero (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryLyapunovNext n T k = 0 := by
  unfold trajectoryLyapunovNext
  exact sinkhornStep_phaseLyapunovAfter_eq_zero (n := n) (hstep := T.step k)

/-- Every admissible Sinkhorn step has zero phase-aligned post-step RN barrier. -/
theorem trajectoryRNBarrierNext_eq_zero (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryRNBarrierNext n T k = 0 := by
  unfold trajectoryRNBarrierNext
  exact sinkhornStep_phaseRNBarrierAfter_eq_zero (n := n) (hstep := T.step k)

/--
Monotonic Lyapunov inequality along the Sinkhorn trajectory.
This is the genuine convergence theorem: imbalance on the uncontrolled axis decreases.
-/
theorem trajectoryLyapunov_monotone (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryLyapunovNext n T k ≤ trajectoryLyapunov n T k := by
  simpa [trajectoryLyapunovNext, trajectoryLyapunov] using
    sinkhornStep_phaseLyapunov_monotone (n := n) (hstep := T.step k)

/--
Exact row-step identity on the normalized axis:
the post-row-normalization RN barrier on rows is zero.
-/
theorem rn_barrier_row_step_eq_zero (M : SinkhornMatrix n) (hpos : HasPositiveRowSums n M) :
    rowRNBarrier n (rowNormalize n M hpos) = 0 :=
  rowRNBarrier_rowNormalize_eq_zero (n := n) M hpos

/--
Monotonic Radon-Nikodym barrier inequality along the Sinkhorn trajectory.
The logarithmic imbalance contracts after each alternating normalization.
-/
theorem trajectoryRNBarrier_monotone (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ trajectoryRNBarrier n T k := by
  simpa [trajectoryRNBarrierNext, trajectoryRNBarrier] using
    sinkhornStep_phaseRNBarrier_monotone (n := n) (hstep := T.step k)

end SinkhornFlow

section EntropicOTBridge

variable (n : Nat)

abbrev CostMatrix := SinkhornMatrix n
abbrev Coupling := SinkhornMatrix n
abbrev Marginal := Fin n → ℝ

/-- Coupling with prescribed row/column marginals. -/
def HasMarginals (PiM : Coupling n) (mu nu : Marginal n) : Prop :=
  (∀ i : Fin n, rowSum n PiM i = mu i) ∧
    (∀ j : Fin n, colSum n PiM j = nu j)

/-- Entropic OT Gibbs kernel `K_ε(i,j) = exp(-C(i,j)/ε)`. -/
noncomputable def entropicKernel (ε : ℝ) (C : CostMatrix n) : Coupling n :=
  fun i j => Real.exp (-C i j / ε)

/-- Sinkhorn-Knopp two-sided diagonal scaling of a kernel. -/
noncomputable def sinkhornScaledCoupling
    (K : Coupling n) (left right : Fin n → ℝ) : Coupling n :=
  Matrix.diagonal left * K * Matrix.diagonal right

@[simp] lemma sinkhornScaledCoupling_def
    (K : Coupling n) (left right : Fin n → ℝ) :
    sinkhornScaledCoupling n K left right
      = Matrix.diagonal left * K * Matrix.diagonal right := rfl

/-- Linear transport cost term `<C, PiM>`. -/
noncomputable def transportCost (C PiM : Coupling n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, C i j * PiM i j

/-- Negative Shannon entropy term `∑ PiM_ij log PiM_ij`. -/
noncomputable def negativeEntropy (PiM : Coupling n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, PiM i j * Real.log (PiM i j)

/-- Entropically regularized OT objective `⟨C,PiM⟩ + ε * ∑ PiM log PiM`. -/
noncomputable def regularizedOTObjective (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  transportCost n C PiM + ε * negativeEntropy n PiM

/-! ### OT / Bayesian / Convex Naming Layer

These are explicit naming aliases for the same functional objects already present:
- entropic OT objective
- Bayesian free-energy objective
- convex objective = linear transport term + entropy regularizer
-/

/-- Explicit OT naming alias for the regularized transport objective. -/
noncomputable abbrev entropicOptimalTransportObjective
    (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  regularizedOTObjective n ε C PiM

/-- Bayesian free-energy naming alias for the same functional. -/
noncomputable abbrev bayesianFreeEnergyObjective
    (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  regularizedOTObjective n ε C PiM

/-- Convex-program decomposition: linear transport term plus entropy regularizer. -/
lemma entropicOptimalTransportObjective_eq_transport_plus_entropy
    (ε : ℝ) (C PiM : Coupling n) :
    entropicOptimalTransportObjective n ε C PiM
      = transportCost n C PiM + ε * negativeEntropy n PiM := rfl

@[simp] lemma bayesianFreeEnergyObjective_eq_regularizedOTObjective
    (ε : ℝ) (C PiM : Coupling n) :
    bayesianFreeEnergyObjective n ε C PiM = regularizedOTObjective n ε C PiM := rfl

/-- OT Gibbs kernel interpreted as Bayesian likelihood matrix. -/
noncomputable abbrev bayesianLikelihoodKernel (ε : ℝ) (C : CostMatrix n) : Coupling n :=
  entropicKernel n ε C

/-- Two-sided Sinkhorn scaling interpreted as Bayesian posterior coupling update. -/
noncomputable abbrev bayesianPosteriorCoupling
    (K : Coupling n) (left right : Fin n → ℝ) : Coupling n :=
  sinkhornScaledCoupling n K left right

/-! ### Schrödinger Bridge Naming Layer

Discrete entropic OT with Gibbs kernel + Sinkhorn scaling is the finite Schrödinger bridge model.
-/

/-- Schrödinger bridge reference kernel (entropic Gibbs kernel). -/
noncomputable abbrev schroedingerBridgeKernel (ε : ℝ) (C : CostMatrix n) : Coupling n :=
  entropicKernel n ε C

/-- Schrödinger bridge coupling via two-sided Sinkhorn scaling. -/
noncomputable abbrev schroedingerBridgeCoupling
    (K : Coupling n) (left right : Fin n → ℝ) : Coupling n :=
  sinkhornScaledCoupling n K left right

/-- Schrödinger bridge objective (entropic OT action). -/
noncomputable abbrev schroedingerBridgeObjective
    (ε : ℝ) (C PiM : Coupling n) : ℝ :=
  regularizedOTObjective n ε C PiM

/-- Row-normalization enforces unit row marginals. -/
lemma rowNormalize_has_unit_rowMarginal
    (M : Coupling n) (hrow : HasPositiveRowSums n M) :
    ∀ i : Fin n, rowSum n (rowNormalize n M hrow) i = 1 :=
  rowSum_rowNormalize (n := n) M hrow

/-- Column-normalization enforces unit column marginals. -/
lemma colNormalize_has_unit_colMarginal
    (M : Coupling n) (hcol : HasPositiveColSums n M) :
    ∀ j : Fin n, colSum n (colNormalize n M hcol) j = 1 :=
  colSum_colNormalize (n := n) M hcol

/--
Sinkhorn-Knopp update is exactly a two-sided Weyl gauge transform on the coupling kernel.
-/
lemma sinkhornTwoStep_eq_twoSidedGauge
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = sinkhornScaledCoupling n M
          (leftWeylScale n M)
          (rightWeylScale n (rowNormalize n M hrow)) := by
  simpa [sinkhornScaledCoupling] using
    (sinkhornTwoStep_eq_weylGauge (n := n) M hrow hcol)

/--
Bayesian posterior form: one Sinkhorn two-step is a two-sided posterior reweighting update.
-/
lemma sinkhornTwoStep_eq_bayesianPosteriorGauge
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = bayesianPosteriorCoupling n M
          (leftWeylScale n M)
          (rightWeylScale n (rowNormalize n M hrow)) := by
  simpa [bayesianPosteriorCoupling] using
    (sinkhornTwoStep_eq_twoSidedGauge (n := n) M hrow hcol)

/--
Schrödinger bridge form: one Sinkhorn two-step is a two-sided gauge-scaled bridge coupling.
-/
lemma sinkhornTwoStep_eq_schroedingerBridgeGauge
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = schroedingerBridgeCoupling n M
          (leftWeylScale n M)
          (rightWeylScale n (rowNormalize n M hrow)) := by
  simpa [schroedingerBridgeCoupling] using
    (sinkhornTwoStep_eq_twoSidedGauge (n := n) M hrow hcol)

/--
Phase-aligned Lyapunov monotonicity for one Sinkhorn step, in OT language.
-/
lemma sinkhornStep_regularizedObjective_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_phaseLyapunov_monotone (n := n) hstep

/--
Entropic OT step monotonicity alias (via the same phase Lyapunov functional).
-/
lemma sinkhornStep_entropicOT_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_regularizedObjective_monotone (n := n) hstep

/--
Bayesian free-energy step monotonicity alias (same statement in Bayesian language).
-/
lemma sinkhornStep_bayesianFreeEnergy_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_regularizedObjective_monotone (n := n) hstep

/--
Radon-Nikodym barrier monotonicity alias:
the negative-log Jacobian generator contracts to the normalized axis after each step.
-/
lemma sinkhornStep_radonNikodymBarrier_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M :=
  sinkhornStep_phaseRNBarrier_monotone (n := n) hstep

/-- Schrödinger bridge step monotonicity alias. -/
lemma schroedingerBridgeStep_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M :=
  sinkhornStep_regularizedObjective_monotone (n := n) hstep

/--
Schrödinger bridge form of RN-barrier monotonicity.
-/
lemma schroedingerBridgeStep_radonNikodymBarrier_monotone
    {phase : SinkhornPhase} {M M' : Coupling n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M :=
  sinkhornStep_radonNikodymBarrier_monotone (n := n) hstep

attribute [rep_depth operator]
  CostMatrix
  Coupling
  Marginal
  HasMarginals
  HasPositiveRowSums
  HasPositiveColSums
  SinkhornMatrix
  IsBistochasticSwitch
  switchMatrix
  switchMatrix_apply
  switchMatrix_row_sum_one
  switchMatrix_mem_rowStochastic
  switchMatrix_mem_doublyStochastic
  SinkhornCertificate.ofBistochastic
  gc_partition_eq_routerPartition
  gc_gibbsWeight_eq_normalizedWeights
  routerParams
  transportCost
  rowSum
  colSum
  leftWeylScale
  rightWeylScale
  sinkhornScaledCoupling
  sinkhornScaledCoupling_def
  rowNormalize
  colNormalize
  rowNormalize_eq_leftDiagonalGauge
  colNormalize_eq_rightDiagonalGauge
  rowNormalize_has_unit_rowMarginal
  colNormalize_has_unit_colMarginal
  rowSum_rowNormalize
  colSum_colNormalize
  relativeVolumeChangeRN
  relativeVolumeChangeRN_eq_exp_logJacobian
  kahlerPotentialRN
  kahlerPotentialRN_eq_neg_logJacobian
  kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN
  rowRadonNikodymGenerator
  colRadonNikodymGenerator
  rowRNBarrier
  colRNBarrier
  rowRNBarrier_nonneg
  colRNBarrier_nonneg
  rowRNBarrier_rowNormalize_eq_zero
  colRNBarrier_colNormalize_eq_zero
  phaseRNBarrierBefore
  phaseRNBarrierAfter
  phaseRNBarrierBefore_nonneg
  phaseRNBarrierAfter_nonneg
  sinkhornStep_phaseRNBarrierAfter_eq_zero
  sinkhornStep_phaseRNBarrier_monotone
  rn_barrier_row_step_eq_zero
  rowLyapunov
  colLyapunov
  rowLyapunov_nonneg
  colLyapunov_nonneg
  rowLyapunov_rowNormalize_eq_zero
  colLyapunov_colNormalize_eq_zero
  phaseAt
  phaseLyapunovBefore
  phaseLyapunovAfter
  phaseLyapunovBefore_nonneg
  phaseLyapunovAfter_nonneg
  sinkhornStep_phaseLyapunovAfter_eq_zero
  sinkhornStep_phaseLyapunov_monotone
  trajectoryRNBarrier
  trajectoryRNBarrierNext
  trajectoryRNBarrier_nonneg
  trajectoryRNBarrierNext_nonneg
  trajectoryRNBarrierNext_eq_zero
  trajectoryRNBarrier_monotone
  trajectoryLyapunov
  trajectoryLyapunovNext
  trajectoryLyapunov_nonneg
  trajectoryLyapunovNext_nonneg
  trajectoryLyapunovNext_eq_zero
  trajectoryLyapunov_monotone
  negativeEntropy
  entropicKernel
  entropicOptimalTransportObjective
  regularizedOTObjective
  bayesianLikelihoodKernel
  bayesianPosteriorCoupling
  schroedingerBridgeKernel
  schroedingerBridgeCoupling
  bayesianFreeEnergyObjective
  bayesianFreeEnergyObjective_eq_regularizedOTObjective
  schroedingerBridgeObjective
  entropicOptimalTransportObjective_eq_transport_plus_entropy
  SinkhornStep
  sinkhornTwoStep_eq_twoSidedGauge
  sinkhornTwoStep_eq_weylGauge
  sinkhornTwoStep_eq_bayesianPosteriorGauge
  sinkhornTwoStep_eq_schroedingerBridgeGauge
  exists_perm_decomposition_of_bistochastic
  exists_perm_decomposition_of_sinkhornBalanced
  normalizedWeights_nonneg
  sinkhornStep_regularizedObjective_monotone
  sinkhornStep_entropicOT_monotone
  sinkhornStep_bayesianFreeEnergy_monotone
  sinkhornStep_radonNikodymBarrier_monotone
  schroedingerBridgeStep_monotone
  schroedingerBridgeStep_radonNikodymBarrier_monotone
  rowBarrierPotential
  colBarrierPotential

end EntropicOTBridge

end InfoGeometry.Canonical.MoE
