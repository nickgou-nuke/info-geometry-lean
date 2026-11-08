/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse
import InfoGeometry.QuantumContext.FiniteSoftmaxStationaryGreen
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange
import InfoGeometry.QuantumContext.MarkovAttentionKemenySnell

/-!
# Algebraic Kemeny trace identity for finite Markov group inverses

For a finite row-stochastic matrix, its group inverse annihilates the constant
column. Consequently the weighted sum of the group-inverse potential
differences equals the trace of the group inverse. This is an algebraic
identity; no expected hitting-time interpretation is asserted here.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A group inverse sends every vector in the kernel of its operator to zero. -/
theorem groupInverse_apply_eq_zero_of_mem_ker
    (A D : Module.End ℝ V) (hD : IsGroupInverse A D) (x : V)
    (hx : A x = 0) : D x = 0 := by
  have hADx : A (D x) = 0 := by
    have hcomm := congrArg (fun f : Module.End ℝ V => f x) hD.2.2
    change A (D x) = D (A x) at hcomm
    rw [hx, map_zero] at hcomm
    exact hcomm
  have hrecover := congrArg (fun f : Module.End ℝ V => f x) hD.2.1
  change D (A (D x)) = D x at hrecover
  rw [hADx, map_zero] at hrecover
  exact hrecover.symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix group inverse of a finite row-stochastic Laplacian has zero row
sums. The proof transports the group inverse to endomorphisms and uses the
constant-vector kernel of `1 - P`. -/
theorem groupInverse_matrix_row_sum_eq_zero
    (P G : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hG : IsGroupInverse (1 - P) G) :
    ∀ i, ∑ j, G i j = 0 := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  let D : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
  have hD : IsGroupInverse A D := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  have hPone : P *ᵥ (fun _ : ι => (1 : ℝ)) = 1 :=
    (Matrix.mem_rowStochastic.mp hP).2
  have honeker : A (fun _ : ι => (1 : ℝ)) = 0 := by
    change (1 - P) *ᵥ (fun _ : ι => (1 : ℝ)) = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPone]
    ext i
    simp
  have hDone : D (fun _ : ι => (1 : ℝ)) = 0 :=
    groupInverse_apply_eq_zero_of_mem_ker A D hD _ honeker
  have hmulVec : G *ᵥ (fun _ : ι => (1 : ℝ)) = 0 := by
    simpa [D, Matrix.toLin'_apply] using hDone
  intro i
  have hi := congrFun hmulVec i
  simpa [Matrix.mulVec, dotProduct] using hi

/-- The algebraic potential difference associated with a weighted group
inverse. It is not, by definition alone, an expected hitting time. -/
def groupInversePotentialDifference
    (π : ι → ℝ) (G : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  (G j j - G i j) / π j

omit [DecidableEq ι] in
/-- The weighted sum of group-inverse potential differences is the
trace of the group inverse whenever its rows sum to zero. -/
theorem weightedGroupInversePotentialSum_eq_trace
    (π : ι → ℝ) (G : Matrix ι ι ℝ)
    (hπ : ∀ j, π j ≠ 0)
    (hrows : ∀ i, ∑ j, G i j = 0)
    (i : ι) :
    ∑ j, π j * groupInversePotentialDifference π G i j = Matrix.trace G := by
  calc
    (∑ j, π j * groupInversePotentialDifference π G i j) =
        ∑ j, (G j j - G i j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [groupInversePotentialDifference]
          field_simp [hπ j]
    _ = (∑ j, G j j) - ∑ j, G i j := by rw [Finset.sum_sub_distrib]
    _ = Matrix.trace G := by simp [Matrix.trace, hrows i]

/-- The group-inverse deviation candidate with the first-return diagonal
convention: its diagonal value is `1 / π i`, while its off-diagonal value is
`(G j j - G i j) / π j`. This algebraic definition alone does not identify it
with an expected hitting time. -/
def groupInverseReturnAdjustedPotential
    (π : ι → ℝ) (G : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  groupInversePotentialDifference π G i j +
    if i = j then (π j)⁻¹ else 0

private theorem sum_diagonal_indicator (i : ι) :
    ∑ j, (if i = j then (1 : ℝ) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The first-return diagonal correction changes the group-inverse trace
identity by exactly one. No stochastic stopping-time interpretation is
asserted: this is a finite algebraic identity. -/
theorem weightedGroupInverseReturnAdjustedPotentialSum_eq_trace_add_one
    (π : ι → ℝ) (G : Matrix ι ι ℝ)
    (hπ : ∀ j, π j ≠ 0)
    (hrows : ∀ i, ∑ j, G i j = 0)
    (i : ι) :
    ∑ j, π j * groupInverseReturnAdjustedPotential π G i j =
      Matrix.trace G + 1 := by
  classical
  calc
    (∑ j, π j * groupInverseReturnAdjustedPotential π G i j) =
        (∑ j, π j * groupInversePotentialDifference π G i j) +
          ∑ j, if i = j then (1 : ℝ) else 0 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [groupInverseReturnAdjustedPotential, mul_add]
            by_cases hij : i = j
            · subst i
              simp [groupInversePotentialDifference, hπ j]
            · simp [groupInversePotentialDifference, hij]
    _ = Matrix.trace G + 1 := by
      rw [weightedGroupInversePotentialSum_eq_trace π G hπ hrows i,
        sum_diagonal_indicator]

/-- The algebraic return-adjusted potential sum equals the matrix trace of the
stationary-mean-regularized group-inverse shift. This theorem asserts only the
trace identity; identifying the shift as an inverse of the regularized
Laplacian requires the additional hypotheses in the separate Kemeny–Snell
inverse theorems. No probabilistic hitting-time interpretation is used. -/
theorem weightedGroupInverseReturnAdjustedPotentialSum_eq_regularizedShift_trace
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hπ : ∀ j, π j ≠ 0)
    (hπsum : ∑ j, π j = 1)
    (hG : IsGroupInverse (1 - P) G)
    (i : ι) :
    ∑ j, π j * groupInverseReturnAdjustedPotential π G i j =
      Matrix.trace (G + stationaryMeanMatrix π) := by
  rw [weightedGroupInverseReturnAdjustedPotentialSum_eq_trace_add_one
    π G hπ (groupInverse_matrix_row_sum_eq_zero P G hP hG) i]
  rw [Matrix.trace_add]
  congr 1
  simp [stationaryMeanMatrix, Matrix.trace, hπsum]

/-- For symmetric finite softmax scores, the explicit partition-function
stationary weight and any group inverse of the softmax Laplacian satisfy the
return-adjusted algebraic trace identity. The candidate is not identified here
with a probabilistic mean first-return time. -/
theorem symmetricSoftmax_returnAdjustedPotentialSum_eq_trace_add_one
    [Nonempty ι]
    (scores : ι → ι → ℝ)
    (hsymm : ∀ i j, scores i j = scores j i)
    (G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - softmaxAttentionMatrix scores) G)
    (i : ι) :
    ∑ j, softmaxPartitionStationaryWeight scores j *
        groupInverseReturnAdjustedPotential
          (softmaxPartitionStationaryWeight scores) G i j =
      Matrix.trace G + 1 := by
  have hstationary := softmaxPartitionStationaryWeight_is_stationary
    scores hsymm
  apply weightedGroupInverseReturnAdjustedPotentialSum_eq_trace_add_one
  · intro j
    exact (hstationary.1 j).ne'
  · exact groupInverse_matrix_row_sum_eq_zero
      (softmaxAttentionMatrix scores) G
      (softmaxAttentionMatrix_mem_rowStochastic scores) hG

/-- For any finite row-stochastic `P`, any nonzero coordinate weights, and any
group inverse `G` of `1 - P`, the weighted algebraic
potential sum is independent of the starting index and equals `trace G`.
The theorem does not identify this potential with a probabilistic hitting time. -/
theorem markovGroupInverse_weightedPotentialSum_eq_trace
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hG : IsGroupInverse (1 - P) G)
    (hπ : ∀ j, π j ≠ 0)
    (i : ι) :
    ∑ j, π j * groupInversePotentialDifference π G i j = Matrix.trace G := by
  exact weightedGroupInversePotentialSum_eq_trace π G hπ
    (groupInverse_matrix_row_sum_eq_zero P G hP hG) i

/-- For a strictly positive finite row-stochastic transition matrix and a
normalized nonnegative stationary row weight, the group-inverse potential
solves the off-target finite Bellman equation. This is an algebraic identity;
no expected hitting-time interpretation is asserted. -/
theorem groupInversePotentialDifference_laplacian_eq_one_off_target
    [Nonempty ι]
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (target : ι) :
    ∀ i, i ≠ target →
      ((1 - P).mulVec
        (fun k => groupInversePotentialDifference π G k target)) i = 1 := by
  classical
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  let D : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
  have hπpos : ∀ j, 0 < π j :=
    stationaryRowProbability_pos_of_pos_entries P π hPpos hπnonneg hπsum hπstat
  have hπne : π target ≠ 0 := (hπpos target).ne'
  have hD : IsGroupInverse A D := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  let e : ι → ℝ := fun i => if i = target then 1 else 0
  have hcol (k : ι) : D e k = G k target := by
    simp [D, e, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Finset.sum_ite_eq']
  have hprojection :=
    principalIdempotent_eq_stationaryMean_projection
      P π hP hPpos hπsum hπstat D hD e
  have hprojection_form :
      principalIdempotent A D e = e - A (D e) := by
    simp [principalIdempotent, regularIdempotent, Module.End.mul_apply,
      Module.End.one_apply]
  have hAcol (i : ι) :
      A (D e) i = (if i = target then 1 else 0) - π target := by
    have hi := congrFun hprojection i
    rw [hprojection_form] at hi
    have hmean : weightedMeanMap π e = π target := by
      change ∑ i, π i * (if i = target then (1 : ℝ) else 0) = π target
      rw [Finset.sum_eq_single target]
      · simp
      · intro i hi hne
        simp [hne]
      · intro h
        exact (h (Finset.mem_univ target)).elim
    rw [hmean] at hi
    simp only [Pi.sub_apply] at hi
    have he : e i = if i = target then (1 : ℝ) else 0 := by
      by_cases hit : i = target
      · subst i
        simp [e]
      · simp [e, hit]
    rw [he] at hi
    by_cases hit : i = target
    · subst i
      have hvalue : A (D e) target = 1 - π target := by
        have hi' : 1 - A (D e) target = π target := by simpa using hi
        linarith
      simpa using hvalue
    · simp [hit] at hi
      have hvalue : A (D e) i = -π target := by nlinarith [hi]
      simpa [hit] using hvalue
  have hone : A (fun _ : ι => (1 : ℝ)) = 0 := by
    change (1 - P).mulVec (fun _ : ι => (1 : ℝ)) = 0
    have hPone : P *ᵥ (fun _ : ι => (1 : ℝ)) = 1 :=
      (Matrix.mem_rowStochastic.mp hP).2
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPone]
    ext i
    simp
  have hconst : A (fun _ : ι => G target target) = 0 := by
    have hfun : (fun _ : ι => G target target) =
        G target target • (fun _ : ι => (1 : ℝ)) := by
      ext k
      simp
    rw [hfun, map_smul, hone, smul_zero]
  let potential : ι → ℝ :=
    fun k => groupInversePotentialDifference π G k target
  have hpotential : potential =
      (π target)⁻¹ • (fun k => G target target - D e k) := by
    funext k
    change (G target target - G k target) / π target =
      (π target)⁻¹ * (G target target - D e k)
    rw [div_eq_mul_inv, hcol k]
    ring
  have himage : A potential =
      (π target)⁻¹ • (A (fun _ : ι => G target target) - A (D e)) := by
    have hsubfun : (fun k => G target target - D e k) =
        (fun _ : ι => G target target) - D e := by
      ext k
      rfl
    calc
      A potential = A ((π target)⁻¹ •
          ((fun _ : ι => G target target) - D e)) := by
            rw [hpotential, hsubfun]
      _ = (π target)⁻¹ •
          (A (fun _ : ι => G target target) - A (D e)) := by
            simp only [map_smul, map_sub]
  intro i hit
  have hi := congrFun himage i
  rw [hconst] at hi
  change A potential i = (π target)⁻¹ * (0 - A (D e) i) at hi
  rw [hAcol i] at hi
  simp [hit, hπne] at hi
  have hgoal : A potential i = 1 := hi
  simpa [A, potential, Matrix.toLin'_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec] using hgoal

/-- A strictly positive finite row-stochastic Laplacian has at most one
solution to the single-target Dirichlet problem: the value is fixed at the
target, and the Laplacian values are fixed away from it. This is an algebraic
boundary-value uniqueness statement, not a probabilistic hitting-time claim. -/
theorem positive_markov_dirichlet_boundary_unique
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (target : ι) (x y : ι → ℝ)
    (hboundary : x target = y target)
    (hx : ∀ i, i ≠ target → ((1 - P).mulVec x) i = 1)
    (hy : ∀ i, i ≠ target → ((1 - P).mulVec y) i = 1) :
    x = y := by
  classical
  let d : ι → ℝ := x - y
  have htarget : d target = 0 := by
    dsimp [d]
    rw [hboundary, sub_self]
  have hLapOff (i : ι) (hi : i ≠ target) :
      ((1 - P).mulVec d) i = 0 := by
    dsimp [d]
    rw [Matrix.mulVec_sub]
    change ((1 - P).mulVec x) i - ((1 - P).mulVec y) i = 0
    rw [hx i hi, hy i hi, sub_self]
  have hmean : weightedMeanMap π ((1 - P).mulVec d) = 0 :=
    weightedMeanMap_laplacian_eq_zero P π d hπstat
  have hsum :
      (∑ i, π i * ((1 - P).mulVec d) i) =
        π target * ((1 - P).mulVec d) target := by
    rw [Finset.sum_eq_single target]
    · intro i _ hne
      rw [hLapOff i hne, mul_zero]
    · simp
  have hAtTarget : ((1 - P).mulVec d) target = 0 := by
    have hπpos : 0 < π target :=
      stationaryRowProbability_pos_of_pos_entries P π hPpos hπnonneg hπsum hπstat target
    have hprod : π target * ((1 - P).mulVec d) target = 0 := by
      simpa [weightedMeanMap] using hsum.symm.trans hmean
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hπpos)
  have hLap : (1 - P).mulVec d = 0 := by
    funext i
    by_cases hi : i = target
    · simpa [hi] using hAtTarget
    · exact hLapOff i hi
  have hfixed : P *ᵥ d = d := by
    have hsub : d - P *ᵥ d = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hLap
    exact (sub_eq_zero.mp hsub).symm
  obtain ⟨c, hc⟩ :=
    (positive_rowStochastic_mulVec_fixed_iff_const P hP hPpos d).mp hfixed
  have hc0 : c = 0 := by
    calc
      c = d target := (hc target).symm
      _ = 0 := htarget
  have hd : d = 0 := by
    funext i
    rw [hc i, hc0]
    rfl
  dsimp [d] at hd
  exact sub_eq_zero.mp hd

/-- The group-inverse potential is the unique solution of the finite
single-target Dirichlet boundary problem: it vanishes at the target and its
`I - P` Laplacian equals one off the target. No expected hitting-time
interpretation is asserted. -/
theorem groupInversePotentialDifference_unique_dirichlet_solution
    [Nonempty ι]
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (target : ι) (x : ι → ℝ)
    (hboundary : x target = 0)
    (hx : ∀ i, i ≠ target → ((1 - P).mulVec x) i = 1) :
    x = fun i => groupInversePotentialDifference π G i target := by
  apply positive_markov_dirichlet_boundary_unique
    P π hP hPpos hπnonneg hπsum hπstat target x
    (fun i => groupInversePotentialDifference π G i target)
  · simp [groupInversePotentialDifference, hboundary]
  · exact hx
  · intro i hi
    exact groupInversePotentialDifference_laplacian_eq_one_off_target
      P G π hP hPpos hπnonneg hπsum hπstat hG target i hi

end InfoGeometry.QuantumContext.MarkovDrazin

end
