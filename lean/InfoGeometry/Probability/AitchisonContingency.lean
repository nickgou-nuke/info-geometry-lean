/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.BipartiteLogCoupling

/-!
# Orthogonal projection of positive contingency tables

The existing rectangular interaction `C_I * X * C_J` is used unchanged.
The metric is explicitly the sum-of-squares Frobenius geometry, never the
default norm on matrices. Probability points use Mathlib's native `StdSimplex`.
All logarithmic probability results require strictly positive weights.

Source contract: `docs/AITCHISON_CONTINGENCY_CONTRACT.md`. No Bayesian sampling,
posterior, asymptotic, or Sinkhorn convergence statement is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Probability.AitchisonContingency

open InfoGeometry.Probability.BipartiteLogCoupling

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The existing interaction, now exposed as a native linear endomorphism. -/
def interactionLinear : Matrix I J ℝ →ₗ[ℝ] Matrix I J ℝ where
  toFun := interaction
  map_add' X Y := by simp [interaction, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [interaction, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem interactionLinear_apply (X : Matrix I J ℝ) :
    interactionLinear X = interaction X := rfl

def additiveProjection : Matrix I J ℝ →ₗ[ℝ] Matrix I J ℝ :=
  LinearMap.id - interactionLinear

@[simp] theorem additiveProjection_apply (X : Matrix I J ℝ) :
    additiveProjection X = X - interaction X := rfl

def additiveSubspace : Submodule ℝ (Matrix I J ℝ) := LinearMap.ker interactionLinear
def interactionSubspace : Submodule ℝ (Matrix I J ℝ) := LinearMap.range interactionLinear

def totalSumLinear : Matrix I J ℝ →ₗ[ℝ] ℝ where
  toFun X := ∑ i, ∑ j, X i j
  map_add' X Y := by simp [Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.mul_sum]

def centeredSubspace : Submodule ℝ (Matrix I J ℝ) := LinearMap.ker totalSumLinear
def centeredAdditiveSubspace : Submodule ℝ (Matrix I J ℝ) :=
  additiveSubspace ⊓ centeredSubspace

@[simp] theorem mem_additiveSubspace (X : Matrix I J ℝ) :
    X ∈ additiveSubspace ↔ interaction X = 0 := Iff.rfl

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem mem_centeredSubspace (X : Matrix I J ℝ) :
    X ∈ centeredSubspace ↔ totalSumLinear X = 0 := Iff.rfl

@[simp] theorem interaction_zero : interaction (0 : Matrix I J ℝ) = 0 := by
  simp [interaction]

theorem interaction_add (X Y : Matrix I J ℝ) :
    interaction (X + Y) = interaction X + interaction Y := interactionLinear.map_add X Y

theorem interaction_sub (X Y : Matrix I J ℝ) :
    interaction (X - Y) = interaction X - interaction Y := interactionLinear.map_sub X Y

theorem interaction_idempotent [Nonempty I] [Nonempty J] (X : Matrix I J ℝ) :
    interaction (interaction X) = interaction X := by
  have hI := (complementary_average (I := I)).2.2
  have hJ := (complementary_average (I := J)).2.2
  calc
    interaction (interaction X) = (center I * center I) * X * (center J * center J) := by
      simp only [interaction, Matrix.mul_assoc]
    _ = interaction X := by rw [hI, hJ]; rfl

theorem additiveProjection_mem [Nonempty I] [Nonempty J] (X : Matrix I J ℝ) :
    additiveProjection X ∈ additiveSubspace := by
  simp [interaction_sub, interaction_idempotent]

theorem additiveProjection_idempotent [Nonempty I] [Nonempty J] (X : Matrix I J ℝ) :
    additiveProjection (additiveProjection X) = additiveProjection X := by
  rw [additiveProjection_apply, (mem_additiveSubspace _).mp (additiveProjection_mem X), sub_zero]

/-- Explicit Frobenius pairing on rectangular matrices. -/
def frobenius (X Y : Matrix I J ℝ) : ℝ := ∑ i, ∑ j, X i j * Y i j

/-- Explicit squared Frobenius size; no matrix norm instance is used. -/
def frobeniusSq (X : Matrix I J ℝ) : ℝ := ∑ i, ∑ j, (X i j) ^ 2

omit [DecidableEq I] [DecidableEq J] in
theorem frobenius_eq_trace (X Y : Matrix I J ℝ) :
    frobenius X Y = Matrix.trace (X.transpose * Y) := by
  simp only [frobenius, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

omit [DecidableEq I] [DecidableEq J] in
theorem frobenius_comm (X Y : Matrix I J ℝ) : frobenius X Y = frobenius Y X := by
  unfold frobenius
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq I] [DecidableEq J] in
theorem frobenius_add_left (X Y Z : Matrix I J ℝ) :
    frobenius (X + Y) Z = frobenius X Z + frobenius Y Z := by
  simp [frobenius, add_mul, Finset.sum_add_distrib]

omit [DecidableEq I] [DecidableEq J] in
theorem frobenius_add_right (X Y Z : Matrix I J ℝ) :
    frobenius X (Y + Z) = frobenius X Y + frobenius X Z := by
  simp [frobenius, mul_add, Finset.sum_add_distrib]

omit [DecidableEq I] [DecidableEq J] in
theorem frobenius_sub_right (X Y Z : Matrix I J ℝ) :
    frobenius X (Y - Z) = frobenius X Y - frobenius X Z := by
  simp [frobenius, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem frobenius_zero_right (X : Matrix I J ℝ) : frobenius X 0 = 0 := by
  simp [frobenius]

omit [DecidableEq I] [DecidableEq J] in
theorem frobenius_self (X : Matrix I J ℝ) : frobenius X X = frobeniusSq X := by
  simp [frobenius, frobeniusSq, pow_two]

omit [DecidableEq I] [DecidableEq J] in
theorem frobeniusSq_nonneg (X : Matrix I J ℝ) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (X i j)

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem frobeniusSq_eq_zero (X : Matrix I J ℝ) : frobeniusSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hr := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => Finset.sum_nonneg
        (fun j (_ : j ∈ Finset.univ) => sq_nonneg (X i j)))).mp h
    ext i j
    exact (Finset.sum_sq_eq_zero_iff Finset.univ (X i)).mp
      (hr i (Finset.mem_univ i)) j (Finset.mem_univ j)
  · rintro rfl
    simp [frobeniusSq]

/-- Scalar expansion after the Frobenius pairing has been evaluated in `ℝ`. -/
private theorem real_pairing_square_expansion (a b c : ℝ) :
    (a + b) + (b + c) = a + 2 * b + c := by
  ring

omit [DecidableEq I] [DecidableEq J] in
theorem frobeniusSq_add (X Y : Matrix I J ℝ) :
    frobeniusSq (X + Y) = frobeniusSq X + 2 * frobenius X Y + frobeniusSq Y := by
  rw [← frobenius_self, frobenius_add_left, frobenius_add_right, frobenius_add_right,
    frobenius_self, frobenius_self, frobenius_comm Y X]
  exact real_pairing_square_expansion _ _ _

/-- Symmetry of the canonical centering matrices gives self-adjointness. -/
theorem interaction_self_adjoint (X Y : Matrix I J ℝ) :
    frobenius (interaction X) Y = frobenius X (interaction Y) := by
  rw [frobenius_eq_trace, frobenius_eq_trace]
  simp only [interaction, Matrix.transpose_mul, center_transpose]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (center J) (X.transpose * center I * Y)

theorem interaction_orthogonal_additive (X Y : Matrix I J ℝ)
    (hY : Y ∈ additiveSubspace) : frobenius (interaction X) Y = 0 := by
  rw [interaction_self_adjoint, (mem_additiveSubspace Y).mp hY, frobenius_zero_right]

/-- Exact residual decomposition against every additive competitor. -/
theorem additive_pythagorean [Nonempty I] [Nonempty J] (X Y : Matrix I J ℝ)
    (hY : Y ∈ additiveSubspace) :
    frobeniusSq (X - Y) = frobeniusSq (interaction X) +
      frobeniusSq (additiveProjection X - Y) := by
  have hres : additiveProjection X - Y ∈ additiveSubspace :=
    Submodule.sub_mem _ (additiveProjection_mem X) hY
  have hsplit : X - Y = interaction X + (additiveProjection X - Y) := by
    rw [additiveProjection_apply]
    abel
  rw [hsplit, frobeniusSq_add, interaction_orthogonal_additive X _ hres]
  simp only [mul_zero, add_zero]

theorem additive_best_approximation [Nonempty I] [Nonempty J]
    (X Y : Matrix I J ℝ) (hY : Y ∈ additiveSubspace) :
    frobeniusSq (X - additiveProjection X) ≤ frobeniusSq (X - Y) := by
  have hres : X - additiveProjection X = interaction X := by
    rw [additiveProjection_apply]
    abel
  rw [hres, additive_pythagorean X Y hY]
  exact le_add_of_nonneg_right (frobeniusSq_nonneg _)

theorem additive_best_approximation_eq_iff [Nonempty I] [Nonempty J]
    (X Y : Matrix I J ℝ) (hY : Y ∈ additiveSubspace) :
    frobeniusSq (X - Y) = frobeniusSq (X - additiveProjection X) ↔
      Y = additiveProjection X := by
  have hres : X - additiveProjection X = interaction X := by
    rw [additiveProjection_apply]
    abel
  rw [hres, additive_pythagorean X Y hY]
  constructor
  · intro h
    have hz : frobeniusSq (additiveProjection X - Y) = 0 := by linarith
    exact (sub_eq_zero.mp ((frobeniusSq_eq_zero _).mp hz)).symm
  · rintro rfl
    simp [frobeniusSq]

def rowLogMean (X : Matrix I J ℝ) (i : I) : ℝ :=
  (∑ j, X i j) / (Fintype.card J : ℝ)

def colLogMean (X : Matrix I J ℝ) (j : J) : ℝ :=
  (∑ i, X i j) / (Fintype.card I : ℝ)

def grandMean (X : Matrix I J ℝ) : ℝ :=
  (∑ i, ∑ j, X i j) / ((Fintype.card I : ℝ) * (Fintype.card J : ℝ))

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem average_left_apply (X : Matrix I J ℝ) (i : I) (j : J) :
    (average I * X) i j = colLogMean X j := by
  simp [Matrix.mul_apply, average, colLogMean, div_eq_mul_inv, Finset.mul_sum, mul_comm]

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem average_right_apply (X : Matrix I J ℝ) (i : I) (j : J) :
    (X * average J) i j = rowLogMean X i := by
  simp [Matrix.mul_apply, average, rowLogMean, div_eq_mul_inv, Finset.sum_mul]

omit [DecidableEq I] [DecidableEq J] in
theorem average_both_apply (X : Matrix I J ℝ) (i : I) (j : J) :
    (average I * X * average J) i j = grandMean X := by
  rw [average_right_apply]
  unfold rowLogMean
  simp only [average_left_apply, colLogMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  unfold grandMean
  ring

theorem interaction_apply (X : Matrix I J ℝ) (i : I) (j : J) :
    interaction X i j = X i j - rowLogMean X i - colLogMean X j + grandMean X := by
  have hs : interaction X = X - X * average J - average I * X +
      average I * X * average J := by
    simp only [interaction, center, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    abel
  rw [hs]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [average_both_apply, average_left_apply, average_right_apply]

/-- The kernel really is the additive row/column subspace. -/
theorem mem_additiveSubspace_iff [Nonempty I] [Nonempty J] (X : Matrix I J ℝ) :
    X ∈ additiveSubspace ↔ ∃ a : I → ℝ, ∃ b : J → ℝ,
      X = rowShift a + colShift b := by
  constructor
  · intro h
    refine ⟨rowLogMean X, fun j => colLogMean X j - grandMean X, ?_⟩
    ext i j
    have hij := congrFun (congrFun ((mem_additiveSubspace X).mp h) i) j
    rw [interaction_apply] at hij
    change X i j = rowLogMean X i + (colLogMean X j - grandMean X)
    change X i j - rowLogMean X i - colLogMean X j + grandMean X = 0 at hij
    linarith
  · rintro ⟨a, b, rfl⟩
    rw [mem_additiveSubspace]
    have h := interaction_shift (0 : Matrix I J ℝ) a b
    simpa using h

theorem interaction_column_sum [Nonempty I] (X : Matrix I J ℝ) (j : J) :
    (∑ i, interaction X i j) = 0 := by
  have hh : average I * interaction X = 0 := by
    simp only [interaction, ← Matrix.mul_assoc,
      (complementary_average (I := I)).1, Matrix.zero_mul]
  let i₀ : I := Classical.arbitrary I
  have hz := congrFun (congrFun hh i₀) j
  rw [average_left_apply] at hz
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact by simpa [colLogMean] using (div_eq_iff hn).mp hz

theorem totalSum_interaction [Nonempty I] (X : Matrix I J ℝ) :
    totalSumLinear (interaction X) = 0 := by
  calc
    totalSumLinear (interaction X) = ∑ j : J, ∑ i : I, interaction X i j :=
      Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero (fun j _ => interaction_column_sum X j)

theorem additiveProjection_preserves_total [Nonempty I] (X : Matrix I J ℝ) :
    totalSumLinear (additiveProjection X) = totalSumLinear X := by
  rw [additiveProjection_apply, map_sub, totalSum_interaction, sub_zero]

/-- Every interaction has zero arithmetic sum in each row. -/
theorem interaction_row_sum [Nonempty J] (X : Matrix I J ℝ) (i : I) :
    (∑ j, interaction X i j) = 0 := by
  have hh : interaction X * average J = 0 := by
    simp only [interaction, Matrix.mul_assoc,
      (complementary_average (I := J)).2.1, Matrix.mul_zero]
  let j₀ : J := Classical.arbitrary J
  have hz := congrFun (congrFun hh i) j₀
  rw [average_right_apply] at hz
  have hn : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact by simpa [rowLogMean] using (div_eq_iff hn).mp hz

/-- The native interaction range consists exactly of matrices with all row and
column sums zero. Both conditions concern the log-coordinate matrix, not the
arithmetic probability marginals of its entrywise exponential. -/
theorem mem_interactionSubspace_iff [Nonempty I] [Nonempty J] (X : Matrix I J ℝ) :
    X ∈ interactionSubspace ↔
      (∀ i, ∑ j, X i j = 0) ∧ (∀ j, ∑ i, X i j = 0) := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨interaction_row_sum Y, interaction_column_sum Y⟩
  · rintro ⟨hr, hc⟩
    refine ⟨X, ?_⟩
    apply Matrix.ext
    intro i j
    simp [interactionLinear_apply, interaction_apply,
      rowLogMean, colLogMean, grandMean, hr, hc]

end InfoGeometry.Probability.AitchisonContingency
