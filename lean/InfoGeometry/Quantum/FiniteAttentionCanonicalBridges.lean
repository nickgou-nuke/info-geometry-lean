import Mathlib
import InfoGeometry.Probability.AitchisonFinite

/-!
# Finite canonical bridges for attention-like data

The constructions here are finite and explicit.  A diagonal bipartite state is
given a genuine marginal (the diagonal part of a partial trace).  Gibbs and
Andreev data are owned by existing thermal and operator-algebra modules.  Radon and
Fourier--Mellin expressions are measure-parametrised integral carriers; no
Dirac delta or Hilbert-space operator is silently introduced.
-/

open scoped BigOperators
open MeasureTheory

namespace InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

open InfoGeometry.Probability.AitchisonFinite

section Marginal

abbrev BipartiteOperator (m n : ℕ) :=
  Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ

noncomputable def partialTraceSecondOp {m n : ℕ}
    (ρ : BipartiteOperator m n) : Matrix (Fin m) (Fin m) ℂ :=
  fun i k => ∑ j, ρ (i, j) (k, j)

theorem partialTraceSecondOp_trace {m n : ℕ} (ρ : BipartiteOperator m n) :
    Matrix.trace (partialTraceSecondOp ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Matrix.diag, partialTraceSecondOp]
  rw [Fintype.sum_prod_type]

theorem partialTraceSecondOp_diagonal {m n : ℕ}
    (p : Fin m → Fin n → ℂ) :
    partialTraceSecondOp (Matrix.diagonal (fun ij => p ij.1 ij.2)) =
      Matrix.diagonal (fun i => ∑ j, p i j) := by
  ext i k
  by_cases hik : i = k
  · subst k
    simp [partialTraceSecondOp]
  · simp [partialTraceSecondOp, hik]

/-! Complex positivity is stated through the real part of the Hermitian
quadratic form, since `ℂ` has no order structure. -/
def ComplexPositive {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, 0 ≤ (∑ i, ∑ j, star (v i) * A i j * v j).re

theorem sum_prod_fiber_indicator {m n : ℕ} {α : Type*}
    [AddCommMonoid α] (j : Fin n) (f : Fin m → α) :
    (∑ x : Fin m × Fin n, if x.2 = j then f x.1 else 0) = ∑ i, f i := by
  classical
  rw [Fintype.sum_prod_type]
  simp

theorem fiber_quadratic_form {m n : ℕ}
    (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (v : Fin m → ℂ) (j : Fin n) :
    (∑ x, ∑ y, star (if x.2 = j then v x.1 else 0) * A x y *
        (if y.2 = j then v y.1 else 0)) =
      ∑ i, ∑ k, star (v i) * A (i, j) (k, j) * v k := by
  classical
  simp only [Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single j]
  · simp
  · intro y hy hyj
    simp [hyj]
  · simp

theorem complexPositive_block_fiber_verified {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : ComplexPositive A) (j : Fin n) :
    ComplexPositive (A.submatrix (fun i : Fin m => (i, j))
      (fun i : Fin m => (i, j))) := by
  intro v
  have hw := hA (fun x : Fin m × Fin n => if x.2 = j then v x.1 else 0)
  rw [fiber_quadratic_form A v j] at hw
  exact hw

/-
theorem complexPositive_partialTrace_verified {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : ComplexPositive A) :
    ComplexPositive (partialTraceSecondOp A) := by
  classical
  intro v
  have hblock : ∀ j : Fin n,
      0 ≤ (∑ i, ∑ k, star (v i) * A (i, j) (k, j) * v k).re := by
    intro j
    exact complexPositive_block_fiber_verified hA j v
  have hrewrite :
      (∑ i, ∑ k, star (v i) * partialTraceSecondOp A i k * v k).re =
        (∑ j, ∑ i, ∑ k, star (v i) * A (i, j) (k, j) * v k).re := by
    congr 1
    simp only [partialTraceSecondOp]
    rw [Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.sum_comm]
  rw [hrewrite]
  rw [Complex.re_sum]
  exact Finset.sum_nonneg (fun j _ => hblock j)

noncomputable def partialTraceSecondDensityVerified {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    FiniteDensityOperator (Fin m) := by
  refine ⟨partialTraceSecondOp ρ.operator, ?_,
    complexPositive_partialTrace_verified ρ.positive, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i k
    simp [partialTraceSecondOp, ρ.hermitian.apply]
  · exact partialTraceSecondOp_trace ρ.operator ▸ ρ.trace_one

theorem partialTraceSecondDensityVerified_operator {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    (partialTraceSecondDensityVerified ρ).operator =
      partialTraceSecondOp ρ.operator := by
  rfl

theorem partialTraceSecondDensityVerified_trace_one {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    Matrix.trace (partialTraceSecondDensityVerified ρ).operator = 1 := by
  exact (partialTraceSecondDensityVerified ρ).trace_one
 -/

structure FiniteDensityOperator (ι : Type*) [Fintype ι] [DecidableEq ι] where
  operator : Matrix ι ι ℂ
  hermitian : operator.IsHermitian
  positive : ComplexPositive operator
  trace_one : Matrix.trace operator = 1

theorem complexPositive_partialTrace {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : ComplexPositive A) :
    ComplexPositive (partialTraceSecondOp A) := by
  classical
  intro v
  have hblock : ∀ j : Fin n,
      0 ≤ (∑ i, ∑ k, star (v i) * A (i, j) (k, j) * v k).re := by
    intro j
    exact complexPositive_block_fiber_verified hA j v
  have hrewrite :
      (∑ i, ∑ k, star (v i) * partialTraceSecondOp A i k * v k).re =
        (∑ j, ∑ i, ∑ k, star (v i) * A (i, j) (k, j) * v k).re := by
    congr 1
    simp only [partialTraceSecondOp]
    simp only [Finset.mul_sum, Finset.sum_mul]
    calc
      (∑ x, ∑ y, ∑ i, star (v x) * A (x, i) (y, i) * v y) =
          ∑ x, ∑ i, ∑ y, star (v x) * A (x, i) (y, i) * v y := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ y, star (v x) * A (x, i) (y, i) * v y := by
        exact Finset.sum_comm
      _ = ∑ j, ∑ i, ∑ k, star (v i) * A (i, j) (k, j) * v k := by
        rfl
  rw [hrewrite, Complex.re_sum]
  exact Finset.sum_nonneg (fun j _ => hblock j)

noncomputable def partialTraceSecondDensity {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    FiniteDensityOperator (Fin m) := by
  refine ⟨partialTraceSecondOp ρ.operator, ?_,
    complexPositive_partialTrace ρ.positive, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i k
    simp [partialTraceSecondOp, ρ.hermitian.apply]
  · exact partialTraceSecondOp_trace ρ.operator ▸ ρ.trace_one

theorem partialTraceSecondDensity_operator {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    (partialTraceSecondDensity ρ).operator = partialTraceSecondOp ρ.operator := by
  rfl

theorem partialTraceSecondDensity_trace_one {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    Matrix.trace (partialTraceSecondDensity ρ).operator = 1 := by
  exact (partialTraceSecondDensity ρ).trace_one

/-
theorem complexPositive_block {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : ComplexPositive A) (j : Fin n) :
    ComplexPositive (A.submatrix (fun i : Fin m => (i, j))
      (fun i : Fin m => (i, j))) := by
  classical
  intro v
  let w : Fin m × Fin n → ℂ := fun x => if x.2 = j then v x.1 else 0
  have hw := hA w
  simpa [w, Matrix.submatrix, Fintype.sum_prod_type,
    Finset.sum_ite_irrel, Finset.sum_ite_eq'] using hw

theorem complexPositive_partialTrace {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : ComplexPositive A) :
    ComplexPositive (partialTraceSecondOp A) := by
  classical
  intro v
  have hblocks : ∀ j : Fin n,
      0 ≤ (∑ i, ∑ k, star (v i) *
        A (i, j) (k, j) * v k).re := by
    intro j
    exact complexPositive_block hA j v
  simp only [partialTraceSecondOp, Matrix.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_comm]
  exact Finset.sum_nonneg (fun j _ => hblocks j)
 -/

noncomputable def diagonalFiniteDensity {n : ℕ}
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    FiniteDensityOperator (Fin n) := by
  refine ⟨Matrix.diagonal (fun i => (p i : ℂ)), ?_, ?_, ?_⟩
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact isSelfAdjoint_iff.mpr (by simp)
  · intro v
    simp [Matrix.diagonal_apply]
    apply Finset.sum_nonneg
    intro i hi
    nlinarith [sq_nonneg (v i).re, sq_nonneg (v i).im, hp i]
  · simpa [Matrix.trace, Matrix.diag] using congrArg (fun x : ℝ => (x : ℂ)) hsum

theorem diagonalFiniteDensity_operator {n : ℕ}
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (diagonalFiniteDensity p hp hsum).operator =
      Matrix.diagonal (fun i => (p i : ℂ)) := by
  rfl

theorem diagonalFiniteDensity_partialTrace {m n : ℕ}
    (p : Fin m → Fin n → ℝ) (_hp : ∀ i j, 0 ≤ p i j)
    (_hsum : ∑ i, ∑ j, p i j = 1) :
    partialTraceSecondOp (Matrix.diagonal (fun ij => (p ij.1 ij.2 : ℂ))) =
      Matrix.diagonal (fun i => (∑ j, p i j : ℝ) : Fin m → ℂ) := by
  ext i k
  by_cases hik : i = k
  · subst k
    simp [partialTraceSecondOp]
  · simp [partialTraceSecondOp, hik]

theorem diagonalFiniteDensity_softmax {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) :
    (fun i => Real.exp (z i) / ∑ j, Real.exp (z j)) =
      (InfoGeometry.Probability.AitchisonFinite.softmax n z hn).1 := by
  rfl

/-
theorem complexPositive_block_fiber {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : ComplexPositive A) (j : Fin n) :
    ComplexPositive (A.submatrix (fun i : Fin m => (i, j))
      (fun i : Fin m => (i, j))) := by
  classical
  intro v
  let w : Fin m × Fin n → ℂ := fun x => if x.2 = j then v x.1 else 0
  have hw := hA w
  rw [Fintype.sum_prod_type] at hw
  simp only [w, Matrix.submatrix] at hw ⊢
  simpa using hw
 -/

/-! The complex density-operator positivity layer is a separate frontier:
the scalar matrix partial trace and its trace identity are already verified. -/

/-
theorem complexPositive_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℂ} (hA : ComplexPositive A) (f : κ → ι) :
    ComplexPositive (A.submatrix f f) := by
  classical
  intro v
  let w : ι → ℂ := fun i => ∑ k : κ, if f k = i then v k else 0
  have hw : (∑ i, ∑ j, star (w i) * A i j * w j).re ≥ 0 := hA w
  simpa [w, Matrix.submatrix, Finset.sum_ite_irrel, Finset.sum_ite_eq'] using hw

theorem complexPositive_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → Matrix ι ι ℂ) (hA : ∀ k, ComplexPositive (A k)) :
    ComplexPositive (∑ k, A k) := by
  intro v
  simp only [Matrix.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_comm]
  exact Finset.sum_nonneg (fun k _ => hA k v)

structure FiniteDensityOperator (ι : Type*) [Fintype ι] [DecidableEq ι] where
  operator : Matrix ι ι ℂ
  hermitian : operator.IsHermitian
  positive : ComplexPositive operator
  trace_one : Matrix.trace operator = 1

noncomputable def partialTraceSecondDensity {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    FiniteDensityOperator (Fin m) := by
  let blocks : Fin n → Matrix (Fin m) (Fin m) ℂ :=
    fun j => ρ.operator.submatrix (fun i => (i, j)) (fun k => (k, j))
  have hpos : ∀ j, ComplexPositive (blocks j) := by
    intro j
    exact complexPositive_submatrix ρ.positive (fun i => (i, j))
  let S : Matrix (Fin m) (Fin m) ℂ := ∑ j, blocks j
  have hS : S = partialTraceSecondOp ρ.operator := by
    ext i k
    simp [S, blocks, partialTraceSecondOp]
  refine ⟨partialTraceSecondOp ρ.operator, ?_, ?_, ?_⟩
  · rw [← hS]
    simp only [Matrix.isHermitian_iff]
    intro i k
    simp [S, blocks, Matrix.submatrix, ρ.hermitian.apply]
  · rw [← hS]
    exact complexPositive_sum blocks hpos
  · exact partialTraceSecondOp_trace ρ.operator ▸ ρ.trace_one

theorem partialTraceSecondDensity_operator {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    (partialTraceSecondDensity ρ).operator = partialTraceSecondOp ρ.operator := by
  rfl

theorem partialTraceSecondDensity_trace_one {m n : ℕ}
    (ρ : FiniteDensityOperator (Fin m × Fin n)) :
    Matrix.trace (partialTraceSecondDensity ρ).operator = 1 := by
  exact (partialTraceSecondDensity ρ).trace_one
-/

/-- A diagonal bipartite state on two finite classical channels. -/
noncomputable def bipartiteState (m n : ℕ) :=
  (Fin m → Fin n → ℝ)

/-- The marginal obtained by tracing the second diagonal channel. -/
noncomputable def partialTraceSecond {m n : ℕ}
    (ρ : bipartiteState m n) : Fin m → ℝ :=
  fun i => ∑ j, ρ i j

theorem partialTraceSecond_sum
    {m n : ℕ} (ρ : bipartiteState m n)
    (hρ : ∑ i, ∑ j, ρ i j = 1) :
    ∑ i, partialTraceSecond ρ i = 1 := by
  simpa [partialTraceSecond] using hρ

theorem partialTraceSecond_nonneg
    {m n : ℕ} (ρ : bipartiteState m n)
    (hρ : ∀ i j, 0 ≤ ρ i j) (i : Fin m) :
    0 ≤ partialTraceSecond ρ i := by
  exact Finset.sum_nonneg (fun j _ => hρ i j)

noncomputable def partialTraceSecondSimplex {m n : ℕ}
    (_hm : 0 < m) (hn : 0 < n) (ρ : bipartiteState m n)
    (hρ : ∀ i j, 0 < ρ i j) (hρsum : ∑ i, ∑ j, ρ i j = 1) :
    PositiveSimplex m := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨partialTraceSecond ρ, ⟨
    fun i => Finset.sum_pos' (fun j _ => le_of_lt (hρ i j))
      ⟨⟨0, hn⟩, Finset.mem_univ _, hρ i ⟨0, hn⟩⟩,
    partialTraceSecond_sum ρ hρsum⟩⟩

theorem partialTraceSecondSimplex_apply {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (ρ : bipartiteState m n)
    (hρ : ∀ i j, 0 < ρ i j) (hρsum : ∑ i, ∑ j, ρ i j = 1)
    (i : Fin m) :
    (partialTraceSecondSimplex hm hn ρ hρ hρsum).1 i =
      ∑ j, ρ i j := rfl

/-- Diagonal matrix associated to a finite probability vector. -/
noncomputable def diagonalDensity {n : ℕ} (p : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal p

theorem diagonalDensity_trace {n : ℕ} (p : Fin n → ℝ) :
    Matrix.trace (diagonalDensity p) = ∑ i, p i := by
  simp [diagonalDensity, Matrix.trace_diagonal]

end Marginal

section IntegralTransforms

variable {d : ℕ}

/-- A Radon-type slice transform with the slice measure supplied explicitly. -/
noncomputable def radonSlice (μ : Fin d → Measure (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (ξ : Fin d) : ℝ :=
  ∫ x, f x ∂(μ ξ)

theorem radonSlice_add
    (μ : Fin d → Measure (Fin d → ℝ))
    (f g : (Fin d → ℝ) → ℝ) (ξ : Fin d)
    (hf : Integrable f (μ ξ)) (hg : Integrable g (μ ξ)) :
    radonSlice μ (fun x => f x + g x) ξ =
      radonSlice μ f ξ + radonSlice μ g ξ := by
  simp only [radonSlice]
  exact integral_add hf hg

/-- A measure-parametrised Fourier--Mellin carrier on positive scale. -/
noncomputable def fourierMellin (μt : Measure ℝ) (μr : Measure ℝ)
    (f : ℝ → ℝ → ℂ) (ω : ℝ) (s : ℂ) : ℂ :=
  ∫ t, ∫ r, f t r * Complex.exp (-Complex.I * ω * t) *
    Complex.exp ((s - 1) * Complex.log r) ∂μr ∂μt

theorem fourierMellin_zero (μt : Measure ℝ) (μr : Measure ℝ)
    (ω : ℝ) (s : ℂ) :
    fourierMellin μt μr (fun _ _ => 0) ω s = 0 := by
  simp [fourierMellin]

end IntegralTransforms

section CLRInverse

/-- The zero-sum logit carrier. -/
abbrev CenteredLogits (n : ℕ) :=
  {z : Fin n → ℝ // ∑ i, z i = 0}

noncomputable def clrInverse {n : ℕ} (z : CenteredLogits n) (hn : 0 < n) :
    PositiveSimplex n :=
  softmax n z.1 hn

theorem clrInverse_clr {n : ℕ} (z : CenteredLogits n) (hn : 0 < n) (i : Fin n) :
    clr (clrInverse z hn) hn i = z.1 i := by
  exact clr_softmax_centered z.1 hn z.2 i

theorem clr_pairwise_difference {n : ℕ} (p : PositiveSimplex n)
    (hn : 0 < n) (i j : Fin n) :
    clr p hn i - clr p hn j = Real.log (p.1 i / p.1 j) := by
  exact clr_sub_eq_log_ratio p hn i j

noncomputable def clrMap {n : ℕ} (hn : 0 < n) :
    PositiveSimplex n → CenteredLogits n :=
  fun p => ⟨clr p hn, sum_clr p hn⟩

noncomputable def clrHomeomorph {n : ℕ} (hn : 0 < n) :
    PositiveSimplex n ≃ₜ CenteredLogits n :=
  { toEquiv :=
      { toFun := clrMap hn
        invFun := fun z => clrInverse z hn
        left_inv := by
          intro p
          apply Subtype.ext
          funext i
          exact congrFun (congrArg Subtype.val (softmax_clr p hn)) i
        right_inv := by
          intro z
          apply Subtype.ext
          funext i
          exact clrInverse_clr z hn i }
    continuous_toFun := by
      exact Continuous.subtype_mk (continuous_clr hn)
        (fun p => sum_clr p hn)
    continuous_invFun := by
      simpa only [clrInverse] using
        (continuous_softmax hn).comp continuous_subtype_val }

theorem clrHomeomorph_apply {n : ℕ} (hn : 0 < n)
    (p : PositiveSimplex n) :
    clrHomeomorph hn p = clrMap hn p := by
  rfl

theorem clrHomeomorph_symm_apply {n : ℕ} (hn : 0 < n)
    (z : CenteredLogits n) :
    (clrHomeomorph hn).symm z = clrInverse z hn := by
  change clrInverse z hn = clrInverse z hn
  rfl

end CLRInverse

end InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
