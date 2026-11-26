/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.PositionalEncodingRepresentation
import InfoGeometry.Canonical.HypercomplexOneParameterFlows
import InfoGeometry.Clifford.Cl55RoPEAttentionPairing
import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Canonical.DrazinInfiniteCore
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Classification of Translation-Covariant Positional Encodings

This module closes the main formalization debts identified in
`docs/POSITIONAL_ENCODING_GROUP_THEORY_EPISTEMIC_COMPILATION.md` atop
`InfoGeometry.LLM.PositionalEncodingRepresentation`:

1. **Basis-change invariance, diagonal decoupling, and 2×2 real-canonical normal modes:**
   conjugation invariance `exp (t • (P X P⁻¹)) = P exp (t • X) P⁻¹`, decoupling of
   diagonalizable complex/real generators, the continuous homomorphism `ℂ →ₐ[ℝ] M₂(ℝ)`
   identifying `exp (t • realComplexBlock a b) = exp (a t) • rot2 (b t)`, arbitrary
   block-diagonal real-canonical flows, and stacked multi-frequency RoPE scores.
2. **Higher-order nilpotent Jordan blocks (`k × k` for arbitrary `k : ℕ`):**
   exact closed form of `(jordanShift k) ^ m`, exact finite-sum exponential truncation
   for any nilpotent `N ^ k = 0`, arbitrary `k × k` Jordan block exponentials, concrete
   `3 × 3` constant-acceleration hockey-puck kinematics, and degree-`(k - 1)` polynomial
   relative-position penalties (with ALiBi as `k = 2`).
3. **Stability trichotomy and causal decaying linear attention:**
   `x < 0` exponential decay (`Tendsto ... atTop (nhds 0)`), `x = 0` invariance,
   `x > 0` blowup, and exact equivalence between the causal recurrent linear-attention
   memory state `S_{n+1} = exp (-γ Δtₙ) • Sₙ + v_{n+1} k_{n+1}ᵀ` and the pairwise
   exponentially-decayed relative-position attention sum.
4. **Multi-dimensional translation groups `(ℝ^d, +)`, 2D image RoPE, and cross-lane bridges:**
   `MultiDimTranslationCovariantModifiers`, commuting infinitesimal generators on Banach
   spaces `M.relativeModifier x = exp (∑ i, x i • L i)`, concrete 2D image RoPE on `ℝ⁴`,
   an `InvariantRotorPairing` instance connecting `rot2` to `Cl55RoPEAttentionPairing`,
   and Drazin/Riesz zero-defect bridges for nilpotent Jordan blocks via
   `DrazinSpectralKernel` and `DrazinInfiniteCore`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.LLM.PositionalEncodingClassification

open Matrix NormedSpace Multiplicative
open InfoGeometry.LLM.PositionalEncodingRepresentation
open InfoGeometry.Canonical.HypercomplexOneParameterFlows
open InfoGeometry.Modular.SchrodingerFlow

universe u v w

/-! ## 1. Basis-change invariance, diagonal decoupling, and 2×2 real normal modes -/

section SpectralAndBlockDecomposition

/-- Time-scaled conjugation commutes with the matrix exponential. -/
theorem exp_smul_units_conj {n : Type u} [Fintype n] [DecidableEq n]
    (t : ℝ) (P : (Matrix n n ℝ)ˣ) (X : Matrix n n ℝ) :
    NormedSpace.exp (t • ((P : Matrix n n ℝ) * X * (↑P⁻¹ : Matrix n n ℝ))) =
      (P : Matrix n n ℝ) * NormedSpace.exp (t • X) * (↑P⁻¹ : Matrix n n ℝ) := by
  have hsmul : t • ((P : Matrix n n ℝ) * X * (↑P⁻¹ : Matrix n n ℝ)) =
      (P : Matrix n n ℝ) * (t • X) * (↑P⁻¹ : Matrix n n ℝ) := by
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [hsmul]
  exact Matrix.exp_units_conj P (t • X)

/-- Complex version of time-scaled conjugation invariance for matrix exponentials. -/
theorem exp_smul_units_conj_complex {n : Type u} [Fintype n] [DecidableEq n]
    (t : ℝ) (P : (Matrix n n ℂ)ˣ) (X : Matrix n n ℂ) :
    NormedSpace.exp ((t : ℂ) • ((P : Matrix n n ℂ) * X * (↑P⁻¹ : Matrix n n ℂ))) =
      (P : Matrix n n ℂ) * NormedSpace.exp ((t : ℂ) • X) * (↑P⁻¹ : Matrix n n ℂ) := by
  have hsmul : (t : ℂ) • ((P : Matrix n n ℂ) * X * (↑P⁻¹ : Matrix n n ℂ)) =
      (P : Matrix n n ℂ) * ((t : ℂ) • X) * (↑P⁻¹ : Matrix n n ℂ) := by
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [hsmul]
  exact Matrix.exp_units_conj P ((t : ℂ) • X)

/-- Time-independent invertible change of basis transforms the conjugated exponential
attention score into the score between dual-transformed queries and keys. -/
theorem attentionScore_conj_change_of_basis {n : Type u} [Fintype n] [DecidableEq n]
    (t : ℝ) (P : (Matrix n n ℝ)ˣ) (X : Matrix n n ℝ) (q k : n → ℝ) :
    attentionScore q
        ((NormedSpace.exp (t • ((P : Matrix n n ℝ) * X * (↑P⁻¹ : Matrix n n ℝ)))) *ᵥ k) =
      attentionScore ((P : Matrix n n ℝ)ᵀ *ᵥ q)
        ((NormedSpace.exp (t • X)) *ᵥ ((↑P⁻¹ : Matrix n n ℝ) *ᵥ k)) := by
  rw [exp_smul_units_conj]
  unfold attentionScore
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- Exponential of a time-scaled real diagonal generator. -/
theorem exp_smul_diagonal {n : Type u} [Fintype n] [DecidableEq n]
    (t : ℝ) (d : n → ℝ) :
    NormedSpace.exp (t • Matrix.diagonal d) =
      Matrix.diagonal (fun j => Real.exp (t * d j)) := by
  have hdiag : t • Matrix.diagonal d = Matrix.diagonal (fun j => t * d j) := by
    ext i j; by_cases hij : i = j <;> simp [hij]
  rw [hdiag, Matrix.exp_diagonal]
  congr 1
  funext j
  simp [Pi.coe_exp, Real.exp_eq_exp_ℝ]

/-- Exponential of a time-scaled complex diagonal generator. -/
theorem exp_smul_diagonal_complex {n : Type u} [Fintype n] [DecidableEq n]
    (t : ℝ) (d : n → ℂ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal d) =
      Matrix.diagonal (fun j => Complex.exp ((t : ℂ) * d j)) := by
  have hdiag : (t : ℂ) • Matrix.diagonal d = Matrix.diagonal (fun j => (t : ℂ) * d j) := by
    ext i j; by_cases hij : i = j <;> simp [hij]
  rw [hdiag, Matrix.exp_diagonal]
  congr 1
  funext j
  simp [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

/-- For a diagonal real generator, attention components completely decouple. -/
theorem attentionScore_diagonal_exp {n : Type u} [Fintype n] [DecidableEq n]
    (t : ℝ) (d q k : n → ℝ) :
    attentionScore q ((NormedSpace.exp (t • Matrix.diagonal d)) *ᵥ k) =
      ∑ j : n, q j * Real.exp (t * d j) * k j := by
  rw [exp_smul_diagonal]
  unfold attentionScore dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_diagonal]
  exact (mul_assoc (q j) (Real.exp (t * d j)) (k j)).symm

/-- For any complex-diagonalizable generator `X = P * diagonal d * P⁻¹`, the score
decouples into independent scalar complex modes in the eigenbasis. -/
theorem attentionScore_diagonalizable_exp {n : Type u} [Fintype n] [DecidableEq n]
    (t : ℝ) (P : (Matrix n n ℂ)ˣ) (d q k : n → ℂ) :
    attentionScore q
        ((NormedSpace.exp ((t : ℂ) • ((P : Matrix n n ℂ) * Matrix.diagonal d * (↑P⁻¹ : Matrix n n ℂ)))) *ᵥ k) =
      ∑ j : n, ((P : Matrix n n ℂ)ᵀ *ᵥ q) j *
        (Complex.exp ((t : ℂ) * d j) * ((↑P⁻¹ : Matrix n n ℂ) *ᵥ k) j) := by
  rw [exp_smul_units_conj_complex, exp_smul_diagonal_complex]
  unfold attentionScore
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have hP : (P : Matrix n n ℂ)ᵀ *ᵥ q = q ᵥ* (P : Matrix n n ℂ) :=
    Matrix.mulVec_transpose (P : Matrix n n ℂ) q
  rw [hP]
  unfold dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_diagonal]

/-- Infinitesimal generator of 2D planar rotation `[[0, -1], [1, 0]]`. -/
def rotGen2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

/-- Real 2×2 representation `[[a, -b], [b, a]]` of `a + b i ∈ ℂ`. -/
def realComplexBlock (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, -b; b, a]

/-- Planar 2D rotation matrix `rot2 θ`. -/
def rot2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotGen2_sq : rotGen2 * rotGen2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotGen2, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

/-- Non-commutativity witness on `M₂(ℝ)`: the planar rotation generator and the 2×2
upper-triangular shift do not commute. -/
theorem noncomm_rotGen2_shift2 :
    rotGen2 * (!![0, (1 : ℝ); 0, 0]) ≠ (!![0, (1 : ℝ); 0, 0]) * rotGen2 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [rotGen2, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Closed existential non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem exists_noncomm_mat2_real :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨rotGen2, !![0, (1 : ℝ); 0, 0], noncomm_rotGen2_shift2⟩

theorem realComplexBlock_eq_add (a b : ℝ) :
    realComplexBlock a b = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) + b • rotGen2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realComplexBlock, rotGen2]

theorem realComplexBlock_zero_zero : realComplexBlock 0 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realComplexBlock]

theorem realComplexBlock_one_zero :
    realComplexBlock 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realComplexBlock]

theorem realComplexBlock_add (a₁ b₁ a₂ b₂ : ℝ) :
    realComplexBlock (a₁ + a₂) (b₁ + b₂) =
      realComplexBlock a₁ b₁ + realComplexBlock a₂ b₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realComplexBlock] <;> abel

theorem realComplexBlock_smul (r a b : ℝ) :
    realComplexBlock (r * a) (r * b) = r • realComplexBlock a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realComplexBlock] <;> ring

theorem realComplexBlock_mul (a₁ b₁ a₂ b₂ : ℝ) :
    realComplexBlock (a₁ * a₂ - b₁ * b₂) (a₁ * b₂ + b₁ * a₂) =
      realComplexBlock a₁ b₁ * realComplexBlock a₂ b₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realComplexBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rot2_eq_realComplexBlock (θ : ℝ) :
    rot2 θ = realComplexBlock (Real.cos θ) (Real.sin θ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot2, realComplexBlock]

theorem rot2_zero : rot2 0 = 1 := by
  rw [rot2_eq_realComplexBlock, Real.cos_zero, Real.sin_zero, realComplexBlock_one_zero]

theorem rot2_add (s t : ℝ) : rot2 (s + t) = rot2 s * rot2 t := by
  rw [rot2_eq_realComplexBlock, rot2_eq_realComplexBlock, rot2_eq_realComplexBlock,
    Real.cos_add, Real.sin_add, add_comm (Real.sin s * Real.cos t), realComplexBlock_mul]

theorem rot2_transpose (θ : ℝ) : (rot2 θ)ᵀ = rot2 (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot2, Real.cos_neg, Real.sin_neg]

theorem rot2_mul_neg (θ : ℝ) : rot2 θ * rot2 (-θ) = 1 := by
  rw [← rot2_add, add_neg_cancel, rot2_zero]

theorem rot2_neg_mul (θ : ℝ) : rot2 (-θ) * rot2 θ = 1 := by
  rw [← rot2_add, neg_add_cancel, rot2_zero]

/-- Continuous `ℝ`-algebra embedding of `ℂ` into `2 × 2` real matrices. -/
def complexToMat2 : ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun z := realComplexBlock z.re z.im
  map_one' := by simp [realComplexBlock_one_zero]
  map_mul' z w := by
    simp only [Complex.mul_re, Complex.mul_im]
    exact realComplexBlock_mul z.re z.im w.re w.im
  map_zero' := by simp [realComplexBlock_zero_zero]
  map_add' z w := by
    simp only [Complex.add_re, Complex.add_im]
    exact realComplexBlock_add z.re z.im w.re w.im
  commutes' r := by
    rw [realComplexBlock_eq_add]
    simp [Algebra.algebraMap_eq_smul_one]

theorem continuous_complexToMat2 : Continuous complexToMat2 := by
  change Continuous fun z : ℂ => realComplexBlock z.re z.im
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [realComplexBlock] <;> continuity

/-- `complexToMat2` intertwines the complex exponential with the matrix exponential. -/
theorem complexToMat2_exp (z : ℂ) :
    complexToMat2 (Complex.exp z) = NormedSpace.exp (complexToMat2 z) := by
  have hsumC : HasSum (fun n : ℕ => ((n.factorial : ℚ)⁻¹) • z ^ n) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' z
  have hsumM : HasSum (fun n : ℕ => ((n.factorial : ℚ)⁻¹) • (complexToMat2 z) ^ n)
      (complexToMat2 (Complex.exp z)) := by
    have hmap := hsumC.map complexToMat2.toAddMonoidHom continuous_complexToMat2
    refine hmap.congr_fun fun n => ?_
    dsimp [Function.comp_def]
    rw [← map_pow, ← map_rat_smul complexToMat2]
  have hsumExp : HasSum (fun n : ℕ => ((n.factorial : ℚ)⁻¹) • (complexToMat2 z) ^ n)
      (NormedSpace.exp (complexToMat2 z)) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (complexToMat2 z)
  exact hsumM.unique hsumExp

/-- Exact exponential of the 2×2 real rotation-scaling generator `realComplexBlock a b`:
exponential radial factor `exp (a t)` times planar rotation `rot2 (b t)`. -/
theorem exp_smul_realComplexBlock (t a b : ℝ) :
    NormedSpace.exp (t • realComplexBlock a b) = Real.exp (a * t) • rot2 (b * t) := by
  let z : ℂ := ⟨a, b⟩
  have hcm : complexToMat2 ((t : ℂ) * z) = t • realComplexBlock a b := by
    change realComplexBlock (((t : ℂ) * z).re) (((t : ℂ) * z).im) = t • realComplexBlock a b
    simp only [z, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    exact realComplexBlock_smul t a b
  rw [← hcm, ← complexToMat2_exp]
  have hz : (t : ℂ) * z = ((t * a : ℝ) : ℂ) + ((t * b : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [z]
  rw [hz, Complex.exp_add_mul_I]
  change realComplexBlock _ _ = Real.exp (a * t) • rot2 (b * t)
  rw [rot2_eq_realComplexBlock, ← realComplexBlock_smul]
  have hexp :
      Complex.exp ((t * a : ℝ) : ℂ) = ((Real.exp (t * a) : ℝ) : ℂ) :=
    (Complex.ofReal_exp (t * a)).symm
  rw [hexp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_mul, zero_add]
  have hta : t * a = a * t := mul_comm t a
  have htb : t * b = b * t := mul_comm t b
  rw [hta, htb]

/-- Exponential of a planar rotation generator equals `rot2 θ`. -/
theorem exp_smul_rotGen2 (θ : ℝ) :
    NormedSpace.exp (θ • rotGen2) = rot2 θ := by
  have hgen : rotGen2 = realComplexBlock 0 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotGen2, realComplexBlock]
  rw [hgen, exp_smul_realComplexBlock, zero_mul, Real.exp_zero, one_smul, one_mul]

/-- Entrywise multiplication of a sigma-indexed `Matrix.blockDiagonal'` matrix on a vector. -/
theorem blockDiagonal'_mulVec {κ : Type u} [Fintype κ] [DecidableEq κ]
    {d : κ → Type v} [∀ i, Fintype (d i)]
    (B : ∀ i, Matrix (d i) (d i) ℝ) (x : (Σ i, d i) → ℝ) (i : κ) (j : d i) :
    (Matrix.blockDiagonal' B *ᵥ x) ⟨i, j⟩ = (B i *ᵥ fun k => x ⟨i, k⟩) j := by
  change ∑ p : Σ i', d i', (Matrix.blockDiagonal' B ⟨i, j⟩ p) * x p =
    ∑ k : d i, B i j k * x ⟨i, k⟩
  rw [Fintype.sum_sigma]
  have hsum :
      (∑ i' : κ, ∑ k : d i', Matrix.blockDiagonal' B ⟨i, j⟩ ⟨i', k⟩ * x ⟨i', k⟩) =
        ∑ k : d i, Matrix.blockDiagonal' B ⟨i, j⟩ ⟨i, k⟩ * x ⟨i, k⟩ := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro i' _ hne
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [Matrix.blockDiagonal'_apply, hne.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.blockDiagonal'_apply]

/-- Exponential of a time-scaled block-diagonal generator decomposes block by block. -/
theorem exp_smul_blockDiagonal' {κ : Type u} [Fintype κ] [DecidableEq κ]
    {d : κ → Type v} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    (t : ℝ) (B : ∀ i, Matrix (d i) (d i) ℝ) :
    NormedSpace.exp (t • Matrix.blockDiagonal' B) =
      Matrix.blockDiagonal' (fun i => NormedSpace.exp (t • B i)) := by
  have hsmul : t • Matrix.blockDiagonal' B = Matrix.blockDiagonal' (fun i => t • B i) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst h; simp [Matrix.blockDiagonal'_apply]
    · simp [Matrix.blockDiagonal'_apply, h]
  rw [hsmul, Matrix.exp_blockDiagonal']
  have hpi : NormedSpace.exp (fun i => t • B i) = fun i => NormedSpace.exp (t • B i) := by
    open scoped Matrix.Norms.Operator in exact Pi.exp_def (fun i => t • B i)
  rw [hpi]

/-- Block-diagonal real-canonical decomposition of attention scores: each invariant subspace
contributes independently. -/
theorem attentionScore_blockDiagonal'_exp {κ : Type u} [Fintype κ] [DecidableEq κ]
    {d : κ → Type v} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    (t : ℝ) (B : ∀ i, Matrix (d i) (d i) ℝ) (q k : (Σ i, d i) → ℝ) :
    attentionScore q ((NormedSpace.exp (t • Matrix.blockDiagonal' B)) *ᵥ k) =
      ∑ i : κ, attentionScore (fun j => q ⟨i, j⟩)
        ((NormedSpace.exp (t • B i)) *ᵥ (fun j => k ⟨i, j⟩)) := by
  rw [exp_smul_blockDiagonal']
  unfold attentionScore dotProduct
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blockDiagonal'_mulVec]

/-- Multi-frequency RoPE generator stacked along `m` 2D blocks (`Fin 2 × Fin m`). -/
def ropeStackGenerator {m : ℕ} (freqs : Fin m → ℝ) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℝ :=
  Matrix.blockDiagonal (fun i => freqs i • rotGen2)

/-- The exponential of a multi-frequency RoPE generator is the block-diagonal stack of
planar rotations `rot2 (t * freqs i)`. -/
theorem exp_ropeStackGenerator {m : ℕ} (freqs : Fin m → ℝ) (t : ℝ) :
    NormedSpace.exp (t • ropeStackGenerator freqs) =
      Matrix.blockDiagonal (fun i => rot2 (t * freqs i)) := by
  have hsmul : t • ropeStackGenerator freqs =
      Matrix.blockDiagonal (fun i => (t * freqs i) • rotGen2) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases h : i = j
    · subst h; simp [ropeStackGenerator, Matrix.blockDiagonal_apply, mul_smul]
    · simp [ropeStackGenerator, Matrix.blockDiagonal_apply, h]
  rw [hsmul, Matrix.exp_blockDiagonal]
  have hpi : NormedSpace.exp (fun i => (t * freqs i) • rotGen2) =
      fun i => NormedSpace.exp ((t * freqs i) • rotGen2) := by
    open scoped Matrix.Norms.Operator in
    exact Pi.exp_def (fun i => (t * freqs i) • rotGen2)
  rw [hpi]
  congr 1
  funext i
  exact exp_smul_rotGen2 (t * freqs i)

theorem blockDiagonal_mulVec {κ : Type u} [Fintype κ] [DecidableEq κ]
    {d : Type v} [Fintype d]
    (B : κ → Matrix d d ℝ) (x : d × κ → ℝ) (j : d) (i : κ) :
    (Matrix.blockDiagonal B *ᵥ x) (j, i) = (B i *ᵥ fun k => x (k, i)) j := by
  change ∑ p : d × κ, Matrix.blockDiagonal B (j, i) p * x p = ∑ k : d, B i j k * x (k, i)
  rw [Fintype.sum_prod_type_right]
  have hsum :
      (∑ i' : κ, ∑ k : d, Matrix.blockDiagonal B (j, i) (k, i') * x (k, i')) =
        ∑ k : d, Matrix.blockDiagonal B (j, i) (k, i) * x (k, i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro i' _ hne
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [Matrix.blockDiagonal_apply, hne.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.blockDiagonal_apply]

/-- Relative-position invariance of a stacked multi-frequency RoPE layer. -/
theorem ropeStack_relative_attentionScore {m : ℕ} (freqs : Fin m → ℝ)
    (t s : ℝ) (q k : Fin 2 × Fin m → ℝ) :
    attentionScore
        ((NormedSpace.exp (t • ropeStackGenerator freqs)) *ᵥ q)
        ((NormedSpace.exp (s • ropeStackGenerator freqs)) *ᵥ k) =
      attentionScore q
        ((NormedSpace.exp ((s - t) • ropeStackGenerator freqs)) *ᵥ k) := by
  rw [transformed_attentionScore_eq_relative, exp_ropeStackGenerator, exp_ropeStackGenerator,
    exp_ropeStackGenerator]
  have hT :
      (Matrix.blockDiagonal fun i => rot2 (t * freqs i))ᵀ =
        Matrix.blockDiagonal fun i => rot2 (-(t * freqs i)) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases h : i = j
    · subst h
      simp [Matrix.blockDiagonal_apply, ← rot2_transpose]
    · simp [Matrix.blockDiagonal_apply, h, Ne.symm h]
  have hmul :
      (Matrix.blockDiagonal fun i => rot2 (-(t * freqs i))) *
          (Matrix.blockDiagonal fun i => rot2 (s * freqs i)) =
        Matrix.blockDiagonal fun i => rot2 ((s - t) * freqs i) := by
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext i
    rw [← rot2_add]
    congr 1
    rw [sub_mul, ← neg_add_eq_sub]
  rw [hT, hmul]

end SpectralAndBlockDecomposition

/-! ## 2. Higher-order Jordan blocks (`k × k`) and polynomial penalties -/

section HigherJordanBlocks

/-- Superdiagonal nilpotent shift matrix of arbitrary dimension `k`. -/
def jordanShift (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if j.1 = i.1 + 1 then 1 else 0

/-- Jordan block `λ I + N` of arbitrary size `k`. -/
def jordanBlock (k : ℕ) (lam : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  lam • (1 : Matrix (Fin k) (Fin k) ℝ) + jordanShift k

/-- Exact entrywise formula for the `m`-th power of `jordanShift k`. -/
theorem jordanShift_pow_apply (k m : ℕ) (i j : Fin k) :
    ((jordanShift k) ^ m) i j = if j.1 = i.1 + m then 1 else 0 := by
  induction m generalizing i j with
  | zero =>
      simp only [pow_zero, Nat.add_zero, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : j.1 ≠ i.1 := fun h => hij (Fin.ext h.symm)
        simp [hij, hne]
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      have hterm : ∀ r : Fin k,
          ((jordanShift k) ^ m) i r * jordanShift k r j =
            if r.1 = i.1 + m then (if j.1 = r.1 + 1 then 1 else 0) else 0 := by
        intro r
        rw [ih i r]
        by_cases hr : r.1 = i.1 + m
        · simp [hr, jordanShift]
        · simp [hr]
      simp_rw [hterm]
      by_cases hlt : i.1 + m < k
      · let r0 : Fin k := ⟨i.1 + m, hlt⟩
        have huniq : ∀ r : Fin k,
            (if r.1 = i.1 + m then (if j.1 = r.1 + 1 then (1 : ℝ) else 0) else 0) =
              if r = r0 then (if j.1 = i.1 + (m + 1) then 1 else 0) else 0 := by
          intro r
          by_cases hr : r = r0
          · subst hr; simp [r0, Nat.add_assoc]
          · have hr1 : r.1 ≠ i.1 + m := fun heq => hr (Fin.ext heq)
            simp [hr, hr1]
        simp_rw [huniq]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ r0)]
      · have hjne : j.1 ≠ i.1 + (m + 1) := by omega
        rw [if_neg hjne]
        refine Finset.sum_eq_zero fun r _ => ?_
        have hrne : r.1 ≠ i.1 + m := by omega
        simp [hrne]

/-- The `k × k` Jordan shift is nilpotent of index `k`. -/
theorem jordanShift_pow_self_eq_zero (k : ℕ) : (jordanShift k) ^ k = 0 := by
  ext i j
  rw [jordanShift_pow_apply]
  have hne : j.1 ≠ i.1 + k := by omega
  simp [hne]

/-- Higher powers `m ≥ k` of `jordanShift k` vanish. -/
theorem jordanShift_pow_eq_zero_of_le (k : ℕ) {m : ℕ} (hm : k ≤ m) :
    (jordanShift k) ^ m = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, jordanShift_pow_self_eq_zero, zero_mul]

/-- Any nilpotent matrix `N ^ k = 0` has an exact finite polynomial exponential. -/
theorem exp_smul_of_pow_eq_zero {n : Type u} [Fintype n] [DecidableEq n]
    {N : Matrix n n ℝ} {k : ℕ} (hN : N ^ k = 0) (t : ℝ) :
    NormedSpace.exp (t • N) =
      ∑ m ∈ Finset.range k, (t ^ m / (m.factorial : ℝ)) • N ^ m := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  have hpow : ∀ m : ℕ, (m.factorial : ℝ)⁻¹ • (t • N) ^ m =
      (t ^ m / (m.factorial : ℝ)) • N ^ m := by
    intro m
    rw [smul_pow, smul_smul, div_eq_inv_mul]
  simp_rw [hpow]
  refine tsum_eq_sum fun m hm => ?_
  have hkm : k ≤ m := by
    rw [Finset.mem_range] at hm
    omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [pow_add N k r, hN, zero_mul, smul_zero]

/-- Exact closed form for the exponential of an arbitrary `k × k` Jordan block. -/
theorem exp_smul_jordanBlock (k : ℕ) (lam t : ℝ) :
    NormedSpace.exp (t • jordanBlock k lam) =
      Real.exp (lam * t) •
        ∑ m ∈ Finset.range k, (t ^ m / (m.factorial : ℝ)) • (jordanShift k) ^ m := by
  have hdecomp : t • jordanBlock k lam =
      (t * lam) • (1 : Matrix (Fin k) (Fin k) ℝ) + t • jordanShift k := by
    simp [jordanBlock, smul_add, smul_smul]
  have hcomm : Commute ((t * lam) • (1 : Matrix (Fin k) (Fin k) ℝ)) (t • jordanShift k) := by
    exact (Commute.one_left (t • jordanShift k)).smul_left (t * lam)
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm,
    exp_smul_of_pow_eq_zero (jordanShift_pow_self_eq_zero k) t]
  have hdiag : (t * lam) • (1 : Matrix (Fin k) (Fin k) ℝ) =
      Matrix.diagonal (fun _ : Fin k => t * lam) := by
    ext i j; by_cases hij : i = j <;> simp [hij]
  rw [hdiag, Matrix.exp_diagonal]
  have hexp : (Matrix.diagonal (NormedSpace.exp (fun _ : Fin k => t * lam))) =
      Real.exp (lam * t) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Pi.coe_exp, Real.exp_eq_exp_ℝ, mul_comm]
    · simp [hij]
  rw [hexp, smul_mul_assoc, one_mul]

/-- Entrywise upper-triangular polynomial-exponential formula for `exp (t • jordanBlock k lam)`. -/
theorem exp_smul_jordanBlock_apply (k : ℕ) (lam t : ℝ) (i j : Fin k) :
    NormedSpace.exp (t • jordanBlock k lam) i j =
      if i.1 ≤ j.1 then
        Real.exp (lam * t) * (t ^ (j.1 - i.1) / ((j.1 - i.1).factorial : ℝ))
      else 0 := by
  rw [exp_smul_jordanBlock, Matrix.smul_apply, Matrix.sum_apply]
  by_cases hij : i.1 ≤ j.1
  · rw [if_pos hij]
    have hmem : j.1 - i.1 ∈ Finset.range k := by
      rw [Finset.mem_range]; omega
    have hsum :
        (∑ m ∈ Finset.range k, ((t ^ m / (m.factorial : ℝ)) • (jordanShift k) ^ m) i j) =
          t ^ (j.1 - i.1) / ((j.1 - i.1).factorial : ℝ) := by
      rw [Finset.sum_eq_single (j.1 - i.1)]
      · have hj : j.1 = i.1 + (j.1 - i.1) := by omega
        rw [Matrix.smul_apply, smul_eq_mul, jordanShift_pow_apply, if_pos hj, mul_one]
      · intro m _ hmne
        have hj : j.1 ≠ i.1 + m := by omega
        rw [Matrix.smul_apply, smul_eq_mul, jordanShift_pow_apply, if_neg hj, mul_zero]
      · intro hnot; exact absurd hmem hnot
    rw [hsum, smul_eq_mul]
  · rw [if_neg hij]
    have hsum :
        (∑ m ∈ Finset.range k, ((t ^ m / (m.factorial : ℝ)) • (jordanShift k) ^ m) i j) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      have hj : j.1 ≠ i.1 + m := by omega
      rw [Matrix.smul_apply, smul_eq_mul, jordanShift_pow_apply, if_neg hj, mul_zero]
    rw [hsum, smul_zero]

/-- Concrete 3×3 constant-acceleration hockey-puck flow generated by `jordanBlock 3 0`. -/
theorem jordanBlock_kinematic_3x3 (t x₀ v₀ a₀ : ℝ) :
    (NormedSpace.exp (t • jordanBlock 3 (0 : ℝ))) *ᵥ ![x₀, v₀, a₀] =
      ![x₀ + v₀ * t + (1 / 2 : ℝ) * a₀ * t ^ 2, v₀ + a₀ * t, a₀] := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    exp_smul_jordanBlock_apply]
  fin_cases i <;>
    simp <;> ring

/-- Query vector selecting the `0`-th coordinate of a `k × k` Jordan clock block. -/
def polynomialPenaltyQuery (k : ℕ) (hk : 0 < k) : Fin k → ℝ :=
  fun i => if i = ⟨0, hk⟩ then 1 else 0

/-- Key vector weighted by inverse factorials so `exp (t • jordanShift k) *ᵥ k`
evaluates to a polynomial of degree `k - 1`. -/
def polynomialClockKey {k : ℕ} (c : Fin k → ℝ) : Fin k → ℝ :=
  fun j => c j * (j.1.factorial : ℝ)

/-- A `k × k` nilpotent Jordan block realizes an arbitrary degree-`(k - 1)` polynomial
relative-position attention bias `∑ j, c j * (t - s) ^ j`. -/
theorem polynomialRelativePenalty_from_jordanBlock {k : ℕ} (hk : 0 < k)
    (c : Fin k → ℝ) (t s : ℝ) :
    attentionScore (polynomialPenaltyQuery k hk)
        ((NormedSpace.exp ((t - s) • jordanShift k)) *ᵥ polynomialClockKey c) =
      ∑ j : Fin k, c j * (t - s) ^ j.1 := by
  have hj0 : jordanShift k = jordanBlock k 0 := by
    simp [jordanBlock]
  rw [hj0]
  unfold attentionScore dotProduct
  rw [Finset.sum_eq_single ⟨0, hk⟩]
  · simp only [polynomialPenaltyQuery, ↓reduceIte, one_mul, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [exp_smul_jordanBlock_apply]
    have h0j : (⟨0, hk⟩ : Fin k).1 ≤ j.1 := Nat.zero_le _
    rw [if_pos h0j, zero_mul, Real.exp_zero, one_mul, Nat.sub_zero]
    have hfac : (j.1.factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j.1)
    simp only [polynomialClockKey]
    field_simp [hfac]
  · intro i _ hne
    simp [polynomialPenaltyQuery, hne]
  · intro hnot
    exact absurd (Finset.mem_univ (⟨0, hk⟩ : Fin k)) hnot

/-- Recovering the linear ALiBi penalty `-p * (t - s)` as the `k = 2` Jordan case. -/
theorem alibi_recovered_from_jordanBlock_deg1 (p t s : ℝ) :
    attentionScore (polynomialPenaltyQuery 2 (by decide))
        ((NormedSpace.exp ((t - s) • jordanShift 2)) *ᵥ polynomialClockKey ![0, -p]) =
      -p * (t - s) := by
  rw [polynomialRelativePenalty_from_jordanBlock]
  simp [Fin.sum_univ_two]

end HigherJordanBlocks

/-! ## 3. Stability trichotomy and causal decaying linear attention -/

section LinearAttentionDecay

/-- Stability trichotomy, case `x < 0`: exponential suppression tends to `0` as `t → ∞`. -/
theorem real_exp_decay_tendsto_zero {x : ℝ} (hx : x < 0) :
    Filter.Tendsto (fun t : ℝ => Real.exp (t * x)) Filter.atTop (nhds 0) := by
  have hmul : Filter.Tendsto (fun t : ℝ => t * x) Filter.atTop Filter.atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg hx Filter.tendsto_id
  exact Real.tendsto_exp_atBot.comp hmul

/-- For `x ≤ 0` and `t ≥ 0`, exponential attention weights remain bounded in `(0, 1]`. -/
theorem real_exp_decay_le_one {x t : ℝ} (hx : x ≤ 0) (ht : 0 ≤ t) :
    0 < Real.exp (t * x) ∧ Real.exp (t * x) ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonneg_of_nonpos ht hx

/-- Stability trichotomy, case `x = 0`: time-independent constant factor `1`. -/
theorem real_exp_zero_const (t : ℝ) : Real.exp (t * (0 : ℝ)) = 1 := by
  simp

/-- Stability trichotomy, case `x > 0`: exponential blowup as `t → ∞`. -/
theorem real_exp_growth_tendsto_atTop {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun t : ℝ => Real.exp (t * x)) Filter.atTop Filter.atTop := by
  have hmul : Filter.Tendsto (fun t : ℝ => t * x) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hx Filter.tendsto_id
  exact Real.tendsto_exp_atTop.comp hmul

/-- Isotropic exponential-decay matrix unit `exp (-γ t) • 1`. -/
def decayUnit {d : ℕ} (γ t : ℝ) : Units (Matrix (Fin d) (Fin d) ℝ) where
  val := Real.exp (-γ * t) • (1 : Matrix (Fin d) (Fin d) ℝ)
  inv := Real.exp (γ * t) • (1 : Matrix (Fin d) (Fin d) ℝ)
  val_inv := by
    rw [smul_mul_smul_comm, mul_one, ← Real.exp_add]
    have h : -γ * t + γ * t = 0 := by ring
    rw [h, Real.exp_zero, one_smul]
  inv_val := by
    rw [smul_mul_smul_comm, mul_one, ← Real.exp_add]
    have h : γ * t + -γ * t = 0 := by ring
    rw [h, Real.exp_zero, one_smul]

/-- Canonical 1-parameter flow for scalar-rate decaying linear attention. -/
def decayFlow {d : ℕ} (γ : ℝ) :
    RealOneParameterFlow (Matrix (Fin d) (Fin d) ℝ) where
  flowHom :=
    { toFun := fun t => decayUnit γ (toAdd t)
      map_one' := by
        apply Units.ext
        simp [decayUnit]
      map_mul' := fun s t => by
        apply Units.ext
        change Real.exp (-γ * (toAdd s + toAdd t)) • (1 : Matrix (Fin d) (Fin d) ℝ) =
          (Real.exp (-γ * toAdd s) • (1 : Matrix (Fin d) (Fin d) ℝ)) *
            (Real.exp (-γ * toAdd t) • (1 : Matrix (Fin d) (Fin d) ℝ))
        rw [smul_mul_smul_comm, mul_one, ← Real.exp_add]
        congr 1
        ring }

theorem decayFlow_eq_exp {d : ℕ} (γ t : ℝ) :
    (decayFlow (d := d) γ).eval t =
      NormedSpace.exp (t • ((-γ) • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
  have hdiag : (-γ) • (1 : Matrix (Fin d) (Fin d) ℝ) =
      Matrix.diagonal (fun _ : Fin d => -γ) := by
    ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hdiag, exp_smul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [decayFlow, RealOneParameterFlow.eval, RealOneParameterFlow.evalUnit, decayUnit,
      Matrix.one_apply, mul_comm]
  · simp [decayFlow, RealOneParameterFlow.eval, RealOneParameterFlow.evalUnit, decayUnit,
      Matrix.one_apply, hij]

/-- Multi-channel diagonal exponential decay flow `diag (exp (-γ_i t))`. -/
def multiChannelDecayUnit {d : ℕ} (γ : Fin d → ℝ) (t : ℝ) :
    Units (Matrix (Fin d) (Fin d) ℝ) where
  val := Matrix.diagonal (fun i => Real.exp (-γ i * t))
  inv := Matrix.diagonal (fun i => Real.exp (γ i * t))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← Real.exp_add]
      have h : -γ i * t + γ i * t = 0 := by ring
      rw [h, Real.exp_zero]
    · simp [hij]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← Real.exp_add]
      have h : γ i * t + -γ i * t = 0 := by ring
      rw [h, Real.exp_zero]
    · simp [hij]

/-- Canonical 1-parameter flow for per-coordinate decaying linear attention. -/
def multiChannelDecayFlow {d : ℕ} (γ : Fin d → ℝ) :
    RealOneParameterFlow (Matrix (Fin d) (Fin d) ℝ) where
  flowHom :=
    { toFun := fun t => multiChannelDecayUnit γ (toAdd t)
      map_one' := by
        apply Units.ext
        ext i j; by_cases hij : i = j <;> simp [multiChannelDecayUnit, hij]
      map_mul' := fun s t => by
        apply Units.ext
        change Matrix.diagonal (fun i => Real.exp (-γ i * (toAdd s + toAdd t))) =
          Matrix.diagonal (fun i => Real.exp (-γ i * toAdd s)) *
            Matrix.diagonal (fun i => Real.exp (-γ i * toAdd t))
        rw [Matrix.diagonal_mul_diagonal]
        congr 1; funext i
        rw [← Real.exp_add]
        congr 1; ring }

theorem multiChannelDecayFlow_eq_exp {d : ℕ} (γ : Fin d → ℝ) (t : ℝ) :
    (multiChannelDecayFlow γ).eval t =
      NormedSpace.exp (t • Matrix.diagonal (fun i => -γ i)) := by
  rw [exp_smul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [multiChannelDecayFlow, RealOneParameterFlow.eval, RealOneParameterFlow.evalUnit,
      multiChannelDecayUnit, mul_comm]
  · simp [multiChannelDecayFlow, RealOneParameterFlow.eval, RealOneParameterFlow.evalUnit,
      multiChannelDecayUnit, hij]

/-- Causal recurrent linear-attention memory state with continuous-time exponential decay:
`S 0 = v₀ k₀ᵀ` and `S (n + 1) = exp (-γ (t_{n+1} - tₙ)) • S n + v_{n+1} k_{n+1}ᵀ`. -/
def linearAttentionState {d dv : ℕ} (γ : ℝ) (times : ℕ → ℝ)
    (keys : ℕ → Fin d → ℝ) (vals : ℕ → Fin dv → ℝ) : ℕ → Matrix (Fin dv) (Fin d) ℝ
  | 0 => Matrix.vecMulVec (vals 0) (keys 0)
  | n + 1 =>
      Real.exp (-γ * (times (n + 1) - times n)) •
          linearAttentionState γ times keys vals n +
        Matrix.vecMulVec (vals (n + 1)) (keys (n + 1))

/-- Exact unrolling of the causal linear-attention recurrence into a sum over all past
tokens `j ≤ n` weighted by `exp (-γ (times n - times j))`. -/
theorem linearAttentionState_eq_sum {d dv : ℕ} (γ : ℝ) (times : ℕ → ℝ)
    (keys : ℕ → Fin d → ℝ) (vals : ℕ → Fin dv → ℝ) (n : ℕ) :
    linearAttentionState γ times keys vals n =
      ∑ j ∈ Finset.range (n + 1),
        Real.exp (-γ * (times n - times j)) • Matrix.vecMulVec (vals j) (keys j) := by
  induction n with
  | zero =>
      simp [linearAttentionState]
  | succ n ih =>
      rw [linearAttentionState, ih, Finset.smul_sum, Finset.sum_range_succ _ (n + 1)]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, ← Real.exp_add]
        congr 2
        rw [← mul_add, sub_add_sub_cancel]
      · have hself : times (n + 1) - times (n + 1) = 0 := sub_self _
        rw [hself, mul_zero, Real.exp_zero, one_smul]

private theorem sum_matrix_mulVec {m n : Type*} [Fintype n]
    (s : Finset ℕ) (M : ℕ → Matrix m n ℝ) (q : n → ℝ) :
    (∑ j ∈ s, M j) *ᵥ q = ∑ j ∈ s, M j *ᵥ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]

/-- Causal linear-attention state readout equals the pairwise exponentially-decayed
relative-position attention sum `∑ j ≤ n, (attentionScore q (decayFlow γ (tₙ - tⱼ) *ᵥ kⱼ)) • vⱼ`. -/
theorem linearAttentionReadout_eq_pairwise_sum {d dv : ℕ} (γ : ℝ) (times : ℕ → ℝ)
    (keys : ℕ → Fin d → ℝ) (vals : ℕ → Fin dv → ℝ) (n : ℕ) (q : Fin d → ℝ) :
    (linearAttentionState γ times keys vals n) *ᵥ q =
      ∑ j ∈ Finset.range (n + 1),
        (attentionScore q ((decayFlow (d := d) γ).eval (times n - times j) *ᵥ keys j)) • vals j := by
  rw [linearAttentionState_eq_sum, sum_matrix_mulVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mulVec]
  funext a
  have houter : (Matrix.vecMulVec (vals j) (keys j) *ᵥ q) a =
      attentionScore q (keys j) * vals j a := by
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, attentionScore]
    calc
      (∑ b : Fin d, vals j a * keys j b * q b)
          = ∑ b : Fin d, vals j a * (q b * keys j b) := by
            refine Finset.sum_congr rfl fun b _ => ?_; ring
      _ = vals j a * ∑ b : Fin d, q b * keys j b := by rw [← Finset.mul_sum]
      _ = (∑ b : Fin d, q b * keys j b) * vals j a := mul_comm _ _
  have hscore :
      attentionScore q ((decayFlow (d := d) γ).eval (times n - times j) *ᵥ keys j) =
        Real.exp (-γ * (times n - times j)) * attentionScore q (keys j) := by
    have hmul : (decayFlow (d := d) γ).eval (times n - times j) *ᵥ keys j =
        Real.exp (-γ * (times n - times j)) • keys j := by
      change (Real.exp (-γ * (times n - times j)) • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ keys j = _
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hmul]
    unfold attentionScore
    rw [dotProduct_smul, smul_eq_mul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [houter, hscore]
  ring

end LinearAttentionDecay

/-! ## 4. Multi-dimensional translation groups `(ℝ^d, +)`, 2D image RoPE, and cross-lane bridges -/

section MultiDimTranslation

/-- Multi-dimensional `(ℝ^d, +)` normalized translation-covariant positional modifiers. -/
structure MultiDimTranslationCovariantModifiers (d : Type u) (A : Type v) [Monoid A] where
  queryFactor : (d → ℝ) → Units A
  keyFactor : (d → ℝ) → Units A
  shift_invariant : ∀ t s r, queryFactor (t + r) * keyFactor (s + r) = queryFactor t * keyFactor s
  normalized : ∀ t, queryFactor t * keyFactor t = 1

namespace MultiDimTranslationCovariantModifiers

variable {d : Type u} {A : Type v} [Monoid A]

theorem keyFactor_eq_inv_queryFactor
    (M : MultiDimTranslationCovariantModifiers d A) (t : d → ℝ) :
    M.keyFactor t = (M.queryFactor t)⁻¹ := by
  calc
    M.keyFactor t = 1 * M.keyFactor t := by simp
    _ = ((M.queryFactor t)⁻¹ * M.queryFactor t) * M.keyFactor t := by simp
    _ = (M.queryFactor t)⁻¹ * (M.queryFactor t * M.keyFactor t) := by rw [mul_assoc]
    _ = (M.queryFactor t)⁻¹ * 1 := by rw [M.normalized t]
    _ = (M.queryFactor t)⁻¹ := by simp

@[simp]
theorem keyFactor_mul_queryFactor
    (M : MultiDimTranslationCovariantModifiers d A) (t : d → ℝ) :
    M.keyFactor t * M.queryFactor t = 1 := by
  rw [M.keyFactor_eq_inv_queryFactor]
  simp

/-- Relative transport from origin `0 : d → ℝ` to position `t : d → ℝ`. -/
def relativeUnit (M : MultiDimTranslationCovariantModifiers d A) (t : d → ℝ) : Units A :=
  M.queryFactor t * M.keyFactor 0

/-- Relative transport coerced into the ambient monoid `A`. -/
def relativeModifier (M : MultiDimTranslationCovariantModifiers d A) (t : d → ℝ) : A :=
  M.relativeUnit t

@[simp]
theorem relativeUnit_zero (M : MultiDimTranslationCovariantModifiers d A) :
    M.relativeUnit 0 = 1 := by
  exact M.normalized 0

theorem relativeUnit_add
    (M : MultiDimTranslationCovariantModifiers d A) (s t : d → ℝ) :
    M.relativeUnit (s + t) = M.relativeUnit s * M.relativeUnit t := by
  have hshift :
      M.queryFactor (s + t) * M.keyFactor t = M.queryFactor s * M.keyFactor 0 := by
    simpa using M.shift_invariant s 0 t
  calc
    M.relativeUnit (s + t) =
        M.queryFactor (s + t) * ((M.keyFactor t * M.queryFactor t) * M.keyFactor 0) := by
      simp [relativeUnit]
    _ = (M.queryFactor (s + t) * M.keyFactor t) * (M.queryFactor t * M.keyFactor 0) := by
      simp only [mul_assoc]
    _ = (M.queryFactor s * M.keyFactor 0) * (M.queryFactor t * M.keyFactor 0) := by
      rw [hshift]
    _ = M.relativeUnit s * M.relativeUnit t := rfl

theorem relativeModifier_add
    (M : MultiDimTranslationCovariantModifiers d A) (s t : d → ℝ) :
    M.relativeModifier (s + t) = M.relativeModifier s * M.relativeModifier t := by
  dsimp [relativeModifier]
  rw [M.relativeUnit_add s t, Units.val_mul]

/-- Abelian translation symmetry `(ℝ^d, +)` forces all relative operators to commute. -/
theorem relativeUnit_comm
    (M : MultiDimTranslationCovariantModifiers d A) (u v : d → ℝ) :
    Commute (M.relativeUnit u) (M.relativeUnit v) := by
  change M.relativeUnit u * M.relativeUnit v = M.relativeUnit v * M.relativeUnit u
  rw [← M.relativeUnit_add u v, ← M.relativeUnit_add v u, add_comm u v]

theorem relativeModifier_comm
    (M : MultiDimTranslationCovariantModifiers d A) (u v : d → ℝ) :
    Commute (M.relativeModifier u) (M.relativeModifier v) := by
  dsimp [relativeModifier]
  exact (M.relativeUnit_comm u v).map (Units.coeHom A)

theorem factorization_eq_relativeUnit
    (M : MultiDimTranslationCovariantModifiers d A) (t s : d → ℝ) :
    M.queryFactor t * M.keyFactor s = M.relativeUnit (t - s) := by
  have hshift := M.shift_invariant t s (-s)
  simpa [relativeUnit, sub_eq_add_neg] using hshift.symm

/-- 1D coordinate-axis flow along axis `i : d`. -/
def axisFlow [DecidableEq d]
    (M : MultiDimTranslationCovariantModifiers d A) (i : d) :
    RealOneParameterFlow A where
  flowHom :=
    { toFun := fun t => M.relativeUnit (Pi.single i (toAdd t))
      map_one' := by simp
      map_mul' := fun s t => by
        change M.relativeUnit (Pi.single i (toAdd s + toAdd t)) =
          M.relativeUnit (Pi.single i (toAdd s)) * M.relativeUnit (Pi.single i (toAdd t))
        rw [Pi.single_add, M.relativeUnit_add] }

@[simp]
theorem axisFlow_eval [DecidableEq d]
    (M : MultiDimTranslationCovariantModifiers d A) (i : d) (t : ℝ) :
    (M.axisFlow i).eval t = M.relativeModifier (Pi.single i t) := rfl

end MultiDimTranslationCovariantModifiers

section MultiDimBanachGenerators

open InfoGeometry.Canonical.MeanValueInvariant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "EndE" => E →L[ℝ] E

/-- Differentiable multi-dimensional `(ℝ^d, +)` translation-covariant modifiers have
pairwise commuting infinitesimal generators `L i` and factor globally as
`M.relativeModifier x = NormedSpace.exp (∑ i, x i • L i)`. -/
theorem multiDim_generators_commute_and_exp
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MultiDimTranslationCovariantModifiers d EndE)
    (L : d → EndE)
    (hzero : ∀ i : d, HasDerivAt (M.axisFlow i).eval (L i) 0) :
    (∀ i j : d, Commute (L i) (L j)) ∧
      (∀ x : d → ℝ, M.relativeModifier x = NormedSpace.exp (∑ i : d, x i • L i)) := by
  have haxis : ∀ i : d, ∀ t : ℝ, M.relativeModifier (Pi.single i t) = flow (L i) t := by
    intro i t
    change (M.axisFlow i).eval t = flow (L i) t
    exact eval_eq_exponential_of_hasDerivAt_zero (M.axisFlow i) (L i) (hzero i) t
  have hflow_comm : ∀ i j : d, ∀ s t : ℝ,
      flow (L i) s * flow (L j) t = flow (L j) t * flow (L i) s := by
    intro i j s t
    rw [← haxis i s, ← haxis j t]
    exact M.relativeModifier_comm (Pi.single i s) (Pi.single j t)
  have hcomm_L : ∀ i j : d, Commute (L i) (L j) := by
    intro i j
    have hLflow : ∀ t : ℝ, L i * flow (L j) t = flow (L j) t * L i := by
      intro t
      have hsL : HasDerivAt (fun s : ℝ => flow (L i) s * flow (L j) t)
          ((L i * flow (L i) 0) * flow (L j) t) 0 :=
        (hasStrictDerivAt_flow_left (L i) 0).hasDerivAt.mul_const (flow (L j) t)
      have hsR : HasDerivAt (fun s : ℝ => flow (L j) t * flow (L i) s)
          (flow (L j) t * (L i * flow (L i) 0)) 0 :=
        (hasStrictDerivAt_flow_left (L i) 0).hasDerivAt.const_mul (flow (L j) t)
      have hsL' : HasDerivAt (fun s : ℝ => flow (L i) s * flow (L j) t)
          (flow (L j) t * (L i * flow (L i) 0)) 0 := by
        simpa only [funext (fun s => hflow_comm i j s t)] using hsR
      have heq := hsL.unique hsL'
      simpa [flow_zero] using heq
    have htL : HasDerivAt (fun t : ℝ => L i * flow (L j) t)
        (L i * (L j * flow (L j) 0)) 0 :=
      (hasStrictDerivAt_flow_left (L j) 0).hasDerivAt.const_mul (L i)
    have htR : HasDerivAt (fun t : ℝ => flow (L j) t * L i)
        ((L j * flow (L j) 0) * L i) 0 :=
      (hasStrictDerivAt_flow_left (L j) 0).hasDerivAt.mul_const (L i)
    have htL' : HasDerivAt (fun t : ℝ => L i * flow (L j) t)
        ((L j * flow (L j) 0) * L i) 0 := by
      simpa only [funext hLflow] using htR
    have heq := htL.unique htL'
    exact (by simpa [flow_zero] using heq : L i * L j = L j * L i)
  refine ⟨hcomm_L, ?_⟩
  intro x
  letI : NormedAlgebra ℚ EndE := NormedAlgebra.restrictScalars ℚ ℝ EndE
  have hsum : ∀ s : Finset d,
      M.relativeModifier (∑ i ∈ s, Pi.single i (x i)) =
        NormedSpace.exp (∑ i ∈ s, x i • L i) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
        simp [MultiDimTranslationCovariantModifiers.relativeModifier]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha,
          M.relativeModifier_add, haxis a (x a), ih]
        change flow (L a) (x a) * NormedSpace.exp (∑ i ∈ s, x i • L i) =
          NormedSpace.exp (x a • L a + ∑ i ∈ s, x i • L i)
        have hcomm_sum : Commute (x a • L a) (∑ i ∈ s, x i • L i) := by
          refine Commute.sum_right _ _ _ fun i _ => ?_
          exact ((hcomm_L a i).smul_left (x a)).smul_right (x i)
        change NormedSpace.exp (x a • L a) * NormedSpace.exp (∑ i ∈ s, x i • L i) = _
        exact (NormedSpace.exp_add_of_commute hcomm_sum).symm
  have hdecomp : (∑ i : d, Pi.single i (x i)) = x := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hfin := hsum Finset.univ
  rw [hdecomp] at hfin
  exact hfin

end MultiDimBanachGenerators

section ImageRoPE2D

/-- Block-diagonal exponential for two blocks via `Matrix.fromBlocks`. -/
theorem exp_fromBlocks_zero {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
  have hpow : ∀ k : ℕ, (Matrix.fromBlocks A 0 0 D) ^ k =
      Matrix.fromBlocks (A ^ k) 0 0 (D ^ k) := by
    intro k
    induction k with
    | zero =>
        simp [Matrix.fromBlocks_one]
    | succ k ih =>
        rw [pow_succ, ih, Matrix.fromBlocks_multiply, pow_succ, pow_succ]
        simp
  have hcontL : Continuous (fun X : Matrix m m ℝ =>
      Matrix.fromBlocks X (0 : Matrix m n ℝ) (0 : Matrix n m ℝ) (0 : Matrix n n ℝ)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks]
    · exact ((continuous_apply j).comp (continuous_apply i))
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  have hcontR : Continuous (fun Y : Matrix n n ℝ =>
      Matrix.fromBlocks (0 : Matrix m m ℝ) (0 : Matrix m n ℝ) (0 : Matrix n m ℝ) Y) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks]
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact ((continuous_apply j).comp (continuous_apply i))
  have hsumA : HasSum (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • A ^ k) (NormedSpace.exp A) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_series_hasSum_exp' A
  have hsumD : HasSum (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • D ^ k) (NormedSpace.exp D) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_series_hasSum_exp' D
  let homL : Matrix m m ℝ →+ Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    { toFun := fun X => Matrix.fromBlocks X 0 0 0
      map_zero' := by simp
      map_add' := fun X₁ X₂ => by simp [Matrix.fromBlocks_add] }
  let homR : Matrix n n ℝ →+ Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    { toFun := fun Y => Matrix.fromBlocks 0 0 0 Y
      map_zero' := by simp
      map_add' := fun Y₁ Y₂ => by simp [Matrix.fromBlocks_add] }
  have hsumL : HasSum (fun k : ℕ => Matrix.fromBlocks (((k.factorial : ℚ)⁻¹) • A ^ k) 0 0 0)
      (Matrix.fromBlocks (NormedSpace.exp A) 0 0 0) :=
    hsumA.map homL hcontL
  have hsumR : HasSum (fun k : ℕ => Matrix.fromBlocks 0 0 0 (((k.factorial : ℚ)⁻¹) • D ^ k))
      (Matrix.fromBlocks 0 0 0 (NormedSpace.exp D)) :=
    hsumD.map homR hcontR
  have hsumM : HasSum (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • (Matrix.fromBlocks A 0 0 D) ^ k)
      (Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D)) := by
    have hadd := hsumL.add hsumR
    have htarget :
        Matrix.fromBlocks (NormedSpace.exp A) 0 0 0 +
          Matrix.fromBlocks 0 0 0 (NormedSpace.exp D) =
        Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
      simp [Matrix.fromBlocks_add]
    rw [htarget] at hadd
    refine hadd.congr_fun fun k => ?_
    rw [hpow k, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  have hsumExp : HasSum (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • (Matrix.fromBlocks A 0 0 D) ^ k)
      (NormedSpace.exp (Matrix.fromBlocks A 0 0 D)) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (Matrix.fromBlocks A 0 0 D)
  exact (hsumM.unique hsumExp).symm

/-- Horizontal (`x`-axis) generator for 2D image RoPE on `ℝ² ⊕ ℝ²`. -/
def rope2DGeneratorX (θx : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (θx • rotGen2) 0 0 0

/-- Vertical (`y`-axis) generator for 2D image RoPE on `ℝ² ⊕ ℝ²`. -/
def rope2DGeneratorY (θy : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks 0 0 0 (θy • rotGen2)

/-- The `x` and `y` generators of 2D image RoPE strictly commute. -/
theorem rope2D_generators_commute (θx θy : ℝ) :
    Commute (rope2DGeneratorX θx) (rope2DGeneratorY θy) := by
  change rope2DGeneratorX θx * rope2DGeneratorY θy =
    rope2DGeneratorY θy * rope2DGeneratorX θx
  simp only [rope2DGeneratorX, rope2DGeneratorY, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- Explicit 2D image RoPE operator `rot2 (tx * θx) ⊕ rot2 (ty * θy)`. -/
def rope2DMat (θx θy tx ty : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (rot2 (tx * θx)) 0 0 (rot2 (ty * θy))

theorem rope2DMat_zero (θx θy : ℝ) :
    rope2DMat θx θy 0 0 = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) := by
  simp [rope2DMat, rot2_zero, Matrix.fromBlocks_one]

theorem rope2DMat_mul (θx θy tx ty sx sy : ℝ) :
    rope2DMat θx θy tx ty * rope2DMat θx θy sx sy =
      rope2DMat θx θy (tx + sx) (ty + sy) := by
  simp only [rope2DMat, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, ← rot2_add, ← add_mul]

/-- Constructive `MultiDimTranslationCovariantModifiers` witness realized by 2D image RoPE. -/
def rope2DModifiers (θx θy : ℝ) :
    MultiDimTranslationCovariantModifiers (Fin 2)
      (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) where
  queryFactor p :=
    { val := rope2DMat θx θy (p 0) (p 1)
      inv := rope2DMat θx θy (-p 0) (-p 1)
      val_inv := by rw [rope2DMat_mul, add_neg_cancel, add_neg_cancel, rope2DMat_zero]
      inv_val := by rw [rope2DMat_mul, neg_add_cancel, neg_add_cancel, rope2DMat_zero] }
  keyFactor p :=
    { val := rope2DMat θx θy (-p 0) (-p 1)
      inv := rope2DMat θx θy (p 0) (p 1)
      val_inv := by rw [rope2DMat_mul, neg_add_cancel, neg_add_cancel, rope2DMat_zero]
      inv_val := by rw [rope2DMat_mul, add_neg_cancel, add_neg_cancel, rope2DMat_zero] }
  shift_invariant t s r := by
    apply Units.ext
    simp only [Units.val_mul, Pi.add_apply, rope2DMat_mul]
    congr 1 <;> abel
  normalized t := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, rope2DMat_mul, add_neg_cancel, rope2DMat_zero]

/-- Closed constructive unit-frequency inhabitant of `MultiDimTranslationCovariantModifiers`. -/
def unitFreqRope2DModifiers :
    MultiDimTranslationCovariantModifiers (Fin 2) (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) :=
  rope2DModifiers 1 1

theorem rope2D_exp_eq_block (θx θy tx ty : ℝ) :
    NormedSpace.exp (tx • rope2DGeneratorX θx + ty • rope2DGeneratorY θy) =
      rope2DMat θx θy tx ty := by
  have hsum : tx • rope2DGeneratorX θx + ty • rope2DGeneratorY θy =
      Matrix.fromBlocks ((tx * θx) • rotGen2) 0 0 ((ty * θy) • rotGen2) := by
    simp [rope2DGeneratorX, rope2DGeneratorY, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
      smul_smul]
  rw [hsum, exp_fromBlocks_zero, exp_smul_rotGen2, exp_smul_rotGen2]
  rfl

/-- 2D image RoPE attention score depends strictly on the relative 2D displacement `(sx - tx, sy - ty)`. -/
theorem rope2D_relative_attentionScore (θx θy tx ty sx sy : ℝ)
    (q k : Fin 2 ⊕ Fin 2 → ℝ) :
    attentionScore
        ((rope2DMat θx θy tx ty) *ᵥ q)
        ((rope2DMat θx θy sx sy) *ᵥ k) =
      attentionScore q
        ((rope2DMat θx θy (sx - tx) (sy - ty)) *ᵥ k) := by
  rw [transformed_attentionScore_eq_relative]
  have hT : (rope2DMat θx θy tx ty)ᵀ =
      Matrix.fromBlocks (rot2 (-(tx * θx))) 0 0 (rot2 (-(ty * θy))) := by
    simp only [rope2DMat, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      rot2_transpose]
  rw [hT, rope2DMat, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [← rot2_add, ← rot2_add]
  have hx : -(tx * θx) + sx * θx = (sx - tx) * θx := by
    rw [sub_mul, ← neg_add_eq_sub]
  have hy : -(ty * θy) + sy * θy = (sy - ty) * θy := by
    rw [sub_mul, ← neg_add_eq_sub]
  rw [hx, hy]
  rfl

end ImageRoPE2D

section CrossLaneBridges

open InfoGeometry.Clifford.Cl55RoPEAttentionPairing
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.DrazinInfiniteCore

/-- Explicit `Cl55RoPEAttentionPairing.InvariantRotorPairing` witness realized by planar `rot2`. -/
def rot2InvariantRotorPairing (ω : ℝ) : InvariantRotorPairing (Fin 2 → ℝ) where
  R θ := Matrix.toLin' (rot2 (ω * θ))
  R_zero := by
    rw [mul_zero, rot2_zero, Matrix.toLin'_one]
  R_add s t := by
    rw [mul_add, rot2_add, Matrix.toLin'_mul]
  inner u v := dotProduct u v
  inner_inv θ u v := by
    change dotProduct (rot2 (ω * θ) *ᵥ u) (rot2 (ω * θ) *ᵥ v) = dotProduct u v
    rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      rot2_transpose, ← rot2_add, neg_add_cancel, rot2_zero, Matrix.vecMul_one]

/-- Any `k × k` nilpotent Jordan shift admits `0` as its Drazin inverse with index `k`. -/
theorem jordanShift_isDrazinInverse_zero (k : ℕ) :
    IsDrazinInverse (jordanShift k) 0 k :=
  IsDrazinInverse.mk (by simp) (by simp) (by rw [mul_zero, jordanShift_pow_self_eq_zero])

private theorem toCLM_jordanShift_pow (k m : ℕ) (x : Fin k → ℝ) :
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' (jordanShift k)) ^ m) x) =
      ((jordanShift k) ^ m) *ᵥ x := by
  induction m generalizing x with
  | zero => simp [pow_zero]
  | succ m ih =>
      rw [pow_succ', pow_succ']
      change (Matrix.toLin' (jordanShift k))
          ((LinearMap.toContinuousLinearMap (Matrix.toLin' (jordanShift k)) ^ m) x) = _
      rw [ih, Matrix.toLin'_apply, Matrix.mulVec_mulVec]

/-- On `Fin k → ℝ`, the continuous linear map induced by `jordanShift k` satisfies the
repo's infinite/constructive Riesz decomposition theorem with vanishing spectral projector
and nilpotent defect index `k`. -/
def jordanShift_constructiveRieszDecompositionAtZero (k : ℕ) :
    ConstructiveRieszDecompositionAtZero (𝕂 := ℝ)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (jordanShift k))) :=
  constructiveRieszDecompositionAtZero_of_nilpotent k (by
    ext x
    rw [toCLM_jordanShift_pow, jordanShift_pow_self_eq_zero, Matrix.zero_mulVec]
    rfl)

end CrossLaneBridges

end MultiDimTranslation

end InfoGeometry.LLM.PositionalEncodingClassification

end noncomputable section
