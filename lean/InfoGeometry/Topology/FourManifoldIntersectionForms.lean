/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Integral Unimodular 4-Manifold Intersection Forms, Van der Blij, Thom Genus & Elkies

This module formalizes the integral unimodular symmetric bilinear form arithmetic,
characteristic-vector congruences, signature and virtual-dimension algebra, Kronheimer–Mrowka
blow-up adjunction and Thom genus lower-bound arithmetic, constructive finite-lattice Elkies
invariant `Θ(q)`, and Kähler vortex degree bounds from Nicolaescu (*Notes on Seiberg–Witten
Theory*, Chapters 2–3).

## Formalized Results

1. **Integral Unimodular Symmetric Bilinear Forms (`IntegralUnimodularForm n`)**:
   * Pairing `pair`, quadratic evaluation `eval`, direct sum `oplus`, negation `neg`,
     `GL(n, ℤ)` congruence `IsIso`, evenness `IsEven`, and characteristic vectors
     `IsCharacteristic` (`q.pair w y ≡ q.eval y [ZMOD 2]`).
   * Concrete models: `diagPos1` (`⟨1⟩`), `diagNeg1` (`⟨-1⟩`), `diagonalUnimodular`,
     hyperbolic plane `hyperbolicH`, and the positive-definite even unimodular lattice
     `e8Form` (verified via explicit `LDLᵀ` factorization over `ℚ` and `ℤ`-quadratic
     sum-of-squares completion).
   * Unconditional characteristic-vector existence (`exists_characteristic`, via invertibility
     of `det q.mat` over `ZMod 2`) and universal mod-8 invariance (`characteristic_eval_mod8_eq`).
2. **Signature `τ(q)` & Van der Blij Arithmetic (Prop. 2.4.15)**:
   * Signature `signature q := (_root_.sigPos q.toRealQuadForm : ℤ) - (_root_.sigNeg q.toRealQuadForm : ℤ)`
     grounded in Mathlib's `sigPos` / `sigNeg` and Sylvester's law of inertia.
   * Van der Blij congruence `q.eval w ≡ signature q [ZMOD 8]` proved for all diagonal forms
     `⟨±1⟩^n`, `hyperbolicH`, `e8Form`, negation, direct sums, `ℤ`-isometries, stabilizations,
     and all standard 4-manifold forms `a•E₈ ⊕ b•H ⊕ c•⟨1⟩ ⊕ d•⟨-1⟩`.
3. **Virtual Dimension & Kronheimer–Mrowka Thom Genus (Lemma 2.2.10, Thm. 2.4.9)**:
   * Integrality and parity of `virtualDim c1_sq chi tau = (c1_sq - 2 * chi - 3 * tau) / 4`,
     and `d(σ) ≡ -(b₀ - b₁ + b₂⁺) [ZMOD 2]`.
   * Adjunction identity `2 * thomGenus d - 2 = (-3) * d + d * d` for
     `thomGenus d = 1 + d * (d - 3) / 2`, blow-up intersection arithmetic on
     `ℂℙ² # d² \overline{ℂℙ²}` (`Σ̃² = 0`, `-K_M ⋅ Σ̃ = d(3 - d)`), and the monopole genus bound
     `thomGenus d ≤ g` (`d > 3`).
4. **Constructive Elkies Finite-Lattice Invariant `Θ(q)` (Thm. 2.4.16)**:
   * Finite characteristic-vector maximization via
     `Matrix.PosDef.finite_setOfPred_dotProduct_mulVec_le`, proving `Θ(q) ≤ n`,
     `Θ(q) = n ↔ q.IsEven`, `8 ∣ Θ(q)` under Van der Blij, `Θ(⟨-1⟩^n) = 0`,
     `Θ(-E₈) = 8 > 0`, and `Θ(q) ≥ 0` on diagonal and even definite lattices.
5. **Kähler Vortex Degree Bound (Prop. 3.2.6)**:
   * Chamber-forcing and degree bound `0 ≤ deg_ω L ≤ deg_ω K_M`.

## Long-Term Mathlib Frontiers

The following analytic, PDE, and classification-theoretic results from Nicolaescu (Ch. 1.2,
1.5, 2.2–2.3, 3.2–3.3, 4) lie beyond current Mathlib smooth 4-manifold and modular-form
infrastructure and are intentionally excluded rather than postulated as axioms:
* Smooth 4-manifold `Spinᶜ` Sobolev spaces, Kuranishi models, and Sard–Smale Fredholm
  transversality for Seiberg–Witten moduli spaces.
* Donaldson's diagonalization theorem (Theorem 2.4.18) and Rohlin's `τ ≡ 0 (mod 16)` theorem.
* General Milnor Gauss-sum / Serre classification proof of Van der Blij for arbitrary
  unclassified definite lattices of rank ≥ 12, and Elkies' modular-form `θ`-series proof of
  `Θ(q) ≥ 0` for arbitrary non-diagonal odd definite lattices.
* Kazdan–Warner PDEs on Kähler surfaces, Taubes' `SW = Gr` symplectic theorem, and
  Cappell–Lee–Miller neck-stretching gluing.
-/

set_option autoImplicit false

namespace InfoGeometry.Topology.FourManifoldIntersectionForms

open Matrix QuadraticForm

/-- The Cartan matrix of `E₈` (chain `0-1-2-3-4-5-6` with branch `4-7`), positive-definite,
even, symmetric, and unimodular (`det = 1`). -/
def e8Matrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0,  0,  0,  0;
      0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0, -1;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2,  0;
      0,  0,  0,  0, -1,  0,  0,  2]

private def e8LowerQ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![ 1,    0,    0,    0,    0,    0,    0, 0;
     -1/2,  1,    0,    0,    0,    0,    0, 0;
      0,   -2/3,  1,    0,    0,    0,    0, 0;
      0,    0,   -3/4,  1,    0,    0,    0, 0;
      0,    0,    0,   -4/5,  1,    0,    0, 0;
      0,    0,    0,    0,   -5/6,  1,    0, 0;
      0,    0,    0,    0,    0,   -6/7,  1, 0;
      0,    0,    0,    0,   -5/6, -5/7, -5/8, 1]

private def e8DiagQ : Fin 8 → ℚ := ![2, 3/2, 4/3, 5/4, 6/5, 7/6, 8/7, 1/8]

private def e8LDQ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![ 2,    0,    0,    0,    0,    0,    0,    0;
     -1,  3/2,    0,    0,    0,    0,    0,    0;
      0,   -1,  4/3,    0,    0,    0,    0,    0;
      0,    0,   -1,  5/4,    0,    0,    0,    0;
      0,    0,    0,   -1,  6/5,    0,    0,    0;
      0,    0,    0,    0,   -1,  7/6,    0,    0;
      0,    0,    0,    0,    0,   -1,  8/7,    0;
      0,    0,    0,    0,   -1, -5/6, -5/7,  1/8]

noncomputable section

/-!
## Section 1: Non-Commutativity Witnesses (`T16`) & Integral Unimodular Forms
-/

section NonCommutativityWitnesses

/-- Closed `T16` non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℤ`. -/
theorem int_mat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num at h00

/-- Closed `T16` non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℤ`. -/
theorem int_mat8_noncomm_witness :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℤ, A * B ≠ B * A := by
  let E01 : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let E10 : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [E01, E10, Matrix.mul_apply] at h00

/-- Closed `T16` non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℚ`. -/
theorem rat_mat8_noncomm_witness :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℚ, A * B ≠ B * A := by
  let E01 : Matrix (Fin 8) (Fin 8) ℚ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let E10 : Matrix (Fin 8) (Fin 8) ℚ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [E01, E10, Matrix.mul_apply] at h00

/-- Closed `T16` non-commutativity witness for `Matrix (Fin n) (Fin n) ℤ` when `2 ≤ n`. -/
theorem int_matN_noncomm_witness (n : ℕ) (hn : 2 ≤ n) :
    ∃ A B : Matrix (Fin n) (Fin n) ℤ, A * B ≠ B * A := by
  let i0 : Fin n := ⟨0, lt_of_lt_of_le (by omega) hn⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le (by omega) hn⟩
  have hne : i0 ≠ i1 := by
    intro h
    have hv : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
    simp [i0, i1] at hv
  let E01 : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => if i = i0 ∧ j = i1 then 1 else 0
  let E10 : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => if i = i1 ∧ j = i0 then 1 else 0
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h i0) i0
  simp [E01, E10, Matrix.mul_apply, hne] at h00

end NonCommutativityWitnesses

section IntegralForms

/-- An integral unimodular symmetric bilinear form of rank `n` over `ℤ`, representing the
intersection form `Q_M : H²(M; ℤ) × H²(M; ℤ) → ℤ` of a closed oriented 4-manifold. -/
@[ext]
structure IntegralUnimodularForm (n : ℕ) where
  /-- Gram matrix with respect to a chosen `ℤ`-basis. -/
  mat : Matrix (Fin n) (Fin n) ℤ
  /-- Symmetry of the intersection pairing. -/
  isSymm : mat.IsSymm
  /-- Unimodularity over `ℤ`: `det mat = ±1`. -/
  det_abs_one : mat.det = 1 ∨ mat.det = -1

namespace IntegralUnimodularForm

/-- Bilinear pairing `q(x, y) = x ⬝ᵥ (q.mat *ᵥ y)`. -/
def pair {n : ℕ} (q : IntegralUnimodularForm n) (x y : Fin n → ℤ) : ℤ :=
  x ⬝ᵥ (q.mat *ᵥ y)

/-- Associated integral quadratic form `q(x) = q(x, x)`. -/
def eval {n : ℕ} (q : IntegralUnimodularForm n) (x : Fin n → ℤ) : ℤ :=
  q.pair x x

theorem pair_symm {n : ℕ} (q : IntegralUnimodularForm n) (x y : Fin n → ℤ) :
    q.pair x y = q.pair y x := by
  unfold pair
  rw [dotProduct_mulVec, ← vecMul_transpose, q.isSymm.eq, dotProduct_comm]

theorem pair_add_left {n : ℕ} (q : IntegralUnimodularForm n) (x₁ x₂ y : Fin n → ℤ) :
    q.pair (x₁ + x₂) y = q.pair x₁ y + q.pair x₂ y := by
  simp [pair, add_dotProduct]

theorem pair_add_right {n : ℕ} (q : IntegralUnimodularForm n) (x y₁ y₂ : Fin n → ℤ) :
    q.pair x (y₁ + y₂) = q.pair x y₁ + q.pair x y₂ := by
  simp [pair, mulVec_add, dotProduct_add]

theorem pair_smul_left {n : ℕ} (q : IntegralUnimodularForm n) (c : ℤ) (x y : Fin n → ℤ) :
    q.pair (c • x) y = c * q.pair x y := by
  simp [pair, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem pair_smul_right {n : ℕ} (q : IntegralUnimodularForm n) (c : ℤ) (x y : Fin n → ℤ) :
    q.pair x (c • y) = c * q.pair x y := by
  simp only [pair, dotProduct, mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => by ring

@[simp]
theorem eval_zero {n : ℕ} (q : IntegralUnimodularForm n) : q.eval 0 = 0 := by
  simp [eval, pair]

theorem eval_neg {n : ℕ} (q : IntegralUnimodularForm n) (x : Fin n → ℤ) :
    q.eval (-x) = q.eval x := by
  simp [eval, pair, mulVec_neg]

theorem eval_add {n : ℕ} (q : IntegralUnimodularForm n) (x y : Fin n → ℤ) :
    q.eval (x + y) = q.eval x + 2 * q.pair x y + q.eval y := by
  unfold eval
  rw [pair_add_left, pair_add_right, pair_add_right, q.pair_symm y x]
  ring

theorem eval_sub {n : ℕ} (q : IntegralUnimodularForm n) (x y : Fin n → ℤ) :
    q.eval (x - y) = q.eval x - 2 * q.pair x y + q.eval y := by
  rw [sub_eq_add_neg, eval_add, eval_neg, ← neg_one_smul ℤ y, pair_smul_right]
  ring

theorem eval_smul {n : ℕ} (q : IntegralUnimodularForm n) (c : ℤ) (x : Fin n → ℤ) :
    q.eval (c • x) = c ^ 2 * q.eval x := by
  unfold eval
  rw [pair_smul_left, pair_smul_right]
  ring

theorem pair_basis {n : ℕ} (q : IntegralUnimodularForm n) (i j : Fin n) :
    q.pair (Pi.single i 1) (Pi.single j 1) = q.mat i j := by
  simp [pair, dotProduct, mulVec, Pi.single_apply]

theorem eval_basis {n : ℕ} (q : IntegralUnimodularForm n) (i : Fin n) :
    q.eval (Pi.single i 1) = q.mat i i :=
  q.pair_basis i i

theorem det_ne_zero {n : ℕ} (q : IntegralUnimodularForm n) : q.mat.det ≠ 0 := by
  rcases q.det_abs_one with h | h <;> omega

theorem isUnit_det {n : ℕ} (q : IntegralUnimodularForm n) : IsUnit q.mat.det := by
  rcases q.det_abs_one with h | h
  · rw [h]; exact isUnit_one
  · rw [h]; exact isUnit_one.neg

/-- Orthogonal direct sum `q₁ ⊕ q₂` of integral unimodular forms. -/
def oplus {n₁ n₂ : ℕ} (q₁ : IntegralUnimodularForm n₁) (q₂ : IntegralUnimodularForm n₂) :
    IntegralUnimodularForm (n₁ + n₂) where
  mat := (Matrix.fromBlocks q₁.mat 0 0 q₂.mat).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with i₁ | i₂ <;>
      rcases finSumFinEquiv.symm j with j₁ | j₂ <;>
      simp [q₁.isSymm.apply, q₂.isSymm.apply]
  det_abs_one := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    rcases q₁.det_abs_one with h₁ | h₁ <;> rcases q₂.det_abs_one with h₂ | h₂
    · left; rw [h₁, h₂, mul_one]
    · right; rw [h₁, h₂, one_mul]
    · right; rw [h₁, h₂, mul_one]
    · left; rw [h₁, h₂]; norm_num

theorem oplus_pair {n₁ n₂ : ℕ} (q₁ : IntegralUnimodularForm n₁) (q₂ : IntegralUnimodularForm n₂)
    (x y : Fin (n₁ + n₂) → ℤ) :
    (q₁.oplus q₂).pair x y =
      q₁.pair (fun i => x (finSumFinEquiv (Sum.inl i))) (fun i => y (finSumFinEquiv (Sum.inl i))) +
      q₂.pair (fun j => x (finSumFinEquiv (Sum.inr j))) (fun j => y (finSumFinEquiv (Sum.inr j))) := by
  unfold pair oplus
  simp only [dotProduct, mulVec]
  have hsum : ∀ f : Fin (n₁ + n₂) → ℤ,
      ∑ k : Fin (n₁ + n₂), f k =
        (∑ i : Fin n₁, f (finSumFinEquiv (Sum.inl i))) +
        (∑ j : Fin n₂, f (finSumFinEquiv (Sum.inr j))) := by
    intro f
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  rw [hsum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum]
    simp only [Equiv.symm_apply_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsum]
    simp only [Equiv.symm_apply_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem oplus_eval {n₁ n₂ : ℕ} (q₁ : IntegralUnimodularForm n₁) (q₂ : IntegralUnimodularForm n₂)
    (x : Fin (n₁ + n₂) → ℤ) :
    (q₁.oplus q₂).eval x =
      q₁.eval (fun i => x (finSumFinEquiv (Sum.inl i))) +
      q₂.eval (fun j => x (finSumFinEquiv (Sum.inr j))) :=
  oplus_pair q₁ q₂ x x

/-- Negation `-q` (reversing orientation of the 4-manifold). -/
def neg {n : ℕ} (q : IntegralUnimodularForm n) : IntegralUnimodularForm n where
  mat := -q.mat
  isSymm := by
    ext i j
    simp [q.isSymm.apply]
  det_abs_one := by
    rw [Matrix.det_neg]
    rcases q.det_abs_one with h | h <;> rw [h]
    · rcases neg_one_pow_eq_or ℤ n with hp | hp <;> [left; right] <;> simp [hp]
    · rcases neg_one_pow_eq_or ℤ n with hp | hp <;> [right; left] <;> simp [hp]

@[simp]
theorem neg_pair {n : ℕ} (q : IntegralUnimodularForm n) (x y : Fin n → ℤ) :
    q.neg.pair x y = -q.pair x y := by
  simp [neg, pair, Matrix.neg_mulVec, dotProduct_neg]

@[simp]
theorem neg_eval {n : ℕ} (q : IntegralUnimodularForm n) (x : Fin n → ℤ) :
    q.neg.eval x = -q.eval x :=
  q.neg_pair x x

/-- `GL(n, ℤ)`-congruence of integral unimodular forms. -/
def IsIso {n : ℕ} (q₁ q₂ : IntegralUnimodularForm n) : Prop :=
  ∃ T : Matrix (Fin n) (Fin n) ℤ, (T.det = 1 ∨ T.det = -1) ∧ Tᵀ * q₁.mat * T = q₂.mat

theorem isIso_refl {n : ℕ} (q : IntegralUnimodularForm n) : q.IsIso q :=
  ⟨1, Or.inl Matrix.det_one, by simp⟩

theorem isIso_symm {n : ℕ} {q₁ q₂ : IntegralUnimodularForm n} (h : q₁.IsIso q₂) : q₂.IsIso q₁ := by
  rcases h with ⟨T, hdet, hmat⟩
  have hunit : IsUnit T.det := by
    rcases hdet with h1 | h1
    · rw [h1]; exact isUnit_one
    · rw [h1]; exact isUnit_one.neg
  let S : Matrix (Fin n) (Fin n) ℤ := T⁻¹
  have hTS : T * S = 1 := Matrix.mul_nonsing_inv T hunit
  have hST : S * T = 1 := Matrix.nonsing_inv_mul T hunit
  have hdetS : S.det = 1 ∨ S.det = -1 := by
    have hmul : T.det * S.det = 1 := by
      rw [← Matrix.det_mul, hTS, Matrix.det_one]
    rcases hdet with h1 | h1
    · left; rw [h1, one_mul] at hmul; exact hmul
    · right; rw [h1] at hmul; linarith
  refine ⟨S, hdetS, ?_⟩
  have hS_tr : Sᵀ * Tᵀ = 1 := by
    rw [← Matrix.transpose_mul, hTS, Matrix.transpose_one]
  calc
    Sᵀ * q₂.mat * S = Sᵀ * (Tᵀ * q₁.mat * T) * S := by rw [hmat]
    _ = (Sᵀ * Tᵀ) * q₁.mat * (T * S) := by simp only [Matrix.mul_assoc]
    _ = q₁.mat := by rw [hS_tr, hTS, Matrix.one_mul, Matrix.mul_one]

theorem isIso_trans {n : ℕ} {q₁ q₂ q₃ : IntegralUnimodularForm n}
    (h₁₂ : q₁.IsIso q₂) (h₂₃ : q₂.IsIso q₃) : q₁.IsIso q₃ := by
  rcases h₁₂ with ⟨T₁, hdet₁, hmat₁⟩
  rcases h₂₃ with ⟨T₂, hdet₂, hmat₂⟩
  refine ⟨T₁ * T₂, ?_, ?_⟩
  · rw [Matrix.det_mul]
    rcases hdet₁ with h₁ | h₁ <;> rcases hdet₂ with h₂ | h₂
    · left; rw [h₁, h₂, mul_one]
    · right; rw [h₁, h₂, one_mul]
    · right; rw [h₁, h₂, mul_one]
    · left; rw [h₁, h₂]; norm_num
  · rw [Matrix.transpose_mul]
    calc
      (T₂ᵀ * T₁ᵀ) * q₁.mat * (T₁ * T₂)
          = T₂ᵀ * (T₁ᵀ * q₁.mat * T₁) * T₂ := by simp only [Matrix.mul_assoc]
      _ = T₂ᵀ * q₂.mat * T₂ := by rw [hmat₁]
      _ = q₃.mat := hmat₂

theorem isIso_pair {n : ℕ} {q₁ q₂ : IntegralUnimodularForm n} (T : Matrix (Fin n) (Fin n) ℤ)
    (hT : Tᵀ * q₁.mat * T = q₂.mat) (x y : Fin n → ℤ) :
    q₂.pair x y = q₁.pair (T *ᵥ x) (T *ᵥ y) := by
  unfold pair
  rw [← hT]
  calc
    x ⬝ᵥ ((Tᵀ * q₁.mat * T) *ᵥ y)
        = x ⬝ᵥ (Tᵀ *ᵥ (q₁.mat *ᵥ (T *ᵥ y))) := by
          simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = (x ᵥ* Tᵀ) ⬝ᵥ (q₁.mat *ᵥ (T *ᵥ y)) := by rw [← Matrix.dotProduct_mulVec]
    _ = (T *ᵥ x) ⬝ᵥ (q₁.mat *ᵥ (T *ᵥ y)) := by rw [Matrix.vecMul_transpose]

theorem isIso_eval {n : ℕ} {q₁ q₂ : IntegralUnimodularForm n} (T : Matrix (Fin n) (Fin n) ℤ)
    (hT : Tᵀ * q₁.mat * T = q₂.mat) (x : Fin n → ℤ) :
    q₂.eval x = q₁.eval (T *ᵥ x) :=
  isIso_pair T hT x x

theorem eval_eq_diag_add_two_upper {n : ℕ} (q : IntegralUnimodularForm n) (x : Fin n → ℤ) :
    q.eval x = ∑ i : Fin n, x i * x i * q.mat i i +
      2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j := by
  unfold eval pair
  simp only [dotProduct, mulVec, Finset.mul_sum]
  have hsplit : ∀ i : Fin n,
      ∑ j : Fin n, x i * (q.mat i j * x j) =
        x i * x i * q.mat i i +
        ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), x i * q.mat i j * x j := by
    intro i
    have hpart : (Finset.univ : Finset (Fin n)) =
        insert i (Finset.univ.filter (fun j => i < j) ∪
          Finset.univ.filter (fun j => j < i)) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
        true_and, true_iff]
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hdisj₁ : i ∉ Finset.univ.filter (fun j => i < j) ∪
        Finset.univ.filter (fun j => j < i) := by simp
    have hdisj₂ : Disjoint (Finset.univ.filter (fun j => i < j))
        (Finset.univ.filter (fun j => j < i)) := by
      rw [Finset.disjoint_left]
      intro j hj₁ hj₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
      omega
    conv_lhs => rw [hpart, Finset.sum_insert hdisj₁, Finset.sum_union hdisj₂]
    have heq_diag : x i * (q.mat i i * x i) = x i * x i * q.mat i i := by ring
    rw [heq_diag]
    have hc₁ : ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * (q.mat i j * x j) =
        ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j :=
      Finset.sum_congr rfl fun j _ => by ring
    have hc₂ : ∑ j ∈ Finset.univ.filter (fun j => j < i), x i * (q.mat i j * x j) =
        ∑ j ∈ Finset.univ.filter (fun j => j < i), x i * q.mat i j * x j :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [hc₁, hc₂]
    ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hswap :
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < i), x i * q.mat i j * x j =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j := by
    have hs₁ :
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < i), x i * q.mat i j * x j =
          ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.2 < p.1),
            x p.1 * q.mat p.1 p.2 * x p.2 := by
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_filter]
    have hs₂ :
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j =
          ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 < p.2),
            x p.1 * q.mat p.1 p.2 * x p.2 := by
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_filter]
    rw [hs₁, hs₂]
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), by simp [hp], rfl⟩
    · intro p _
      have hsym := q.isSymm.apply p.2 p.1
      rw [hsym]
      ring
  rw [hswap]
  have hdouble :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j) +
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j) =
      2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * q.mat i j * x j := by
    ring
  rw [add_assoc, hdouble]
  simp only [Finset.mul_sum, mul_assoc]

/-- An integral form `q` is even (Type II) if `q(x, x) ∈ 2ℤ` for all `x`. -/
def IsEven {n : ℕ} (q : IntegralUnimodularForm n) : Prop :=
  ∀ x : Fin n → ℤ, Even (q.eval x)

theorem isEven_iff_diag_even {n : ℕ} (q : IntegralUnimodularForm n) :
    q.IsEven ↔ ∀ i : Fin n, Even (q.mat i i) := by
  constructor
  · intro h i
    rw [← q.eval_basis i]
    exact h (Pi.single i 1)
  · intro hdiag x
    rw [q.eval_eq_diag_add_two_upper x]
    refine Even.add ?_ (even_two_mul _)
    refine Finset.even_sum _ fun i _ => ?_
    exact Even.mul_left (hdiag i) _

/-- `w` is a characteristic vector for `q` (representing `c₁(σ)`) if `q(w, y) ≡ q(y, y) [ZMOD 2]`
for all `y`. -/
def IsCharacteristic {n : ℕ} (q : IntegralUnimodularForm n) (w : Fin n → ℤ) : Prop :=
  ∀ y : Fin n → ℤ, q.pair w y ≡ q.eval y [ZMOD 2]

theorem isCharacteristic_iff_mulVec_mod2 {n : ℕ} (q : IntegralUnimodularForm n) (w : Fin n → ℤ) :
    q.IsCharacteristic w ↔ ∀ i : Fin n, (q.mat *ᵥ w) i ≡ q.mat i i [ZMOD 2] := by
  constructor
  · intro hw i
    have hi := hw (Pi.single i 1)
    rw [q.pair_symm, q.eval_basis] at hi
    simpa [pair, dotProduct, Pi.single_apply] using hi
  · intro hdiag y
    rw [Int.modEq_iff_dvd]
    have hp : q.pair w y = ∑ i : Fin n, y i * (q.mat *ᵥ w) i := by
      rw [q.pair_symm]
      simp [pair, dotProduct]
    rw [q.eval_eq_diag_add_two_upper y, hp]
    have hs :
        (∑ i : Fin n, y i * y i * q.mat i i) - ∑ i : Fin n, y i * (q.mat *ᵥ w) i =
          ∑ i : Fin n, (y i * (q.mat i i - (q.mat *ᵥ w) i) + (y i * y i - y i) * q.mat i i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdiff :
        (∑ i : Fin n, y i * y i * q.mat i i +
          2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), y i * q.mat i j * y j) -
            ∑ i : Fin n, y i * (q.mat *ᵥ w) i =
          ∑ i : Fin n, (y i * (q.mat i i - (q.mat *ᵥ w) i) + (y i * y i - y i) * q.mat i i) +
            2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), y i * q.mat i j * y j := by
      linarith [hs]
    rw [hdiff]
    refine dvd_add ?_ (dvd_mul_right 2 _)
    refine Finset.dvd_sum fun i _ => dvd_add ?_ ?_
    · exact dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp (hdiag i)) (y i)
    · have hfact : y i * y i - y i = y i * (y i - 1) := by ring
      rw [hfact]
      rcases Int.even_or_odd (y i) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact dvd_mul_of_dvd_left ⟨k * (y i - 1), by rw [hk]; ring⟩ _
      · exact dvd_mul_of_dvd_left ⟨y i * k, by rw [hk]; ring⟩ _

theorem isCharacteristic_oplus {n₁ n₂ : ℕ} (q₁ : IntegralUnimodularForm n₁)
    (q₂ : IntegralUnimodularForm n₂) (w : Fin (n₁ + n₂) → ℤ) :
    (q₁.oplus q₂).IsCharacteristic w ↔
      q₁.IsCharacteristic (fun i => w (finSumFinEquiv (Sum.inl i))) ∧
      q₂.IsCharacteristic (fun j => w (finSumFinEquiv (Sum.inr j))) := by
  constructor
  · intro hw
    constructor
    · intro y₁
      let y : Fin (n₁ + n₂) → ℤ := fun k =>
        Sum.elim y₁ (fun _ => 0) (finSumFinEquiv.symm k)
      have hy := hw y
      simp only [oplus_pair, oplus_eval, y, Equiv.symm_apply_apply, Sum.elim_inl,
        Sum.elim_inr] at hy
      have h0p : q₂.pair (fun j => w (finSumFinEquiv (Sum.inr j))) 0 = 0 := by
        simp [pair]
      have h0e : q₂.eval 0 = 0 := q₂.eval_zero
      change (q₁.pair (fun i => w (finSumFinEquiv (Sum.inl i))) y₁ +
        q₂.pair (fun j => w (finSumFinEquiv (Sum.inr j))) 0) ≡ q₁.eval y₁ + q₂.eval 0 [ZMOD 2] at hy
      rwa [h0p, h0e, add_zero, add_zero] at hy
    · intro y₂
      let y : Fin (n₁ + n₂) → ℤ := fun k =>
        Sum.elim (fun _ => 0) y₂ (finSumFinEquiv.symm k)
      have hy := hw y
      simp only [oplus_pair, oplus_eval, y, Equiv.symm_apply_apply, Sum.elim_inl,
        Sum.elim_inr] at hy
      have h0p : q₁.pair (fun i => w (finSumFinEquiv (Sum.inl i))) 0 = 0 := by
        simp [pair]
      have h0e : q₁.eval 0 = 0 := q₁.eval_zero
      change (q₁.pair (fun i => w (finSumFinEquiv (Sum.inl i))) 0 +
        q₂.pair (fun j => w (finSumFinEquiv (Sum.inr j))) y₂) ≡ q₁.eval 0 + q₂.eval y₂ [ZMOD 2] at hy
      rwa [h0p, h0e, zero_add, zero_add] at hy
  · rintro ⟨hw₁, hw₂⟩ y
    rw [oplus_pair, oplus_eval]
    exact (hw₁ _).add (hw₂ _)

theorem isCharacteristic_neg_iff {n : ℕ} (q : IntegralUnimodularForm n) (w : Fin n → ℤ) :
    q.neg.IsCharacteristic w ↔ q.IsCharacteristic w := by
  constructor <;> intro hw y <;> simpa [neg_pair, neg_eval] using (hw y).neg

theorem isCharacteristic_isIso {n : ℕ} {q₁ q₂ : IntegralUnimodularForm n}
    (T : Matrix (Fin n) (Fin n) ℤ) (hdet : T.det = 1 ∨ T.det = -1)
    (hT : Tᵀ * q₁.mat * T = q₂.mat) (w : Fin n → ℤ) :
    q₂.IsCharacteristic w ↔ q₁.IsCharacteristic (T *ᵥ w) := by
  have hunit : IsUnit T.det := by
    rcases hdet with h1 | h1
    · rw [h1]; exact isUnit_one
    · rw [h1]; exact isUnit_one.neg
  constructor
  · intro hw y
    have hy := hw (T⁻¹ *ᵥ y)
    rw [isIso_pair T hT, isIso_eval T hT, mulVec_mulVec, Matrix.mul_nonsing_inv T hunit,
      one_mulVec] at hy
    exact hy
  · intro hw y
    rw [isIso_pair T hT, isIso_eval T hT]
    exact hw (T *ᵥ y)

/-- Unconditional existence of a characteristic vector for any rank-`n` integral unimodular form,
constructed by inverting `q.mat` over `ZMod 2`. -/
theorem exists_characteristic {n : ℕ} (q : IntegralUnimodularForm n) :
    ∃ w : Fin n → ℤ, q.IsCharacteristic w := by
  let A2 : Matrix (Fin n) (Fin n) (ZMod 2) := q.mat.map (Int.castRingHom (ZMod 2))
  have hdet2 : A2.det = 1 := by
    have hm : A2.det = ((q.mat.det : ℤ) : ZMod 2) := by
      exact ((Int.castRingHom (ZMod 2)).map_det q.mat).symm
    rw [hm]
    rcases q.det_abs_one with h | h <;> rw [h] <;> decide
  have hunit2 : IsUnit A2.det := by rw [hdet2]; exact isUnit_one
  let b2 : Fin n → ZMod 2 := fun i => (q.mat i i : ZMod 2)
  let w2 : Fin n → ZMod 2 := A2⁻¹ *ᵥ b2
  let w : Fin n → ℤ := fun i => (w2 i).val
  refine ⟨w, (q.isCharacteristic_iff_mulVec_mod2 w).mpr fun i => ?_⟩
  have hcast : ((w2 i).val : ZMod 2) = w2 i := ZMod.natCast_zmod_val (w2 i)
  have hmul : A2 *ᵥ w2 = b2 := by
    rw [show w2 = A2⁻¹ *ᵥ b2 from rfl, mulVec_mulVec, Matrix.mul_nonsing_inv A2 hunit2, one_mulVec]
  have hi2 : (((q.mat *ᵥ w) i : ℤ) : ZMod 2) = ((q.mat i i : ℤ) : ZMod 2) := by
    have h1 : (((q.mat *ᵥ w) i : ℤ) : ZMod 2) = (A2 *ᵥ w2) i := by
      simp only [A2, mulVec, dotProduct, Matrix.map_apply, RingHom.coe_coe, Int.coe_castRingHom,
        Int.cast_sum, Int.cast_mul, w]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [h1, hmul]
  exact (ZMod.intCast_eq_intCast_iff ((q.mat *ᵥ w) i) (q.mat i i) 2).mp hi2

/-- Any two characteristic vectors of `q` differ by an even vector `2 • z`. -/
theorem characteristic_sub_even {n : ℕ} (q : IntegralUnimodularForm n)
    {w₁ w₂ : Fin n → ℤ} (h₁ : q.IsCharacteristic w₁) (h₂ : q.IsCharacteristic w₂) :
    ∃ z : Fin n → ℤ, w₁ - w₂ = (2 : ℤ) • z := by
  have hdvd : ∀ i : Fin n, (2 : ℤ) ∣ (q.mat *ᵥ (w₁ - w₂)) i := by
    intro i
    rw [mulVec_sub, Pi.sub_apply]
    have h1i := (q.isCharacteristic_iff_mulVec_mod2 w₁).mp h₁ i
    have h2i := (q.isCharacteristic_iff_mulVec_mod2 w₂).mp h₂ i
    exact Int.modEq_iff_dvd.mp (h1i.trans h2i.symm).symm
  choose u hu using hdvd
  have hmul : q.mat *ᵥ (w₁ - w₂) = (2 : ℤ) • u := by
    ext i
    rw [Pi.smul_apply, smul_eq_mul, hu i]
  let z : Fin n → ℤ := q.mat⁻¹ *ᵥ u
  refine ⟨z, ?_⟩
  calc
    w₁ - w₂ = q.mat⁻¹ *ᵥ (q.mat *ᵥ (w₁ - w₂)) := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul q.mat q.isUnit_det, one_mulVec]
    _ = q.mat⁻¹ *ᵥ ((2 : ℤ) • u) := by rw [hmul]
    _ = (2 : ℤ) • z := by rw [mulVec_smul]

/-- Universal mod-8 invariance: `q(w₁, w₁) ≡ q(w₂, w₂) [ZMOD 8]` for any two characteristic
vectors `w₁, w₂` of any integral unimodular form `q`. -/
theorem characteristic_eval_mod8_eq {n : ℕ} (q : IntegralUnimodularForm n)
    {w₁ w₂ : Fin n → ℤ} (h₁ : q.IsCharacteristic w₁) (h₂ : q.IsCharacteristic w₂) :
    q.eval w₁ ≡ q.eval w₂ [ZMOD 8] := by
  rcases q.characteristic_sub_even h₁ h₂ with ⟨z, hz⟩
  have hw1 : w₁ = w₂ + (2 : ℤ) • z := by
    ext i
    have hi := congr_fun hz i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  rw [hw1, q.eval_add, q.pair_smul_right, q.eval_smul]
  have hev : (2 : ℤ) ∣ (q.pair w₂ z + q.eval z) := by
    have hd := Int.modEq_iff_dvd.mp (h₂ z).symm
    have hsum : q.pair w₂ z + q.eval z = (q.pair w₂ z - q.eval z) + 2 * q.eval z := by ring
    rw [hsum]
    exact dvd_add hd (dvd_mul_right 2 _)
  rcases hev with ⟨m, hm⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨-m, ?_⟩
  calc
    q.eval w₂ - (q.eval w₂ + 2 * (2 * q.pair w₂ z) + 2 ^ 2 * q.eval z)
        = -4 * (q.pair w₂ z + q.eval z) := by ring
    _ = -4 * (2 * m) := by rw [hm]
    _ = 8 * (-m) := by ring

theorem isEven_iff_characteristic_zero {n : ℕ} (q : IntegralUnimodularForm n) :
    q.IsEven ↔ q.IsCharacteristic 0 := by
  rw [q.isEven_iff_diag_even, q.isCharacteristic_iff_mulVec_mod2]
  constructor <;> intro h i
  · rw [mulVec_zero, Pi.zero_apply, Int.modEq_iff_dvd, sub_zero]
    exact (h i).two_dvd
  · have hi := h i
    rw [mulVec_zero, Pi.zero_apply, Int.modEq_iff_dvd, sub_zero] at hi
    rcases hi with ⟨k, hk⟩
    exact ⟨k, by linarith⟩

theorem isEven_characteristic_eval_mod8 {n : ℕ} (q : IntegralUnimodularForm n)
    (hq : q.IsEven) {w : Fin n → ℤ} (hw : q.IsCharacteristic w) :
    q.eval w ≡ 0 [ZMOD 8] := by
  have h0 : q.IsCharacteristic 0 := (q.isEven_iff_characteristic_zero).mp hq
  simpa [q.eval_zero] using q.characteristic_eval_mod8_eq hw h0

end IntegralUnimodularForm

end IntegralForms

/-!
## Section 2: Concrete Models (`⟨1⟩`, `⟨-1⟩`, Diagonal, `H`, `E₈`) & `T17` Witnesses
-/

section ConcreteModels

open IntegralUnimodularForm

/-- Rank-1 positive-definite unimodular form `⟨1⟩` (`ℂℙ²`). -/
def diagPos1 : IntegralUnimodularForm 1 where
  mat := !![1]
  isSymm := by ext i j; fin_cases i; fin_cases j; rfl
  det_abs_one := Or.inl (by decide)

/-- Rank-1 negative-definite unimodular form `⟨-1⟩` (`\overline{ℂℙ²}`). -/
def diagNeg1 : IntegralUnimodularForm 1 where
  mat := !![-1]
  isSymm := by ext i j; fin_cases i; fin_cases j; rfl
  det_abs_one := Or.inr (by decide)

/-- Closed `T17` constructive inhabitant for `IntegralUnimodularForm`. -/
def canonicalIntegralUnimodularForm : IntegralUnimodularForm 1 := diagPos1

/-- Diagonal unimodular form `⊕_i ⟨±1⟩` indexed by `s : Fin n → Bool`. -/
def diagonalUnimodular {n : ℕ} (s : Fin n → Bool) : IntegralUnimodularForm n where
  mat := Matrix.diagonal fun i => if s i then (1 : ℤ) else -1
  isSymm := Matrix.diagonal_transpose _
  det_abs_one := by
    rw [Matrix.det_diagonal]
    induction n with
    | zero => left; simp
    | succ m ih =>
      rw [Fin.prod_univ_succ]
      have htail := ih (fun i => s i.succ)
      cases h0 : s 0 <;> rcases htail with ht | ht <;> simp [h0, ht]

instance (n : ℕ) : Inhabited (IntegralUnimodularForm n) :=
  ⟨diagonalUnimodular (fun _ => true)⟩

theorem diagonalUnimodular_eval {n : ℕ} (s : Fin n → Bool) (x : Fin n → ℤ) :
    (diagonalUnimodular s).eval x = ∑ i : Fin n, (if s i then (1 : ℤ) else -1) * (x i) ^ 2 := by
  unfold eval pair diagonalUnimodular
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem diagonalUnimodular_isCharacteristic_iff {n : ℕ} (s : Fin n → Bool) (w : Fin n → ℤ) :
    (diagonalUnimodular s).IsCharacteristic w ↔ ∀ i : Fin n, Odd (w i) := by
  rw [(diagonalUnimodular s).isCharacteristic_iff_mulVec_mod2 w]
  constructor <;> intro h i
  · have hi := h i
    simp only [diagonalUnimodular, Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq] at hi
    cases hs : s i <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul] at hi
    · rw [Int.odd_iff]
      have hd : (2 : ℤ) ∣ (1 - w i) := by
        have := Int.modEq_iff_dvd.mp hi
        omega
      omega
    · rw [Int.odd_iff]
      have hd : (2 : ℤ) ∣ (1 - w i) := Int.modEq_iff_dvd.mp hi
      omega
  · simp only [diagonalUnimodular, Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq]
    rcases h i with ⟨k, hk⟩
    rw [Int.modEq_iff_dvd]
    cases s i <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul]
    · exact ⟨k, by rw [hk]; ring⟩
    · exact ⟨-k, by rw [hk]; ring⟩

/-- Rank-2 even indefinite unimodular hyperbolic form `H` (`S² × S²`). -/
def hyperbolicH : IntegralUnimodularForm 2 where
  mat := !![0, 1; 1, 0]
  isSymm := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  det_abs_one := Or.inr (by decide)

theorem hyperbolicH_isEven : hyperbolicH.IsEven := by
  rw [hyperbolicH.isEven_iff_diag_even]
  intro i
  fin_cases i <;> exact Even.zero

theorem hyperbolicH_eval (x : Fin 2 → ℤ) : hyperbolicH.eval x = 2 * x 0 * x 1 := by
  unfold eval pair hyperbolicH
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  ring

private theorem e8LowerQ_mul_diag :
    e8LowerQ * Matrix.diagonal e8DiagQ = e8LDQ := by
  ext i j
  rw [Matrix.mul_diagonal]
  have hdec : ∀ a b : Fin 8, e8LowerQ a b * e8DiagQ b = e8LDQ a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num [e8LowerQ, e8DiagQ, e8LDQ]
  exact hdec i j

private theorem e8Matrix_eq_LDL :
    e8Matrix.map (Int.castRingHom ℚ) =
      e8LowerQ * Matrix.diagonal e8DiagQ * e8LowerQᵀ := by
  rw [e8LowerQ_mul_diag]
  ext i j
  simp only [Matrix.map_apply, Int.coe_castRingHom, Matrix.mul_apply, Matrix.transpose_apply]
  have hdec : ∀ a b : Fin 8, (e8Matrix a b : ℚ) = ∑ k : Fin 8, e8LDQ a k * e8LowerQ b k := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [e8Matrix, e8LDQ, e8LowerQ, Fin.sum_univ_eight]
  exact hdec i j

theorem e8Matrix_isSymm : e8Matrix.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem e8Matrix_det : e8Matrix.det = 1 := by
  have hQ : (e8Matrix.map (Int.castRingHom ℚ)).det = 1 := by
    rw [e8Matrix_eq_LDL, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have hL : e8LowerQ.det = 1 := by
      have htri : e8LowerQ.IsLowerTriangular := by
        intro i j hij
        simp only [OrderDual.toDual_lt_toDual] at hij
        fin_cases i <;> fin_cases j <;> simp_all [e8LowerQ]
      rw [Matrix.det_of_isLowerTriangular e8LowerQ htri]
      norm_num [Fin.prod_univ_eight, e8LowerQ]
    have hD : (Matrix.diagonal e8DiagQ).det = 1 := by
      rw [Matrix.det_diagonal]
      norm_num [Fin.prod_univ_eight, e8DiagQ]
    rw [hL, hD]
    norm_num
  have hcast : ((e8Matrix.det : ℤ) : ℚ) = (e8Matrix.map (Int.castRingHom ℚ)).det :=
    (Int.castRingHom ℚ).map_det e8Matrix
  rw [hQ] at hcast
  exact Int.cast_injective (α := ℚ) (by simpa using hcast)

/-- Positive-definite even unimodular `E₈` intersection form of rank 8. -/
def e8Form : IntegralUnimodularForm 8 where
  mat := e8Matrix
  isSymm := e8Matrix_isSymm
  det_abs_one := Or.inl e8Matrix_det

theorem e8Form_isEven : e8Form.IsEven := by
  rw [e8Form.isEven_iff_diag_even]
  intro i
  fin_cases i <;> exact even_two

/-- Explicit `840`-scaled sum-of-squares completion of the `E₈` quadratic form over any
commutative ring `R`. -/
theorem e8_sum_of_squares_840 {R : Type*} [CommRing R] (x : Fin 8 → R) :
    (840 : R) * (x ⬝ᵥ ((e8Matrix.map (Int.castRingHom R)) *ᵥ x)) =
      420 * (2 * x 0 - x 1) ^ 2 + 140 * (3 * x 1 - 2 * x 2) ^ 2 +
      70 * (4 * x 2 - 3 * x 3) ^ 2 + 42 * (5 * x 3 - 4 * x 4) ^ 2 +
      28 * (6 * x 4 - 5 * x 5 - 5 * x 7) ^ 2 + 20 * (7 * x 5 - 6 * x 6 - 5 * x 7) ^ 2 +
      15 * (8 * x 6 - 5 * x 7) ^ 2 + 105 * (x 7) ^ 2 := by
  simp only [dotProduct, mulVec, Matrix.map_apply, Int.coe_castRingHom,
    Fin.sum_univ_succ, Fin.isValue, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num [e8Matrix]
  ring

private lemma e8_sos_zero_imp_zero {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x : Fin 8 → R)
    (h : 420 * (2 * x 0 - x 1) ^ 2 + 140 * (3 * x 1 - 2 * x 2) ^ 2 +
      70 * (4 * x 2 - 3 * x 3) ^ 2 + 42 * (5 * x 3 - 4 * x 4) ^ 2 +
      28 * (6 * x 4 - 5 * x 5 - 5 * x 7) ^ 2 + 20 * (7 * x 5 - 6 * x 6 - 5 * x 7) ^ 2 +
      15 * (8 * x 6 - 5 * x 7) ^ 2 + 105 * (x 7) ^ 2 = 0) :
    x = 0 := by
  have t0 : 0 ≤ (2 * x 0 - x 1) ^ 2 := sq_nonneg _
  have t1 : 0 ≤ (3 * x 1 - 2 * x 2) ^ 2 := sq_nonneg _
  have t2 : 0 ≤ (4 * x 2 - 3 * x 3) ^ 2 := sq_nonneg _
  have t3 : 0 ≤ (5 * x 3 - 4 * x 4) ^ 2 := sq_nonneg _
  have t4 : 0 ≤ (6 * x 4 - 5 * x 5 - 5 * x 7) ^ 2 := sq_nonneg _
  have t5 : 0 ≤ (7 * x 5 - 6 * x 6 - 5 * x 7) ^ 2 := sq_nonneg _
  have t6 : 0 ≤ (8 * x 6 - 5 * x 7) ^ 2 := sq_nonneg _
  have t7 : 0 ≤ (x 7) ^ 2 := sq_nonneg _
  have s0 : (2 * x 0 - x 1) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  have s1 : (3 * x 1 - 2 * x 2) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  have s2 : (4 * x 2 - 3 * x 3) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  have s3 : (5 * x 3 - 4 * x 4) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  have s4 : (6 * x 4 - 5 * x 5 - 5 * x 7) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  have s5 : (7 * x 5 - 6 * x 6 - 5 * x 7) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  have s6 : (8 * x 6 - 5 * x 7) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  have s7 : (x 7) ^ 2 = 0 := by linarith [t0, t1, t2, t3, t4, t5, t6, t7, h]
  rw [sq_eq_zero_iff] at s0 s1 s2 s3 s4 s5 s6 s7
  ext i
  fin_cases i <;> dsimp <;> linarith [s0, s1, s2, s3, s4, s5, s6, s7]

theorem e8Matrix_posDef_int : e8Matrix.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos e8Matrix_isSymm fun x hx => ?_
  have hid : (840 : ℤ) * (x ⬝ᵥ e8Matrix *ᵥ x) =
      420 * (2 * x 0 - x 1) ^ 2 + 140 * (3 * x 1 - 2 * x 2) ^ 2 +
      70 * (4 * x 2 - 3 * x 3) ^ 2 + 42 * (5 * x 3 - 4 * x 4) ^ 2 +
      28 * (6 * x 4 - 5 * x 5 - 5 * x 7) ^ 2 + 20 * (7 * x 5 - 6 * x 6 - 5 * x 7) ^ 2 +
      15 * (8 * x 6 - 5 * x 7) ^ 2 + 105 * (x 7) ^ 2 := by
    have h := e8_sum_of_squares_840 (R := ℤ) x
    have hm : e8Matrix.map (Int.castRingHom ℤ) = e8Matrix := by
      ext i j; simp
    rwa [hm] at h
  have hnonneg : 0 ≤ x ⬝ᵥ e8Matrix *ᵥ x := by
    have h840 : 0 ≤ (840 : ℤ) * (x ⬝ᵥ e8Matrix *ᵥ x) := by rw [hid]; positivity
    linarith
  have hne : x ⬝ᵥ e8Matrix *ᵥ x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hid
    exact hx (e8_sos_zero_imp_zero x hid.symm)
  simpa using lt_of_le_of_ne hnonneg hne.symm

theorem e8Matrix_posDef_real : (e8Matrix.map (Int.castRingHom ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (e8Matrix_isSymm.map _)) fun x hx => ?_
  have hid := e8_sum_of_squares_840 (R := ℝ) x
  have hnonneg : 0 ≤ x ⬝ᵥ (e8Matrix.map (Int.castRingHom ℝ)) *ᵥ x := by
    have h840 : 0 ≤ (840 : ℝ) * (x ⬝ᵥ (e8Matrix.map (Int.castRingHom ℝ)) *ᵥ x) := by
      rw [hid]; positivity
    linarith
  have hne : x ⬝ᵥ (e8Matrix.map (Int.castRingHom ℝ)) *ᵥ x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hid
    exact hx (e8_sos_zero_imp_zero x hid.symm)
  simpa using lt_of_le_of_ne hnonneg hne.symm

end ConcreteModels

/-!
## Section 3: Signature `τ(q)` (Sylvester Inertia) & Van der Blij Arithmetic (Prop. 2.4.15)
-/

section SignatureAndVanDerBlij

open IntegralUnimodularForm

/-- Real quadratic form associated with an integral unimodular form `q`. -/
def IntegralUnimodularForm.toRealQuadForm {n : ℕ} (q : IntegralUnimodularForm n) :
    QuadraticForm ℝ (Fin n → ℝ) :=
  (q.mat.map (Int.castRingHom ℝ)).toQuadraticForm'

theorem toRealQuadForm_apply {n : ℕ} (q : IntegralUnimodularForm n) (x : Fin n → ℝ) :
    q.toRealQuadForm x = x ⬝ᵥ ((q.mat.map (Int.castRingHom ℝ)) *ᵥ x) := by
  simp only [IntegralUnimodularForm.toRealQuadForm, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', dotProduct_mulVec]

/-- Signature `τ(q) = b₂⁺ - b₂⁻` defined via Mathlib's `sigPos` and `sigNeg`. -/
def signature {n : ℕ} (q : IntegralUnimodularForm n) : ℤ :=
  (_root_.sigPos q.toRealQuadForm : ℤ) - (_root_.sigNeg q.toRealQuadForm : ℤ)

theorem toRealQuadForm_neg {n : ℕ} (q : IntegralUnimodularForm n) :
    q.neg.toRealQuadForm = -q.toRealQuadForm := by
  ext x
  simp [toRealQuadForm_apply, IntegralUnimodularForm.neg, Matrix.map_neg, Matrix.neg_mulVec,
    dotProduct_neg]

theorem signature_neg {n : ℕ} (q : IntegralUnimodularForm n) :
    signature q.neg = -signature q := by
  unfold signature
  rw [toRealQuadForm_neg, _root_.sigPos_neg, _root_.sigNeg_neg]
  ring

theorem signature_of_posDef {n : ℕ} (q : IntegralUnimodularForm n)
    (hq : (q.mat.map (Int.castRingHom ℝ)).PosDef) :
    signature q = (n : ℤ) := by
  have hQ : q.toRealQuadForm.PosDef := hq.toQuadraticForm'
  have hpos_top : (q.toRealQuadForm.restrict (⊤ : Submodule ℝ (Fin n → ℝ))).PosDef := by
    intro ⟨x, _⟩ hx
    exact hQ x (by simpa using hx)
  have hpos_ge : n ≤ _root_.sigPos q.toRealQuadForm := by
    simpa using _root_.le_sigPos_of_posDef q.toRealQuadForm hpos_top
  have hpos_le : _root_.sigPos q.toRealQuadForm ≤ n := by
    simpa using _root_.sigPos_le_finrank q.toRealQuadForm
  have hpos : _root_.sigPos q.toRealQuadForm = n := le_antisymm hpos_le hpos_ge
  have hneg : _root_.sigNeg q.toRealQuadForm = 0 := by
    obtain ⟨V, hVrank, hVneg⟩ := _root_.exists_finrank_eq_sigNeg_and_negDef q.toRealQuadForm
    rw [← hVrank]
    have hbot : V = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hx0
      have h1 : 0 < q.toRealQuadForm x := hQ x hx0
      have h2 : 0 < (-q.toRealQuadForm) x := hVneg ⟨x, hx⟩ (by simpa using hx0)
      simp only [QuadraticMap.neg_apply] at h2
      linarith
    rw [hbot, finrank_bot]
  unfold signature
  rw [hpos, hneg]
  ring

theorem signature_of_negDef {n : ℕ} (q : IntegralUnimodularForm n)
    (hq : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) :
    signature q = -(n : ℤ) := by
  have hneg : signature q.neg = (n : ℤ) := signature_of_posDef q.neg hq
  rw [signature_neg] at hneg
  linarith

theorem signature_e8Form : signature e8Form = 8 :=
  signature_of_posDef e8Form e8Matrix_posDef_real

theorem signature_e8Form_neg : signature e8Form.neg = -8 := by
  rw [signature_neg, signature_e8Form]

theorem signature_diagonalUnimodular {n : ℕ} (s : Fin n → Bool) :
    signature (diagonalUnimodular s) =
      ({i : Fin n | s i = true}.ncard : ℤ) - ({i : Fin n | s i = false}.ncard : ℤ) := by
  let w : Fin n → ℝ := fun i => if s i then (1 : ℝ) else -1
  have hQ : (diagonalUnimodular s).toRealQuadForm = QuadraticMap.weightedSumSquares ℝ w := by
    ext x
    simp only [toRealQuadForm_apply, diagonalUnimodular, Matrix.map_apply, Matrix.diagonal_apply,
      dotProduct, mulVec, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · cases s i <;> simp <;> ring
    · intro j _ hij
      simp [hij.symm]
    · intro hi; exact False.elim (hi (Finset.mem_univ i))
  have hpos : _root_.sigPos (diagonalUnimodular s).toRealQuadForm =
      {i : Fin n | s i = true}.ncard := by
    rw [hQ, QuadraticForm.sigPos_weightedSumSquares]
    congr 1
    ext i
    cases hs : s i <;> simp [w, hs]
  have hneg : _root_.sigNeg (diagonalUnimodular s).toRealQuadForm =
      {i : Fin n | s i = false}.ncard := by
    rw [hQ, QuadraticForm.sigNeg_weightedSumSquares]
    congr 1
    ext i
    cases hs : s i <;> simp [w, hs]
  unfold signature
  rw [hpos, hneg]

theorem signature_diagPos1 : signature diagPos1 = 1 := by
  have h : diagPos1 = diagonalUnimodular (fun _ => true) := by
    ext i j
    fin_cases i; fin_cases j; simp [diagPos1, diagonalUnimodular]
  rw [h, signature_diagonalUnimodular]
  have h1 : ({i : Fin 1 | true = true} : Set (Fin 1)).ncard = 1 := by simp
  have h2 : ({i : Fin 1 | true = false} : Set (Fin 1)).ncard = 0 := by simp
  rw [h1, h2]
  norm_num

theorem signature_diagNeg1 : signature diagNeg1 = -1 := by
  have h : diagNeg1 = diagPos1.neg := by
    ext i j
    fin_cases i; fin_cases j; simp [diagNeg1, diagPos1, IntegralUnimodularForm.neg]
  rw [h, signature_neg, signature_diagPos1]

theorem signature_hyperbolicH : signature hyperbolicH = 0 := by
  let e : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun v => ![v 0 + v 1, v 0 - v 1]
      invFun := fun v => ![(v 0 + v 1) / 2, (v 0 - v 1) / 2]
      left_inv := fun v => by ext i; fin_cases i <;> simp <;> ring
      right_inv := fun v => by ext i; fin_cases i <;> simp <;> ring
      map_add' := fun u v => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c v => by ext i; fin_cases i <;> simp <;> ring }
  let w : Fin 2 → ℝ := ![2, -2]
  have hiso : QuadraticMap.IsometryEquiv (QuadraticMap.weightedSumSquares ℝ w)
      hyperbolicH.toRealQuadForm :=
    { toLinearEquiv := e
      map_app' := fun v => by
        simp only [toRealQuadForm_apply, hyperbolicH, dotProduct, mulVec, Fin.sum_univ_two,
          Matrix.map_apply, RingHom.coe_coe, Int.coe_castRingHom,
          QuadraticMap.weightedSumSquares_apply, smul_eq_mul, w, e, LinearEquiv.coe_mk,
          LinearMap.coe_mk, AddHom.coe_mk]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
        ring }
  have heq : QuadraticMap.Equivalent hyperbolicH.toRealQuadForm
      (QuadraticMap.weightedSumSquares ℝ w) := ⟨hiso.symm⟩
  have hpos : _root_.sigPos hyperbolicH.toRealQuadForm = 1 := by
    rw [heq.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares]
    have hs : {i : Fin 2 | 0 < w i} = {0} := by
      ext i; fin_cases i <;> simp [w]
    rw [hs, Set.ncard_singleton]
  have hneg : _root_.sigNeg hyperbolicH.toRealQuadForm = 1 := by
    rw [heq.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares]
    have hs : {i : Fin 2 | w i < 0} = {1} := by
      ext i; fin_cases i <;> simp [w]
    rw [hs, Set.ncard_singleton]
  unfold signature
  rw [hpos, hneg]
  norm_num

theorem signature_of_isIso {n : ℕ} {q₁ q₂ : IntegralUnimodularForm n}
    (h : q₁.IsIso q₂) : signature q₁ = signature q₂ := by
  rcases h with ⟨T, hdet, hT⟩
  let T_R : Matrix (Fin n) (Fin n) ℝ := T.map (Int.castRingHom ℝ)
  have hdet_R : T_R.det ≠ 0 := by
    have hm : T_R.det = (T.det : ℝ) := ((Int.castRingHom ℝ).map_det T).symm
    rw [hm]
    rcases hdet with h1 | h1 <;> rw [h1] <;> norm_num
  let f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    { toLinearMap := Matrix.toLin' T_R
      invFun := Matrix.toLin' T_R⁻¹
      left_inv := fun x => by
        change T_R⁻¹ *ᵥ (T_R *ᵥ x) = x
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul T_R (isUnit_iff_ne_zero.mpr hdet_R), one_mulVec]
      right_inv := fun x => by
        change T_R *ᵥ (T_R⁻¹ *ᵥ x) = x
        rw [mulVec_mulVec, Matrix.mul_nonsing_inv T_R (isUnit_iff_ne_zero.mpr hdet_R), one_mulVec] }
  have hiso : QuadraticMap.IsometryEquiv q₂.toRealQuadForm q₁.toRealQuadForm :=
    { toLinearEquiv := f
      map_app' := fun x => by
        dsimp [f]
        rw [toRealQuadForm_apply, toRealQuadForm_apply]
        have hmat : T_Rᵀ * q₁.mat.map (Int.castRingHom ℝ) * T_R = q₂.mat.map (Int.castRingHom ℝ) := by
          ext i j
          have hij := congrArg (fun M => M i j) hT
          have hijR := congrArg (Int.castRingHom ℝ) hij
          simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul] at hijR
          simpa [T_R, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] using hijR
        rw [← hmat]
        calc
          (T_R *ᵥ x) ⬝ᵥ (q₁.mat.map (Int.castRingHom ℝ) *ᵥ (T_R *ᵥ x))
              = (x ᵥ* T_Rᵀ) ⬝ᵥ (q₁.mat.map (Int.castRingHom ℝ) *ᵥ (T_R *ᵥ x)) := by
                rw [Matrix.vecMul_transpose]
          _ = x ⬝ᵥ (T_Rᵀ *ᵥ (q₁.mat.map (Int.castRingHom ℝ) *ᵥ (T_R *ᵥ x))) := by
                rw [← Matrix.dotProduct_mulVec]
          _ = x ⬝ᵥ ((T_Rᵀ * q₁.mat.map (Int.castRingHom ℝ) * T_R) *ᵥ x) := by
                simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec] }
  have heq : QuadraticMap.Equivalent q₁.toRealQuadForm q₂.toRealQuadForm := ⟨hiso.symm⟩
  unfold signature
  rw [heq.sigPos_eq, heq.sigNeg_eq]

theorem signature_oplus {n₁ n₂ : ℕ} (q₁ : IntegralUnimodularForm n₁)
    (q₂ : IntegralUnimodularForm n₂) :
    signature (q₁.oplus q₂) = signature q₁ + signature q₂ := by
  obtain ⟨w₁_raw, _, ⟨e₁_raw⟩⟩ := q₁.toRealQuadForm.equivalent_one_zero_neg_one_weighted_sum_squared
  obtain ⟨w₂_raw, _, ⟨e₂_raw⟩⟩ := q₂.toRealQuadForm.equivalent_one_zero_neg_one_weighted_sum_squared
  have hr₁ : Module.finrank ℝ (Fin n₁ → ℝ) = n₁ := Module.finrank_fin_fun ℝ
  have hr₂ : Module.finrank ℝ (Fin n₂ → ℝ) = n₂ := Module.finrank_fin_fun ℝ
  let c₁ : Fin (Module.finrank ℝ (Fin n₁ → ℝ)) ≃ Fin n₁ := finCongr hr₁
  let c₂ : Fin (Module.finrank ℝ (Fin n₂ → ℝ)) ≃ Fin n₂ := finCongr hr₂
  let w₁ : Fin n₁ → ℝ := fun i => w₁_raw (c₁.symm i)
  let w₂ : Fin n₂ → ℝ := fun j => w₂_raw (c₂.symm j)
  let e₁ : QuadraticMap.IsometryEquiv q₁.toRealQuadForm (QuadraticMap.weightedSumSquares ℝ w₁) :=
    e₁_raw.trans
      { toLinearEquiv := LinearEquiv.funCongrLeft ℝ ℝ c₁.symm
        map_app' := fun v => by
          simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
            LinearEquiv.funCongrLeft_apply]
          rw [← Equiv.sum_comp c₁.symm]
          refine Finset.sum_congr rfl fun i _ => by simp [w₁] }
  let e₂ : QuadraticMap.IsometryEquiv q₂.toRealQuadForm (QuadraticMap.weightedSumSquares ℝ w₂) :=
    e₂_raw.trans
      { toLinearEquiv := LinearEquiv.funCongrLeft ℝ ℝ c₂.symm
        map_app' := fun v => by
          simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
            LinearEquiv.funCongrLeft_apply]
          rw [← Equiv.sum_comp c₂.symm]
          refine Finset.sum_congr rfl fun j _ => by simp [w₂] }
  let w : Fin (n₁ + n₂) → ℝ := fun k => Sum.elim w₁ w₂ (finSumFinEquiv.symm k)
  let eSum : (Fin (n₁ + n₂) → ℝ) ≃ₗ[ℝ] (Fin (n₁ + n₂) → ℝ) :=
    { toFun := fun x k =>
        Sum.elim (e₁ (fun i => x (finSumFinEquiv (Sum.inl i))))
          (e₂ (fun j => x (finSumFinEquiv (Sum.inr j)))) (finSumFinEquiv.symm k)
      invFun := fun y k =>
        Sum.elim (e₁.symm (fun i => y (finSumFinEquiv (Sum.inl i))))
          (e₂.symm (fun j => y (finSumFinEquiv (Sum.inr j)))) (finSumFinEquiv.symm k)
      left_inv := fun x => by
        ext k
        rcases hk : finSumFinEquiv.symm k with i | j
        · have hk' : k = finSumFinEquiv (Sum.inl i) := (Equiv.symm_apply_eq finSumFinEquiv).mp hk
          subst hk'; simp
        · have hk' : k = finSumFinEquiv (Sum.inr j) := (Equiv.symm_apply_eq finSumFinEquiv).mp hk
          subst hk'; simp
      right_inv := fun y => by
        ext k
        rcases hk : finSumFinEquiv.symm k with i | j
        · have hk' : k = finSumFinEquiv (Sum.inl i) := (Equiv.symm_apply_eq finSumFinEquiv).mp hk
          subst hk'; simp
        · have hk' : k = finSumFinEquiv (Sum.inr j) := (Equiv.symm_apply_eq finSumFinEquiv).mp hk
          subst hk'; simp
      map_add' := fun x y => by
        ext k
        rcases hk : finSumFinEquiv.symm k with i | j
        · simp only [hk, Sum.elim_inl, Pi.add_apply]
          exact congrFun (map_add e₁ (fun i => x (finSumFinEquiv (Sum.inl i)))
            (fun i => y (finSumFinEquiv (Sum.inl i)))) i
        · simp only [hk, Sum.elim_inr, Pi.add_apply]
          exact congrFun (map_add e₂ (fun j => x (finSumFinEquiv (Sum.inr j)))
            (fun j => y (finSumFinEquiv (Sum.inr j)))) j
      map_smul' := fun c x => by
        ext k
        rcases hk : finSumFinEquiv.symm k with i | j
        · simp only [hk, Sum.elim_inl, Pi.smul_apply]
          exact congrFun (map_smul e₁ c (fun i => x (finSumFinEquiv (Sum.inl i)))) i
        · simp only [hk, Sum.elim_inr, Pi.smul_apply]
          exact congrFun (map_smul e₂ c (fun j => x (finSumFinEquiv (Sum.inr j)))) j }
  have hiso : QuadraticMap.IsometryEquiv (q₁.oplus q₂).toRealQuadForm
      (QuadraticMap.weightedSumSquares ℝ w) :=
    { toLinearEquiv := eSum
      map_app' := fun x => by
        have hx : (q₁.oplus q₂).toRealQuadForm x =
            q₁.toRealQuadForm (fun i => x (finSumFinEquiv (Sum.inl i))) +
            q₂.toRealQuadForm (fun j => x (finSumFinEquiv (Sum.inr j))) := by
          simp only [toRealQuadForm_apply, oplus, dotProduct, mulVec]
          have hsum : ∀ f : Fin (n₁ + n₂) → ℝ,
              ∑ k : Fin (n₁ + n₂), f k =
                (∑ i : Fin n₁, f (finSumFinEquiv (Sum.inl i))) +
                (∑ j : Fin n₂, f (finSumFinEquiv (Sum.inr j))) := by
            intro f
            rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
          rw [hsum]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [hsum]
            simp [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
              Matrix.fromBlocks_apply₁₂]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [hsum]
            simp [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
              Matrix.fromBlocks_apply₂₂]
        have hw_sum : QuadraticMap.weightedSumSquares ℝ w (eSum x) =
            QuadraticMap.weightedSumSquares ℝ w₁ (e₁ (fun i => x (finSumFinEquiv (Sum.inl i)))) +
            QuadraticMap.weightedSumSquares ℝ w₂ (e₂ (fun j => x (finSumFinEquiv (Sum.inr j)))) := by
          simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
          rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            simp [w, eSum]
          · refine Finset.sum_congr rfl fun j _ => ?_
            simp [w, eSum]
        change QuadraticMap.weightedSumSquares ℝ w (eSum x) = (q₁.oplus q₂).toRealQuadForm x
        rw [hw_sum, e₁.map_app, e₂.map_app, hx] }
  have heq1 : QuadraticMap.Equivalent q₁.toRealQuadForm (QuadraticMap.weightedSumSquares ℝ w₁) := ⟨e₁⟩
  have heq2 : QuadraticMap.Equivalent q₂.toRealQuadForm (QuadraticMap.weightedSumSquares ℝ w₂) := ⟨e₂⟩
  have heq12 : QuadraticMap.Equivalent (q₁.oplus q₂).toRealQuadForm
      (QuadraticMap.weightedSumSquares ℝ w) := ⟨hiso⟩
  have hsplit_set : ∀ (p₁ : Fin n₁ → Prop) (p₂ : Fin n₂ → Prop),
      {k : Fin (n₁ + n₂) | Sum.elim p₁ p₂ (finSumFinEquiv.symm k)}.ncard =
        {i : Fin n₁ | p₁ i}.ncard + {j : Fin n₂ | p₂ j}.ncard := by
    intro p₁ p₂
    let S₁ : Set (Fin (n₁ + n₂)) := (fun i => finSumFinEquiv (Sum.inl i)) '' {i | p₁ i}
    let S₂ : Set (Fin (n₁ + n₂)) := (fun j => finSumFinEquiv (Sum.inr j)) '' {j | p₂ j}
    have hU : {k : Fin (n₁ + n₂) | Sum.elim p₁ p₂ (finSumFinEquiv.symm k)} = S₁ ∪ S₂ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, S₁, S₂]
      rcases hk : finSumFinEquiv.symm k with i | j
      · have hk' : k = finSumFinEquiv (Sum.inl i) := (Equiv.symm_apply_eq finSumFinEquiv).mp hk
        subst hk'
        simp only [Equiv.symm_apply_apply, Sum.elim_inl]
        constructor
        · intro h; exact Or.inl ⟨i, h, rfl⟩
        · rintro (⟨a, ha, heq⟩ | ⟨b, _, heq⟩)
          · exact Sum.inl.inj (finSumFinEquiv.injective heq) ▸ ha
          · exact absurd (finSumFinEquiv.injective heq) (by simp)
      · have hk' : k = finSumFinEquiv (Sum.inr j) := (Equiv.symm_apply_eq finSumFinEquiv).mp hk
        subst hk'
        simp only [Equiv.symm_apply_apply, Sum.elim_inr]
        constructor
        · intro h; exact Or.inr ⟨j, h, rfl⟩
        · rintro (⟨a, _, heq⟩ | ⟨b, hb, heq⟩)
          · exact absurd (finSumFinEquiv.injective heq) (by simp)
          · exact Sum.inr.inj (finSumFinEquiv.injective heq) ▸ hb
    have hdisj : Disjoint S₁ S₂ := by
      rw [Set.disjoint_left]
      rintro k ⟨i, _, rfl⟩ ⟨j, _, h⟩
      have h' := finSumFinEquiv.injective h
      simp at h'
    have hnc1 : S₁.ncard = {i : Fin n₁ | p₁ i}.ncard :=
      Set.ncard_image_of_injective _ (finSumFinEquiv.injective.comp Sum.inl_injective)
    have hnc2 : S₂.ncard = {j : Fin n₂ | p₂ j}.ncard :=
      Set.ncard_image_of_injective _ (finSumFinEquiv.injective.comp Sum.inr_injective)
    rw [hU, Set.ncard_union_eq hdisj, hnc1, hnc2]
  have hpos12 : _root_.sigPos (q₁.oplus q₂).toRealQuadForm =
      _root_.sigPos q₁.toRealQuadForm + _root_.sigPos q₂.toRealQuadForm := by
    rw [heq12.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares,
      heq1.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares,
      heq2.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares]
    have hp : {k : Fin (n₁ + n₂) | 0 < w k} =
        {k : Fin (n₁ + n₂) | Sum.elim (fun i => 0 < w₁ i) (fun j => 0 < w₂ j) (finSumFinEquiv.symm k)} := by
      ext k; rcases hk : finSumFinEquiv.symm k with i | j <;> simp [w, hk]
    rw [hp]
    exact hsplit_set (fun i => 0 < w₁ i) (fun j => 0 < w₂ j)
  have hneg12 : _root_.sigNeg (q₁.oplus q₂).toRealQuadForm =
      _root_.sigNeg q₁.toRealQuadForm + _root_.sigNeg q₂.toRealQuadForm := by
    rw [heq12.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares,
      heq1.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares,
      heq2.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares]
    have hn : {k : Fin (n₁ + n₂) | w k < 0} =
        {k : Fin (n₁ + n₂) | Sum.elim (fun i => w₁ i < 0) (fun j => w₂ j < 0) (finSumFinEquiv.symm k)} := by
      ext k; rcases hk : finSumFinEquiv.symm k with i | j <;> simp [w, hk]
    rw [hn]
    exact hsplit_set (fun i => w₁ i < 0) (fun j => w₂ j < 0)
  unfold signature
  rw [hpos12, hneg12]
  push_cast
  ring

/-- Van der Blij property (Prop. 2.4.15): every characteristic vector `w` satisfies
`q(w, w) ≡ τ(q) [ZMOD 8]`. -/
def IsVanDerBlij {n : ℕ} (q : IntegralUnimodularForm n) : Prop :=
  ∀ w : Fin n → ℤ, q.IsCharacteristic w → q.eval w ≡ signature q [ZMOD 8]

theorem vanDerBlij_of_exists {n : ℕ} (q : IntegralUnimodularForm n) {w₀ : Fin n → ℤ}
    (hw₀ : q.IsCharacteristic w₀) (hmod : q.eval w₀ ≡ signature q [ZMOD 8]) :
    IsVanDerBlij q := by
  intro w hw
  exact (q.characteristic_eval_mod8_eq hw hw₀).trans hmod

private theorem odd_sq_mod8 {a : ℤ} (ha : Odd a) : a ^ 2 ≡ 1 [ZMOD 8] := by
  rcases ha with ⟨k, rfl⟩
  rw [Int.modEq_iff_dvd]
  have hk : (1 : ℤ) - (2 * k + 1) ^ 2 = -(4 * (k * (k + 1))) := by ring
  rw [hk]
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨-(m * (2 * m + 1)), by rw [hm]; ring⟩
  · exact ⟨-((2 * m + 1) * (m + 1)), by rw [hm]; ring⟩

theorem vanDerBlij_diagonalUnimodular {n : ℕ} (s : Fin n → Bool) :
    IsVanDerBlij (diagonalUnimodular s) := by
  intro w hw
  have hodd := (diagonalUnimodular_isCharacteristic_iff s w).mp hw
  rw [diagonalUnimodular_eval, signature_diagonalUnimodular]
  have hsum : (∑ i : Fin n, (if s i then (1 : ℤ) else -1) * w i ^ 2) ≡
      ∑ i : Fin n, (if s i then (1 : ℤ) else -1) [ZMOD 8] := by
    rw [Int.modEq_iff_dvd, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    have hi : (8 : ℤ) ∣ ((if s i then (1 : ℤ) else -1) -
        (if s i then (1 : ℤ) else -1) * w i ^ 2) := by
      have hm := Int.modEq_iff_dvd.mp ((odd_sq_mod8 (hodd i)).mul_left (if s i then (1 : ℤ) else -1))
      simpa [mul_one] using hm
    exact hi
  have hcard : (∑ i : Fin n, (if s i then (1 : ℤ) else -1)) =
      ({i : Fin n | s i = true}.ncard : ℤ) - ({i : Fin n | s i = false}.ncard : ℤ) := by
    have hsplit : ∀ i : Fin n, (if s i then (1 : ℤ) else -1) =
        (if s i = true then (1 : ℤ) else 0) - (if s i = false then (1 : ℤ) else 0) := by
      intro i; cases s i <;> simp
    simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_boole]
    have ht' : ((Finset.univ.filter (fun x : Fin n => s x = true)).card : ℤ) =
        ({i : Fin n | s i = true}.ncard : ℤ) := by
      classical
      rw [← Set.ncard_coe_finset]
      congr 2; ext i; simp
    have hf' : ((Finset.univ.filter (fun x : Fin n => s x = false)).card : ℤ) =
        ({i : Fin n | s i = false}.ncard : ℤ) := by
      classical
      rw [← Set.ncard_coe_finset]
      congr 2; ext i; simp
    rw [ht', hf']
  rw [← hcard]
  exact hsum

theorem vanDerBlij_diagPos1 : IsVanDerBlij diagPos1 := by
  have h : diagPos1 = diagonalUnimodular (fun _ => true) := by
    ext i j; fin_cases i; fin_cases j; simp [diagPos1, diagonalUnimodular]
  rw [h]
  exact vanDerBlij_diagonalUnimodular _

theorem vanDerBlij_diagNeg1 : IsVanDerBlij diagNeg1 := by
  have h : diagNeg1 = diagonalUnimodular (fun _ => false) := by
    ext i j; fin_cases i; fin_cases j; simp [diagNeg1, diagonalUnimodular]
  rw [h]
  exact vanDerBlij_diagonalUnimodular _

theorem vanDerBlij_hyperbolicH : IsVanDerBlij hyperbolicH := by
  intro w hw
  have hev := hyperbolicH.isEven_characteristic_eval_mod8 hyperbolicH_isEven hw
  rw [signature_hyperbolicH]
  exact hev

theorem vanDerBlij_e8Form : IsVanDerBlij e8Form := by
  intro w hw
  have hev := e8Form.isEven_characteristic_eval_mod8 e8Form_isEven hw
  rw [signature_e8Form]
  exact hev.trans (by decide)

theorem vanDerBlij_neg {n : ℕ} {q : IntegralUnimodularForm n} (hq : IsVanDerBlij q) :
    IsVanDerBlij q.neg := by
  intro w hw
  rw [neg_eval, signature_neg]
  exact (hq w ((isCharacteristic_neg_iff q w).mp hw)).neg

theorem vanDerBlij_oplus {n₁ n₂ : ℕ} {q₁ : IntegralUnimodularForm n₁}
    {q₂ : IntegralUnimodularForm n₂} (h₁ : IsVanDerBlij q₁) (h₂ : IsVanDerBlij q₂) :
    IsVanDerBlij (q₁.oplus q₂) := by
  intro w hw
  rcases (isCharacteristic_oplus q₁ q₂ w).mp hw with ⟨hw₁, hw₂⟩
  rw [oplus_eval, signature_oplus]
  exact (h₁ _ hw₁).add (h₂ _ hw₂)

theorem vanDerBlij_of_isIso {n : ℕ} {q₁ q₂ : IntegralUnimodularForm n}
    (hiso : q₁.IsIso q₂) (h₁ : IsVanDerBlij q₁) : IsVanDerBlij q₂ := by
  rcases hiso with ⟨T, hdet, hT⟩
  intro w hw
  have hw' := (isCharacteristic_isIso T hdet hT w).mp hw
  rw [isIso_eval T hT, ← signature_of_isIso ⟨T, hdet, hT⟩]
  exact h₁ (T *ᵥ w) hw'

theorem vanDerBlij_of_stabilized {n : ℕ} (q : IntegralUnimodularForm n) :
    IsVanDerBlij (q.oplus (diagPos1.oplus diagNeg1)) ↔ IsVanDerBlij q := by
  constructor
  · intro hstab w hw
    let w' : Fin (n + (1 + 1)) → ℤ := fun k =>
      Sum.elim w (fun _ => 1) (finSumFinEquiv.symm k)
    have hw' : (q.oplus (diagPos1.oplus diagNeg1)).IsCharacteristic w' := by
      rw [isCharacteristic_oplus]
      refine ⟨?_, ?_⟩
      · simpa [w', Equiv.symm_apply_apply] using hw
      · rw [isCharacteristic_oplus]
        constructor
        · rw [show diagPos1 = diagonalUnimodular (fun _ => true) by
            ext i j; fin_cases i; fin_cases j; simp [diagPos1, diagonalUnimodular],
            diagonalUnimodular_isCharacteristic_iff]
          intro _; simp [w', Equiv.symm_apply_apply]
        · rw [show diagNeg1 = diagonalUnimodular (fun _ => false) by
            ext i j; fin_cases i; fin_cases j; simp [diagNeg1, diagonalUnimodular],
            diagonalUnimodular_isCharacteristic_iff]
          intro _; simp [w', Equiv.symm_apply_apply]
    have hmod := hstab w' hw'
    have hev : (q.oplus (diagPos1.oplus diagNeg1)).eval w' = q.eval w := by
      rw [oplus_eval, oplus_eval]
      have hq1 : q.eval (fun i => w' (finSumFinEquiv (Sum.inl i))) = q.eval w := by
        congr 1; ext i; simp [w', Equiv.symm_apply_apply]
      have hp : diagPos1.eval (fun i => w' (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i))))) = 1 := by
        simp [diagPos1, eval, pair, dotProduct, mulVec, w', Equiv.symm_apply_apply]
      have hn : diagNeg1.eval (fun i => w' (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i))))) = -1 := by
        simp [diagNeg1, eval, pair, dotProduct, mulVec, w', Equiv.symm_apply_apply]
      rw [hq1, hp, hn]
      ring
    have hsig : signature (q.oplus (diagPos1.oplus diagNeg1)) = signature q := by
      rw [signature_oplus, signature_oplus, signature_diagPos1, signature_diagNeg1]
      ring
    rwa [hev, hsig] at hmod
  · intro hq
    exact vanDerBlij_oplus hq (vanDerBlij_oplus vanDerBlij_diagPos1 vanDerBlij_diagNeg1)

/-- Standard model form `a • E₈ ⊕ b • H ⊕ c • ⟨1⟩ ⊕ d • ⟨-1⟩` covering all indefinite forms
and all standard 4-manifold intersection forms (`S⁴`, `ℂℙ²`, `S² × S²`, `K3`, `E(n)`). -/
def standard4ManifoldForm : (a b c d : ℕ) → IntegralUnimodularForm (8 * a + 2 * b + c + d)
  | 0, 0, 0, 0 => diagonalUnimodular (fun i : Fin 0 => False.elim i.elim0)
  | a + 1, b, c, d => by
    have hrank : 8 + (8 * a + 2 * b + c + d) = 8 * (a + 1) + 2 * b + c + d := by omega
    exact hrank ▸ e8Form.oplus (standard4ManifoldForm a b c d)
  | 0, b + 1, c, d => by
    have hrank : 2 + (8 * 0 + 2 * b + c + d) = 8 * 0 + 2 * (b + 1) + c + d := by omega
    exact hrank ▸ hyperbolicH.oplus (standard4ManifoldForm 0 b c d)
  | 0, 0, c + 1, d => by
    have hrank : 1 + (8 * 0 + 2 * 0 + c + d) = 8 * 0 + 2 * 0 + (c + 1) + d := by omega
    exact hrank ▸ diagPos1.oplus (standard4ManifoldForm 0 0 c d)
  | 0, 0, 0, d + 1 => by
    have hrank : 1 + (8 * 0 + 2 * 0 + 0 + d) = 8 * 0 + 2 * 0 + 0 + (d + 1) := by omega
    exact hrank ▸ diagNeg1.oplus (standard4ManifoldForm 0 0 0 d)

private theorem vanDerBlij_eqRec {n m : ℕ} (h : n = m) (q : IntegralUnimodularForm n)
    (hq : IsVanDerBlij q) : IsVanDerBlij (h ▸ q) := by
  subst h
  exact hq

theorem vanDerBlij_standard_4manifold_form (a b c d : ℕ) :
    IsVanDerBlij (standard4ManifoldForm a b c d) := by
  induction a with
  | zero =>
    induction b with
    | zero =>
      induction c with
      | zero =>
        induction d with
        | zero =>
          simpa [standard4ManifoldForm] using vanDerBlij_diagonalUnimodular _
        | succ d ihd =>
          simpa [standard4ManifoldForm] using
            vanDerBlij_eqRec _ _ (vanDerBlij_oplus vanDerBlij_diagNeg1 ihd)
      | succ c ihc =>
        simpa [standard4ManifoldForm] using
          vanDerBlij_eqRec _ _ (vanDerBlij_oplus vanDerBlij_diagPos1 ihc)
    | succ b ihb =>
      simpa [standard4ManifoldForm] using
        vanDerBlij_eqRec _ _ (vanDerBlij_oplus vanDerBlij_hyperbolicH ihb)
  | succ a iha =>
    simpa [standard4ManifoldForm] using
      vanDerBlij_eqRec _ _ (vanDerBlij_oplus vanDerBlij_e8Form iha)

end SignatureAndVanDerBlij

/-!
## Section 4: Virtual Dimension `d(σ)` & Kronheimer–Mrowka Thom Genus (Lemma 2.2.10, Thm. 2.4.9)
-/

section VirtualDimAndThomGenus

/-- Expected (virtual) dimension `d(σ) = (c₁(σ)² - 2χ - 3τ) / 4` of the Seiberg–Witten
moduli space (Nicolaescu Lemma 2.2.10). -/
def virtualDim (c1_sq chi tau : ℤ) : ℤ :=
  (c1_sq - 2 * chi - 3 * tau) / 4

/-- Topological Betti identity `2χ + 3τ = 4(b₀ - b₁ + b₂⁺) + τ` (Nicolaescu §2.2.2). -/
theorem two_chi_add_three_tau (b0 b1 b2p b2m : ℤ) :
    2 * (2 * (b0 - b1) + (b2p + b2m)) + 3 * (b2p - b2m) =
      4 * (b0 - b1 + b2p) + (b2p - b2m) := by
  ring

/-- Under Van der Blij (`c₁² ≡ τ [ZMOD 8]`), `4 ∣ (c₁² - 2χ - 3τ)`. -/
theorem four_dvd_virtualDim_num_of_vanDerBlij {c1_sq b0 b1 b2p b2m : ℤ}
    (hvdb : c1_sq ≡ b2p - b2m [ZMOD 8]) :
    4 ∣ (c1_sq - 2 * (2 * (b0 - b1) + (b2p + b2m)) - 3 * (b2p - b2m)) ∧
      4 * virtualDim c1_sq (2 * (b0 - b1) + (b2p + b2m)) (b2p - b2m) =
        c1_sq - 2 * (2 * (b0 - b1) + (b2p + b2m)) - 3 * (b2p - b2m) := by
  rcases Int.modEq_iff_dvd.mp hvdb.symm with ⟨k, hk⟩
  have hnum : c1_sq - 2 * (2 * (b0 - b1) + (b2p + b2m)) - 3 * (b2p - b2m) =
      4 * (2 * k - (b0 - b1 + b2p)) := by
    linarith
  have hdvd : 4 ∣ (c1_sq - 2 * (2 * (b0 - b1) + (b2p + b2m)) - 3 * (b2p - b2m)) :=
    ⟨2 * k - (b0 - b1 + b2p), hnum⟩
  exact ⟨hdvd, Int.mul_ediv_cancel' hdvd⟩

/-- Parity of the SW virtual dimension: `d(σ) ≡ -(b₀ - b₁ + b₂⁺) [ZMOD 2]` (Nicolaescu Lemma 2.2.10,
giving odd `d(σ)` in Donaldson's theorem when `b₀ = 1, b₁ = 0, b₂⁺ = 0`). -/
theorem virtualDim_parity_of_vanDerBlij {c1_sq b0 b1 b2p b2m : ℤ}
    (hvdb : c1_sq ≡ b2p - b2m [ZMOD 8]) :
    virtualDim c1_sq (2 * (b0 - b1) + (b2p + b2m)) (b2p - b2m) ≡ -(b0 - b1 + b2p) [ZMOD 2] := by
  rcases Int.modEq_iff_dvd.mp hvdb.symm with ⟨k, hk⟩
  have hnum : c1_sq - 2 * (2 * (b0 - b1) + (b2p + b2m)) - 3 * (b2p - b2m) =
      4 * (2 * k - (b0 - b1 + b2p)) := by
    linarith
  unfold virtualDim
  rw [hnum, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [Int.modEq_iff_dvd]
  exact ⟨-k, by ring⟩

/-- Negative-definite simply-connected (`b₀ = 1, b₁ = 0, b₂⁺ = 0`) virtual dimension formula
`4 d(σ) = c₁² + b₂ - 4`. -/
theorem virtualDim_negDef_b1_zero {c1_sq b2 : ℤ} (hvdb : c1_sq ≡ -b2 [ZMOD 8]) :
    4 * virtualDim c1_sq (2 + b2) (-b2) = c1_sq + b2 - 4 := by
  have h := (four_dvd_virtualDim_num_of_vanDerBlij (b0 := 1) (b1 := 0) (b2p := 0) (b2m := b2)
    (by simpa using hvdb)).2
  norm_num at h
  linarith

/-- Kähler virtual dimension `d(L) = L² - L ⋅ K_M` when `c₁(σ_L) = 2L - K_M` and
`K_M² = 2χ + 3τ` (Nicolaescu Eq. (3.2.4)). -/
theorem virtualDim_kahler {L_sq LK K_sq chi tau : ℤ} (hK : K_sq = 2 * chi + 3 * tau) :
    virtualDim (4 * L_sq - 4 * LK + K_sq) chi tau = L_sq - LK := by
  unfold virtualDim
  rw [hK]
  have h : 4 * L_sq - 4 * LK + (2 * chi + 3 * tau) - 2 * chi - 3 * tau = 4 * (L_sq - LK) := by ring
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- Kronheimer–Mrowka / Thom degree-`d` genus formula `g_min(dH) = 1 + d(d - 3)/2`. -/
def thomGenus (d : ℤ) : ℤ :=
  1 + d * (d - 3) / 2

theorem two_dvd_mul_sub_three (d : ℤ) : 2 ∣ d * (d - 3) := by
  rcases Int.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (d - 3), by rw [hk]; ring⟩
  · exact ⟨d * (k - 1), by rw [hk]; ring⟩

theorem thomGenus_adjunction_eq (d : ℤ) :
    2 * thomGenus d - 2 = (-3) * d + d * d := by
  unfold thomGenus
  have hm := Int.mul_ediv_cancel' (two_dvd_mul_sub_three d)
  linarith

/-- Kronheimer–Mrowka blow-up intersection identities on `ℂℙ² # d² \overline{ℂℙ²}`:
the proper transform `Σ̃ = dH - ∑ E_i` satisfies `Σ̃² = 0` and `-K_M ⋅ Σ̃ = d(3 - d)`
(Nicolaescu Eq. (2.4.20)). -/
theorem km_blowup_intersection_identities (d : ℤ) :
    let k : ℕ := d.natAbs ^ 2
    let q := diagPos1.oplus (diagonalUnimodular (fun _ : Fin k => false))
    let sigmaTilde : Fin (1 + k) → ℤ := fun m =>
      Sum.elim (fun _ => d) (fun _ => -1) (finSumFinEquiv.symm m)
    let negKM : Fin (1 + k) → ℤ := fun m =>
      Sum.elim (fun _ => 3) (fun _ => -1) (finSumFinEquiv.symm m)
    q.eval sigmaTilde = 0 ∧
      q.pair negKM sigmaTilde = d * (3 - d) ∧
      q.eval negKM = 9 - d ^ 2 := by
  intro k q sigmaTilde negKM
  have hk : (k : ℤ) = d ^ 2 := by
    simp only [k, Nat.cast_pow, Int.natAbs_sq]
  have h1 : q.eval sigmaTilde = 0 := by
    rw [IntegralUnimodularForm.oplus_eval, diagonalUnimodular_eval]
    have hp : diagPos1.eval (fun i => sigmaTilde (finSumFinEquiv (Sum.inl i))) = d ^ 2 := by
      simp [diagPos1, IntegralUnimodularForm.eval, IntegralUnimodularForm.pair, dotProduct,
        mulVec, sigmaTilde]
      ring
    have hn : ∑ j : Fin k, (if false then (1 : ℤ) else -1) *
        (sigmaTilde (finSumFinEquiv (Sum.inr j))) ^ 2 = -(k : ℤ) := by
      simp [sigmaTilde]
    rw [hp, hn, hk]
    ring
  have h2 : q.pair negKM sigmaTilde = d * (3 - d) := by
    rw [IntegralUnimodularForm.oplus_pair]
    have hp : diagPos1.pair (fun i => negKM (finSumFinEquiv (Sum.inl i)))
        (fun i => sigmaTilde (finSumFinEquiv (Sum.inl i))) = 3 * d := by
      simp [diagPos1, IntegralUnimodularForm.pair, dotProduct, mulVec, negKM, sigmaTilde]
    have hn : (diagonalUnimodular (fun _ : Fin k => false)).pair
        (fun j => negKM (finSumFinEquiv (Sum.inr j)))
        (fun j => sigmaTilde (finSumFinEquiv (Sum.inr j))) = -(k : ℤ) := by
      simp [diagonalUnimodular, IntegralUnimodularForm.pair, dotProduct, mulVec, negKM,
        sigmaTilde, Matrix.diagonal_apply]
    rw [hp, hn, hk]
    ring
  have h3 : q.eval negKM = 9 - d ^ 2 := by
    rw [IntegralUnimodularForm.oplus_eval, diagonalUnimodular_eval]
    have hp : diagPos1.eval (fun i => negKM (finSumFinEquiv (Sum.inl i))) = 9 := by
      simp [diagPos1, IntegralUnimodularForm.eval, IntegralUnimodularForm.pair, dotProduct,
        mulVec, negKM]
    have hn : ∑ j : Fin k, (if false then (1 : ℤ) else -1) *
        (negKM (finSumFinEquiv (Sum.inr j))) ^ 2 = -(k : ℤ) := by
      simp [negKM]
    rw [hp, hn, hk]
    ring
  exact ⟨h1, h2, h3⟩

/-- Kronheimer–Mrowka monopole genus lower bound (Thm. 2.4.9, Nicolaescu §2.4.2): for `d > 3`,
the SW `C⁰` curvature bound on a neck-stretched metric with constant scalar curvature
`s₀ = 8π(1 - g)/V` implies `thomGenus d ≤ g`. -/
theorem km_monopole_genus_lower_bound {d g : ℤ} {V s0 psi_sq_max F_bound : ℝ}
    (hd : 3 < d) (hV : 0 < V) (hs0 : s0 = (8 * Real.pi / V) * (1 - (g : ℝ)))
    (hpsi : psi_sq_max ≤ max 0 (-2 * s0))
    (hFA : F_bound ≤ (1 / 4 : ℝ) * psi_sq_max)
    (hch : ((d * (d - 3) : ℤ) : ℝ) ≤ (1 / (2 * Real.pi)) * (V * F_bound)) :
    thomGenus d ≤ g := by
  have hd_pos : (0 : ℝ) < ((d * (d - 3) : ℤ) : ℝ) := by
    have hd0 : 0 < d := lt_trans (by norm_num) hd
    have hd3 : 0 < d - 3 := sub_pos.mpr hd
    exact_mod_cast mul_pos hd0 hd3
  have hg_gt_one : 1 ≤ g := by
    by_contra hg0
    have hgle : (g : ℝ) ≤ 0 := by
      have : g ≤ 0 := by omega
      exact_mod_cast this
    have hs0_pos : 0 < s0 := by
      rw [hs0]
      exact mul_pos (div_pos (by positivity) hV) (by linarith)
    have hmax0 : max 0 (-2 * s0) = 0 := max_eq_left (by linarith)
    rw [hmax0] at hpsi
    have hF_nonpos : F_bound ≤ 0 := by linarith [hFA, hpsi]
    have hrhs : (1 / (2 * Real.pi)) * (V * F_bound) ≤ 0 := by
      have hpi : 0 < (1 / (2 * Real.pi)) := by positivity
      have hVF : V * F_bound ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hV.le hF_nonpos
      exact mul_nonpos_of_nonneg_of_nonpos hpi.le hVF
    linarith
  have hg1_nonneg : (0 : ℝ) ≤ (g : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg_gt_one
    linarith
  have hs0_neg : -2 * s0 = (16 * Real.pi / V) * ((g : ℝ) - 1) := by
    rw [hs0]; ring
  have hmax1 : max 0 (-2 * s0) = (16 * Real.pi / V) * ((g : ℝ) - 1) := by
    rw [hs0_neg, max_eq_right]
    exact mul_nonneg (div_nonneg (by positivity) hV.le) hg1_nonneg
  rw [hmax1] at hpsi
  have hF_bound' : F_bound ≤ (4 * Real.pi / V) * ((g : ℝ) - 1) := by
    have h1 : (1 / 4 : ℝ) * psi_sq_max ≤ (1 / 4 : ℝ) * ((16 * Real.pi / V) * ((g : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hpsi (by norm_num)
    have h2 : (1 / 4 : ℝ) * ((16 * Real.pi / V) * ((g : ℝ) - 1)) = (4 * Real.pi / V) * ((g : ℝ) - 1) := by
      ring
    exact hFA.trans (h1.trans_eq h2)
  have hVne : V ≠ 0 := hV.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hstep : (1 / (2 * Real.pi)) * (V * F_bound) ≤ 2 * ((g : ℝ) - 1) := by
    have h1 : V * F_bound ≤ V * ((4 * Real.pi / V) * ((g : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hF_bound' hV.le
    have h2 : V * ((4 * Real.pi / V) * ((g : ℝ) - 1)) = 4 * Real.pi * ((g : ℝ) - 1) := by
      field_simp [hVne]
    have h3 : (1 / (2 * Real.pi)) * (V * F_bound) ≤ (1 / (2 * Real.pi)) * (4 * Real.pi * ((g : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (h1.trans_eq h2) (by positivity)
    have h4 : (1 / (2 * Real.pi)) * (4 * Real.pi * ((g : ℝ) - 1)) = 2 * ((g : ℝ) - 1) := by
      field_simp [hpine]
      ring
    exact h3.trans_eq h4
  have hreal : ((d * (d - 3) : ℤ) : ℝ) ≤ 2 * ((g : ℝ) - 1) := hch.trans hstep
  have hint : d * (d - 3) ≤ 2 * (g - 1) := by exact_mod_cast hreal
  unfold thomGenus
  have hm := Int.mul_ediv_cancel' (two_dvd_mul_sub_three d)
  omega

/-- Thom conjecture equality combining algebraic curve upper bound `g_min ≤ thomGenus d`
and monopole lower bound `thomGenus d ≤ g_min`. -/
theorem thom_genus_equality_of_upper_and_lower {d g_min : ℤ}
    (hupper : g_min ≤ thomGenus d) (hlower : thomGenus d ≤ g_min) :
    g_min = thomGenus d :=
  le_antisymm hupper hlower

end VirtualDimAndThomGenus

/-!
## Section 5: Constructive Elkies Finite-Lattice Invariant `Θ(q)` (Thm. 2.4.16)
-/

section ElkiesInvariant

open IntegralUnimodularForm

/-- Finite set of characteristic vectors `x` with `q(x) ≥ q(w₀)` for a negative-definite
integral unimodular form `q` (bounded above in `(-q.mat)`-norm by `(-q).eval w₀`). -/
def elkiesCandidateSet {n : ℕ} (q : IntegralUnimodularForm n)
    (_hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) : Set (Fin n → ℤ) :=
  let w₀ := Classical.choose q.exists_characteristic
  { x : Fin n → ℤ | q.IsCharacteristic x ∧ q.eval w₀ ≤ q.eval x }

private theorem neg_mat_posDef_int {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) : (-q.mat).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos q.neg.isSymm fun x hx => ?_
  let xR : Fin n → ℝ := fun i => (x i : ℝ)
  have hxR : xR ≠ 0 := by
    intro h
    apply hx
    ext i
    exact Int.cast_injective (α := ℝ) (by simpa [xR] using congr_fun h i)
  have hposR : 0 < star xR ⬝ᵥ ((-q.mat).map (Int.castRingHom ℝ) *ᵥ xR) :=
    hneg.dotProduct_mulVec_pos hxR
  have hcast : ((star x ⬝ᵥ (-q.mat) *ᵥ x : ℤ) : ℝ) =
      star xR ⬝ᵥ ((-q.mat).map (Int.castRingHom ℝ) *ᵥ xR) := by
    simp [dotProduct, mulVec, xR]
  rw [← hcast] at hposR
  exact_mod_cast hposR

theorem elkiesCandidateSet_finite {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) :
    (elkiesCandidateSet q hneg).Finite := by
  let w₀ := Classical.choose q.exists_characteristic
  have hpos_int : (-q.mat).PosDef := neg_mat_posDef_int q hneg
  refine (Matrix.PosDef.finite_setOfPred_dotProduct_mulVec_le hpos_int (-q.eval w₀)).subset ?_
  rintro x ⟨_, hle⟩
  change x ⬝ᵥ (-q.mat) *ᵥ x ≤ -q.eval w₀
  have hxeq : x ⬝ᵥ (-q.mat) *ᵥ x = -q.eval x := by
    change q.neg.eval x = -q.eval x
    exact q.neg_eval x
  rw [hxeq]
  linarith [hle]

theorem elkiesCandidateSet_nonempty {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) :
    (elkiesCandidateSet q hneg).Nonempty :=
  ⟨Classical.choose q.exists_characteristic,
    Classical.choose_spec q.exists_characteristic, le_refl _⟩

/-- Maximum self-pairing `max { q(x, x) | x characteristic }` for negative-definite `q`. -/
def elkiesMaxCharSquare {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) : ℤ :=
  ((elkiesCandidateSet_finite q hneg).toFinset.image q.eval).max' <|
    (elkiesCandidateSet_nonempty q hneg).image q.eval |>.imp fun _ hx => by
      rcases hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image_of_mem q.eval ((Set.Finite.mem_toFinset _).mpr hy)

/-- Elkies' lattice invariant `Θ(q) := rank(q) + max { q(x, x) | x characteristic }`
(Nicolaescu Thm. 2.4.16). -/
def elkiesTheta {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) : ℤ :=
  (n : ℤ) + elkiesMaxCharSquare q hneg

theorem elkiesTheta_spec {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) :
    (∃ x : Fin n → ℤ, q.IsCharacteristic x ∧ elkiesTheta q hneg = (n : ℤ) + q.eval x) ∧
      ∀ y : Fin n → ℤ, q.IsCharacteristic y → (n : ℤ) + q.eval y ≤ elkiesTheta q hneg := by
  let S := (elkiesCandidateSet_finite q hneg).toFinset.image q.eval
  have hSne : S.Nonempty := (elkiesCandidateSet_nonempty q hneg).image q.eval |>.imp fun _ hx => by
    rcases hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image_of_mem q.eval ((Set.Finite.mem_toFinset _).mpr hy)
  have hmax_mem : elkiesMaxCharSquare q hneg ∈ S := Finset.max'_mem S hSne
  rcases Finset.mem_image.mp hmax_mem with ⟨x, hxmem, hxeq⟩
  have hxchar : q.IsCharacteristic x := ((Set.Finite.mem_toFinset _).mp hxmem).1
  refine ⟨⟨x, hxchar, by simp [elkiesTheta, hxeq]⟩, fun y hy => ?_⟩
  let w₀ := Classical.choose q.exists_characteristic
  have hw₀mem : q.eval w₀ ∈ S :=
    Finset.mem_image_of_mem q.eval
      ((Set.Finite.mem_toFinset _).mpr ⟨Classical.choose_spec q.exists_characteristic, le_refl _⟩)
  by_cases hcmp : q.eval w₀ ≤ q.eval y
  · have hymem : q.eval y ∈ S :=
      Finset.mem_image_of_mem q.eval ((Set.Finite.mem_toFinset _).mpr ⟨hy, hcmp⟩)
    have hle : q.eval y ≤ elkiesMaxCharSquare q hneg := Finset.le_max' S _ hymem
    unfold elkiesTheta
    linarith
  · have hle : q.eval y ≤ elkiesMaxCharSquare q hneg :=
      le_trans (le_of_not_ge hcmp) (Finset.le_max' S _ hw₀mem)
    unfold elkiesTheta
    linarith

theorem elkiesTheta_le_rank {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) :
    elkiesTheta q hneg ≤ (n : ℤ) := by
  rcases (elkiesTheta_spec q hneg).1 with ⟨x, _, hθ⟩
  have hpos_int : (-q.mat).PosDef := neg_mat_posDef_int q hneg
  have hnonpos : q.eval x ≤ 0 := by
    have hnn : 0 ≤ x ⬝ᵥ (-q.mat) *ᵥ x := hpos_int.posSemidef.dotProduct_mulVec_nonneg x
    have hxeq : x ⬝ᵥ (-q.mat) *ᵥ x = -q.eval x := by
      change q.neg.eval x = -q.eval x
      exact q.neg_eval x
    linarith
  linarith

theorem elkiesTheta_eq_rank_iff_isEven {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) :
    elkiesTheta q hneg = (n : ℤ) ↔ q.IsEven := by
  constructor
  · intro hθ
    rcases (elkiesTheta_spec q hneg).1 with ⟨x, hxchar, hxeq⟩
    have hx0 : q.eval x = 0 := by linarith
    have hpos_int : (-q.mat).PosDef := neg_mat_posDef_int q hneg
    have hxzero : x = 0 := by
      by_contra hne
      have hpos : 0 < star x ⬝ᵥ (-q.mat) *ᵥ x := hpos_int.dotProduct_mulVec_pos hne
      have hxeq' : star x ⬝ᵥ (-q.mat) *ᵥ x = -q.eval x := by
        change q.neg.eval x = -q.eval x
        exact q.neg_eval x
      linarith
    subst hxzero
    exact (q.isEven_iff_characteristic_zero).mpr hxchar
  · intro hev
    have h0char : q.IsCharacteristic 0 := (q.isEven_iff_characteristic_zero).mp hev
    have hge : (n : ℤ) ≤ elkiesTheta q hneg := by
      simpa [q.eval_zero] using (elkiesTheta_spec q hneg).2 0 h0char
    exact le_antisymm (elkiesTheta_le_rank q hneg) hge

theorem eight_dvd_elkiesTheta_of_vanDerBlij {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef) (hvdb : IsVanDerBlij q) :
    (8 : ℤ) ∣ elkiesTheta q hneg := by
  rcases (elkiesTheta_spec q hneg).1 with ⟨x, hxchar, hxeq⟩
  have hmod := hvdb x hxchar
  rw [signature_of_negDef q hneg] at hmod
  rw [hxeq]
  have hmod0 : (n : ℤ) + q.eval x ≡ 0 [ZMOD 8] := by
    simpa [add_neg_cancel] using hmod.add_left (n : ℤ)
  simpa using Int.modEq_iff_dvd.mp hmod0.symm

private theorem diagonal_one_real_posDef (n : ℕ) :
    (Matrix.diagonal (fun _ : Fin n => (1 : ℝ))).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_diagonal_of_self_adjoint _ (funext fun _ => rfl)) fun x hx => ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  simp only [star_trivial, dotProduct, Matrix.mulVec_diagonal, one_mul]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem elkiesTheta_diagNeg_eq_zero (n : ℕ) :
    let q := diagonalUnimodular (fun _ : Fin n => false)
    elkiesTheta q (by
      have hm : (-q.mat).map (Int.castRingHom ℝ) = Matrix.diagonal (fun _ => (1 : ℝ)) := by
        ext i j
        simp [q, diagonalUnimodular, Matrix.diagonal_apply, Matrix.one_apply]
      rw [hm]
      exact diagonal_one_real_posDef n) = 0 := by
  intro q
  have hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef := by
    have hm : (-q.mat).map (Int.castRingHom ℝ) = Matrix.diagonal (fun _ => (1 : ℝ)) := by
      ext i j
      simp [q, diagonalUnimodular, Matrix.diagonal_apply, Matrix.one_apply]
    rw [hm]
    exact diagonal_one_real_posDef n
  have hchar1 : q.IsCharacteristic (fun _ => 1) := by
    rw [diagonalUnimodular_isCharacteristic_iff]
    intro _; exact odd_one
  have heval1 : q.eval (fun _ => 1) = -(n : ℤ) := by
    rw [diagonalUnimodular_eval]
    simp
  have hge : 0 ≤ elkiesTheta q hneg := by
    have := (elkiesTheta_spec q hneg).2 (fun _ => 1) hchar1
    linarith
  rcases (elkiesTheta_spec q hneg).1 with ⟨x, hxchar, hxeq⟩
  have hodd := (diagonalUnimodular_isCharacteristic_iff _ x).mp hxchar
  have hxle : q.eval x ≤ -(n : ℤ) := by
    rw [diagonalUnimodular_eval]
    have hterm : ∀ i : Fin n, (if false then (1 : ℤ) else -1) * x i ^ 2 ≤ -1 := by
      intro i
      rcases hodd i with ⟨k, hk⟩
      have hsq : 1 ≤ x i ^ 2 := by
        rw [hk]
        have hkk : 0 ≤ k * (k + 1) := by
          rcases le_or_gt 0 k with hk0 | hk0
          · positivity
          · have hk1 : k + 1 ≤ 0 := by omega
            exact mul_nonneg_of_nonpos_of_nonpos hk0.le hk1
        nlinarith [hkk]
      simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
      linarith [hsq]
    calc
      ∑ i : Fin n, (if false then (1 : ℤ) else -1) * x i ^ 2 ≤ ∑ _i : Fin n, (-1 : ℤ) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = -(n : ℤ) := by simp
  have hle : elkiesTheta q hneg ≤ 0 := by linarith [hxeq, hxle]
  exact le_antisymm hle hge

theorem elkiesTheta_negE8_eq_eight :
    elkiesTheta e8Form.neg (by
      have hm : (-e8Form.neg.mat).map (Int.castRingHom ℝ) =
          e8Matrix.map (Int.castRingHom ℝ) := by
        simp [IntegralUnimodularForm.neg, e8Form]
      rw [hm]
      exact e8Matrix_posDef_real) = 8 := by
  have hev : e8Form.neg.IsEven := by
    intro x
    rw [e8Form.neg_eval]
    exact (e8Form_isEven x).neg
  exact (elkiesTheta_eq_rank_iff_isEven e8Form.neg _).mpr hev

/-- Elkies nonnegativity `Θ(q) ≥ 0` proved constructively for every negative-definite form `q`
that is even or `ℤ`-isometric to the diagonal form `⟨-1⟩^n`. -/
theorem elkiesTheta_nonneg_of_diag_or_even {n : ℕ} (q : IntegralUnimodularForm n)
    (hneg : ((-q.mat).map (Int.castRingHom ℝ)).PosDef)
    (hclass : q.IsEven ∨ q.IsIso (diagonalUnimodular (fun _ : Fin n => false))) :
    0 ≤ elkiesTheta q hneg := by
  rcases hclass with hev | hiso
  · rw [(elkiesTheta_eq_rank_iff_isEven q hneg).mpr hev]
    omega
  · rcases hiso with ⟨T, hdet, hT⟩
    let w : Fin n → ℤ := T *ᵥ (fun _ => 1)
    have hdiag_char : (diagonalUnimodular (fun _ : Fin n => false)).IsCharacteristic (fun _ => 1) := by
      rw [diagonalUnimodular_isCharacteristic_iff]; intro _; exact odd_one
    have hw_char : q.IsCharacteristic w :=
      (q.isCharacteristic_isIso T hdet hT (fun _ => 1)).mp hdiag_char
    have hw_eval : q.eval w = -(n : ℤ) := by
      have hev1 := q.isIso_eval T hT (fun _ => 1)
      rw [← hev1, diagonalUnimodular_eval]
      simp
    have hge : (n : ℤ) + q.eval w ≤ elkiesTheta q hneg := (elkiesTheta_spec q hneg).2 w hw_char
    rw [hw_eval] at hge
    omega

end ElkiesInvariant

/-!
## Section 6: Kähler Vortex Degree Bound `0 ≤ deg_ω L ≤ deg_ω K_M` (Prop. 3.2.6)
-/

section KahlerDegreeBound

/-- Integrated Kähler Seiberg–Witten chamber relation (Nicolaescu §3.2.2, Prop. 3.2.6), tracking
the volume `volM > 0`, degrees `degL` and `degKM`, and the Kähler vortex decoupling equations
for perturbation parameter `t`. -/
structure KahlerDegreeSetup where
  /-- Kähler volume `vol(M) > 0`. -/
  volM : ℝ
  volM_pos : 0 < volM
  /-- Kähler degree `deg_ω(L)`. -/
  degL : ℝ
  /-- Canonical bundle degree `deg_ω(K_M)`. -/
  degKM : ℝ
  /-- Integrated vortex branch predicate at perturbation `t` (`α ≠ 0` vs `β ≠ 0`). -/
  hasAlphaVortex : ℝ → Prop
  hasBetaVortex : ℝ → Prop
  /-- When `α ≠ 0` at `t`, holomorphic section positivity gives `0 ≤ degL` and
  `(16π / volM) * degL ≤ t` (since `∫ |α|² > 0` and `β = 0`). -/
  alpha_vortex_bound : ∀ t : ℝ, hasAlphaVortex t →
    0 ≤ degL ∧ (16 * Real.pi / volM) * degL ≤ t
  /-- When `β ≠ 0` at `t`, dual holomorphic section positivity gives `degL ≤ degKM` and
  `t ≤ (16π / volM) * degL` (since `∫ |β|² > 0` and `α = 0`). -/
  beta_vortex_bound : ∀ t : ℝ, hasBetaVortex t →
    degL ≤ degKM ∧ t ≤ (16 * Real.pi / volM) * degL
  /-- For any `t ≠ (16π / volM) * degL` with a vortex solution, either `α ≠ 0` or `β ≠ 0`. -/
  hasSolution : ℝ → Prop
  solution_dichotomy : ∀ t : ℝ, t ≠ (16 * Real.pi / volM) * degL → hasSolution t →
    hasAlphaVortex t ∨ hasBetaVortex t

/-- Closed `T17` constructive inhabitant for `KahlerDegreeSetup` (K3 / trivial-bundle baseline). -/
def canonicalKahlerDegreeSetup : KahlerDegreeSetup where
  volM := 1
  volM_pos := one_pos
  degL := 0
  degKM := 0
  hasAlphaVortex := fun t => 0 ≤ t
  hasBetaVortex := fun t => t ≤ 0
  alpha_vortex_bound := fun t ht => ⟨le_refl 0, by simpa using ht⟩
  beta_vortex_bound := fun t ht => ⟨le_refl 0, by simpa using ht⟩
  hasSolution := fun _ => True
  solution_dichotomy := fun t _ _ => le_total 0 t

instance : Inhabited KahlerDegreeSetup := ⟨canonicalKahlerDegreeSetup⟩

/-- For `t > (16π / volM) * degL`, any vortex solution forces `α ≠ 0` and hence `0 ≤ degL`. -/
theorem kahler_vortex_alpha_of_large_t (S : KahlerDegreeSetup) {t : ℝ}
    (ht : (16 * Real.pi / S.volM) * S.degL < t) (hsol : S.hasSolution t) :
    S.hasAlphaVortex t ∧ 0 ≤ S.degL := by
  have hne : t ≠ (16 * Real.pi / S.volM) * S.degL := ne_of_gt ht
  rcases S.solution_dichotomy t hne hsol with ha | hb
  · exact ⟨ha, (S.alpha_vortex_bound t ha).1⟩
  · exfalso
    have hble := (S.beta_vortex_bound t hb).2
    linarith

/-- For `t < (16π / volM) * degL`, any vortex solution forces `β ≠ 0` and hence `degL ≤ degKM`. -/
theorem kahler_vortex_beta_of_small_t (S : KahlerDegreeSetup) {t : ℝ}
    (ht : t < (16 * Real.pi / S.volM) * S.degL) (hsol : S.hasSolution t) :
    S.hasBetaVortex t ∧ S.degL ≤ S.degKM := by
  have hne : t ≠ (16 * Real.pi / S.volM) * S.degL := ne_of_lt ht
  rcases S.solution_dichotomy t hne hsol with ha | hb
  · exfalso
    have hale := (S.alpha_vortex_bound t ha).2
    linarith
  · exact ⟨hb, (S.beta_vortex_bound t hb).1⟩

/-- Kähler Seiberg–Witten degree bound (Nicolaescu Prop. 3.2.6): existence of vortices in both
chambers `t₊ > (16π / volM) * degL` and `t₋ < (16π / volM) * degL` forces
`0 ≤ deg_ω(L) ≤ deg_ω(K_M)`. -/
theorem kahler_sw_degree_bound (S : KahlerDegreeSetup) {tPlus tMinus : ℝ}
    (htPlus : (16 * Real.pi / S.volM) * S.degL < tPlus) (hsolPlus : S.hasSolution tPlus)
    (htMinus : tMinus < (16 * Real.pi / S.volM) * S.degL) (hsolMinus : S.hasSolution tMinus) :
    0 ≤ S.degL ∧ S.degL ≤ S.degKM :=
  ⟨(kahler_vortex_alpha_of_large_t S htPlus hsolPlus).2,
   (kahler_vortex_beta_of_small_t S htMinus hsolMinus).2⟩

end KahlerDegreeBound

end

end InfoGeometry.Topology.FourManifoldIntersectionForms
