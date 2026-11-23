/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# InfoGeometry.Arithmetic.AlpogeDeligneFrobeniusBoundBridge

Lean formalization of selected finite algebraic and scalar-analytic estimates
motivated by L. Alpöge's short sign-only proof of Deligne's bound for Frobenius
eigenvalues (`hexagon:2611.00789v1`, Sections 3–5, 7–8). The results below
are not a formalization of the geometric input or of Deligne's theorem itself:
in particular, no scheme, constructible sheaf, Frobenius action on étale
cohomology, or weak-Lefschetz theorem is constructed here. The exact conditional
scope of the scalar Gysin and purity statements is recorded below.

1. **Lemma 2 (Positive-Multiplicity Power-Sum Spectral-Radius Squeeze, §3)**:
   - `powSum_spectralRadius_le_of_bound`: if distinct nonzero `μ : Fin s → ℂ` with
     positive natural multiplicities `m : Fin s → ℕ` (`∀ j, 0 < m j`) satisfy
     `‖∑ j, (m j : ℂ) * (μ j) ^ n‖ ≤ C * B ^ n` for all `n ≥ 1`, then `‖μ j‖ ≤ B`
     for every `j` (proved directly via Lagrange/Vandermonde polynomial annihilation
     with zero complex-analytic pole machinery).
   - `rpow_squeeze_of_tensorPower_bound`: if `‖α‖ ^ (k * e k) ≤ q ^ (e k * (k * a + c k))`
     along a cofinal sequence with `c k / k → 0`, then `‖α‖ ≤ q ^ a`.
2. **Lemma 3 (Path Character-Sum Parseval / Cauchy–Schwarz Estimate, §4)**:
   - `fourierKernel_parseval_sq`: for a nontrivial additive character `ψ : E → ℂ`
     (`|ψ x| = 1`, `∑ y, ψ y = 0`), nondegenerate bilinear form `b : A →ₗ[E] A →ₗ[E] E`,
     and `h ≠ 0`, the kernel `K(x, y) = ψ (h * b x y)` satisfies the exact Parseval
     identity `∑ x, ‖∑ y, K x y * v y‖ ^ 2 = (Fintype.card A : ℝ) * ∑ y, ‖v y‖ ^ 2`.
   - `pathCharacterSum_pairing_unitTerminal_norm_sq_le`: for `m` nondegenerate bilinear
     kernels and `m + 1` site weights bounded by `T`, the endpoint-weighted path sum
     (constant-one terminal vector) has squared norm at most
     `T ^ (2 * (m + 1)) * (Fintype.card A : ℝ) ^ (m + 2)`.
   - `nearestNeighborPathSum_eq_pathPropagator` identifies that recursive operator with
     the literal sum over `Fin (m + 1) → A` vertex tuples, and
     `nearestNeighborPathSum_norm_sq_le` transfers the bound to that sum.
   - `pathPropagator_eq_pathTransferProduct_mulVec` represents every edge as an
     actual matrix on `A` and identifies the chain with their ordered matrix product
     acting on the terminal vector. The state-space dimension is `Fintype.card A`,
     independent of path length; `pathTransferProduct_norm_le` bounds the product
     norm by the product of local operator norms, with no uniform-in-length claim.
   - `pathCharacterSum_pairing_norm_le`: allows an additional bounded terminal vector
     and gives the corresponding looser bound with one extra factor of `T`.
3. **Section 7 Remainder Decomposition (`Q * N - M ^ k`)**:
   - `characterOrthogonality_indicator`: `∑ h : E, ψ (h * x) = if x = 0 then |E| else 0`.
   - `remainder_eq_sum_nonzero_characters`: splits the `h = 0` term (`M ^ k`) from
     `Q * N`, expressing `R = Q * N - M ^ k` as the sum over `h ≠ 0`.
   - `nearestNeighborRemainder_eq_character_path_sums` identifies this remainder
     for the explicit nearest-neighbor path hypersurface; its finite norm bound is
     `nearestNeighborRemainder_norm_sq_le`. Neither theorem supplies positive
     spectral residues or a Frobenius trace interpretation.
4. **Scalar Gysin-style alternating-sum identity and Example 5 numerical instance**:
   - `gysin_alternating_trace_telescoping`: for scalar sequences `tX`, `tY` and
     scalar `tK`, the stated shift and boundary equations imply the finite
     alternating-sum identity. These inputs are not constructed from cohomology
     groups or Gysin morphisms in this file.
     The indices are relative: `tX b` represents degree `D + b` on `X`, while
     `tY a` represents degree `D - 1 + a` on `Y`. Thus `tY a = tX (a + 1)`
     encodes the absolute Gysin degree shift `j ↦ j + 2`, not a degree-`+1`
     Gysin map.
   - `example5_conic_remainder`: a polynomial identity for `r` and `n`; it does
     not construct or prove a geometric example on `𝔸¹`.
5. **Scalar purity squeeze patterned on Poincaré duality (Section 8)**:
   - `poincareDuality_purity_eq`: `‖α‖ ≤ q ^ ((w + i) / 2)` together with the dual
     bound `‖q ^ d / α‖ ≤ q ^ ((-w + 2 * d - i) / 2)` forces exact purity
     `‖α‖ = q ^ ((w + i) / 2)`.

Note on scope: the pinned Mathlib source does define the pro-étale sheaf
`Scheme.ellAdicSheaf` and its cohomology `Scheme.EllAdicCohomology` in
`Mathlib.AlgebraicGeometry.Sites.ElladicCohomology`. Its module documentation
states that comparison with the classical étale-cohomology definition remains
future work. This file does not use that carrier. In particular, its Gysin
argument is an identity on supplied scalar trace sequences `tX` and `tY`, and
its purity theorem assumes both scalar eigenvalue-norm bounds. It does not derive
compactly supported cohomology of constructible `ℓ`-adic sheaves, a Frobenius
action, the Grothendieck–Lefschetz trace formula, Artin vanishing, or affine weak
Lefschetz (Theorem 7 / Lemma 8) from scheme geometry. The separate repository
`LefschetzSL2` package is an abstract real linear-operator representation and
does not supply that weak-Lefschetz map or its cohomological range theorem.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.AlpogeDeligneFrobeniusBoundBridge

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Filter Topology Polynomial

/-! ## 1. Section 3 / Lemma 2: Positive-multiplicity power-sum spectral-radius squeeze -/

/-- **Lemma 2 (Core Power-Sum Spectral-Radius Bound)**:
If distinct complex numbers `μ : Fin s → ℂ` with strictly positive natural
multiplicities `m : Fin s → ℕ` satisfy `‖∑ j, (m j : ℂ) * (μ j) ^ n‖ ≤ C * B ^ n`
for all `n ≥ 1` (with `0 ≤ C` and `0 < B`), then every `μ j` satisfies `‖μ j‖ ≤ B`. -/
theorem powSum_spectralRadius_le_of_bound
    {s : ℕ} (μ : Fin s → ℂ) (m : Fin s → ℕ)
    (hinj : Function.Injective μ) (hm : ∀ j, 0 < m j)
    {C B : ℝ} (hB : 0 < B)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ j : Fin s, (m j : ℂ) * (μ j) ^ n‖ ≤ C * B ^ n) :
    ∀ j : Fin s, ‖μ j‖ ≤ B := by
  by_contra hnot
  push Not at hnot
  obtain ⟨j₁, hj₁⟩ := hnot
  have hne : (Finset.univ : Finset (Fin s)).Nonempty := ⟨j₁, Finset.mem_univ _⟩
  obtain ⟨j₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖μ j‖) hne
  let M : ℝ := ‖μ j₀‖
  have hBM : B < M := lt_of_lt_of_le hj₁ (hmax j₁ (Finset.mem_univ _))
  have hMpos : 0 < M := lt_trans hB hBM
  have hMne : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hMpos)
  let lam : Fin s → ℂ := fun j => μ j / (M : ℂ)
  have hlam_inj : Function.Injective lam := by
    intro a b hab
    exact hinj (div_left_inj' hMne |>.mp hab)
  have hlam_j0_norm : ‖lam j₀‖ = 1 := by
    simp [lam, Complex.norm_real, M, div_self hMpos.ne']
  have hratio_lt : B / M < 1 := (div_lt_one hMpos).mpr hBM
  have hratio_nonneg : 0 ≤ B / M := div_nonneg hB.le hMpos.le
  -- Normalized power sums tend to 0 as n → ∞
  have hS_tendsto : Tendsto (fun n : ℕ => ∑ j : Fin s, (m j : ℂ) * (lam j) ^ n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero_norm' (a := fun n => C * (B / M) ^ n) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      have hpull :
          (∑ j : Fin s, (m j : ℂ) * (lam j) ^ n) =
            (∑ j : Fin s, (m j : ℂ) * (μ j) ^ n) / (M : ℂ) ^ n := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [lam, div_pow, mul_div_assoc]
      rw [hpull, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hMpos.le,
        div_pow, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hbound n hn) (pow_nonneg hMpos.le n)
    · have hpow : Tendsto (fun n : ℕ => (B / M) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt
      simpa using hpow.const_mul C
  -- Annihilator polynomial P(X) = ∏_{i ≠ j₀} (X - lam i)
  let P : ℂ[X] := ∏ i ∈ Finset.univ.erase j₀, (X - Polynomial.C (lam i))
  have hP_eval_j0 : P.eval (lam j₀) ≠ 0 := by
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i hi => by
      simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact fun h => (Finset.ne_of_mem_erase hi) (hlam_inj h.symm)
  have hP_eval_other : ∀ j : Fin s, j ≠ j₀ → P.eval (lam j) = 0 := by
    intro j hj
    rw [eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      (by simp)
  -- Express (m j₀) * P(lam j₀) * (lam j₀)^n as a finite linear combination of shifted sums
  have hlin : ∀ n : ℕ,
      (m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n =
        ∑ r ∈ Finset.range (P.natDegree + 1),
          P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)) := by
    intro n
    have h1 :
        ∑ r ∈ Finset.range (P.natDegree + 1),
          P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)) =
        ∑ j : Fin s, (m j : ℂ) * P.eval (lam j) * (lam j) ^ n := by
      calc
        ∑ r ∈ Finset.range (P.natDegree + 1),
            P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r))
            = ∑ r ∈ Finset.range (P.natDegree + 1),
                ∑ j : Fin s, P.coeff r * ((m j : ℂ) * (lam j) ^ (n + r)) := by
              refine Finset.sum_congr rfl fun r _ => Finset.mul_sum ..
        _ = ∑ j : Fin s, ∑ r ∈ Finset.range (P.natDegree + 1),
              P.coeff r * ((m j : ℂ) * (lam j) ^ (n + r)) := Finset.sum_comm
        _ = ∑ j : Fin s, (m j : ℂ) * P.eval (lam j) * (lam j) ^ n := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [pow_add]
              ring
    rw [h1, Finset.sum_eq_single j₀]
    · intro j _ hj
      rw [hP_eval_other j hj, mul_zero, zero_mul]
    · intro hmem
      exact (hmem (Finset.mem_univ j₀)).elim
  -- RHS tends to 0 as n → ∞, so LHS norm (which is a positive constant!) tends to 0
  have hconst_tendsto :
      Tendsto (fun n : ℕ => ‖(m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n‖) atTop (𝓝 0) := by
    have hRHS :
        Tendsto (fun n : ℕ => ∑ r ∈ Finset.range (P.natDegree + 1),
          P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r))) atTop (𝓝 0) := by
      have hterm : ∀ r ∈ Finset.range (P.natDegree + 1),
          Tendsto (fun n : ℕ => P.coeff r * (∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)))
            atTop (𝓝 0) := by
        intro r _
        have hshift :
            Tendsto (fun n : ℕ => ∑ j : Fin s, (m j : ℂ) * (lam j) ^ (n + r)) atTop (𝓝 0) :=
          hS_tendsto.comp (tendsto_add_atTop_nat r)
        simpa using hshift.const_mul (P.coeff r)
      simpa using tendsto_finsetSum (Finset.range (P.natDegree + 1)) hterm
    have hLHS : Tendsto (fun n : ℕ => (m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n) atTop (𝓝 0) :=
      hRHS.congr (fun n => (hlin n).symm)
    exact (tendsto_zero_iff_norm_tendsto_zero.mp hLHS)
  have hconst_eq : ∀ n : ℕ,
      ‖(m j₀ : ℂ) * P.eval (lam j₀) * (lam j₀) ^ n‖ = (m j₀ : ℝ) * ‖P.eval (lam j₀)‖ := by
    intro n
    rw [norm_mul, norm_mul, norm_pow, hlam_j0_norm, one_pow, mul_one, Complex.norm_natCast]
  have hzero : (m j₀ : ℝ) * ‖P.eval (lam j₀)‖ = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr (fun n => (hconst_eq n).symm)) hconst_tendsto
  have hpos : 0 < (m j₀ : ℝ) * ‖P.eval (lam j₀)‖ :=
    mul_pos (Nat.cast_pos.mpr (hm j₀)) (norm_pos_iff.mpr hP_eval_j0)
  exact (ne_of_gt hpos) hzero

/-- **Lemma 2 (Tensor-Power Limit Squeeze)**:
If `1 < q`, `0 ≤ x`, and along all `k ≥ 2` we have `x ^ (k * e k) ≤ q ^ (e k * (k * a + c k))`
with `1 ≤ e k` and `c k / k → 0`, then `x ≤ q ^ a`. -/
theorem rpow_squeeze_of_tensorPower_bound
    {q x a : ℝ} (hq : 1 < q) (hx : 0 ≤ x)
    (e : ℕ → ℕ) (c : ℕ → ℝ) (he : ∀ k, 2 ≤ k → 1 ≤ e k)
    (hc : Tendsto (fun k : ℕ => c k / (k : ℝ)) atTop (𝓝 0))
    (hbound : ∀ k : ℕ, 2 ≤ k →
      x ^ (k * e k) ≤ q ^ ((e k : ℝ) * ((k : ℝ) * a + c k))) :
    x ≤ q ^ a := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hstep : ∀ k : ℕ, 2 ≤ k → x ≤ q ^ (a + c k / (k : ℝ)) := by
    intro k hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hk)
    have hepos : (0 : ℝ) < (e k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (he k hk))
    have hke_pos : (0 : ℝ) < ((k * e k : ℕ) : ℝ) := by
      push_cast
      exact mul_pos hkpos hepos
    have hpow : x ^ ((k * e k : ℕ) : ℝ) ≤ (q ^ (a + c k / (k : ℝ))) ^ ((k * e k : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
      have hexp :
          (a + c k / (k : ℝ)) * ((k * e k : ℕ) : ℝ) = (e k : ℝ) * ((k : ℝ) * a + c k) := by
        push_cast
        field_simp [hkpos.ne']
      rw [hexp]
      exact hbound k hk
    exact (Real.rpow_le_rpow_iff hx (Real.rpow_nonneg hqpos.le _) hke_pos).mp hpow
  have htend : Tendsto (fun k : ℕ => q ^ (a + c k / (k : ℝ))) atTop (𝓝 (q ^ a)) := by
    have hadd : Tendsto (fun k : ℕ => a + c k / (k : ℝ)) atTop (𝓝 (a + 0)) :=
      tendsto_const_nhds.add hc
    rw [add_zero] at hadd
    have hcont : Continuous (fun y : ℝ => q ^ y) := by
      have hfun : (fun y : ℝ => q ^ y) = fun y => Real.exp (Real.log q * y) := by
        funext y
        exact Real.rpow_def_of_pos hqpos y
      rw [hfun]
      exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact hcont.continuousAt.tendsto.comp hadd
  exact ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨2, hstep⟩)

/-! ## 2. Section 4 / Lemma 3: Path character-sum Parseval & Cauchy–Schwarz estimate -/

namespace FiniteFieldAddChar

variable {E : Type*} [Field E] [Fintype E] (ψ : AddChar E ℂ) (hψ : ψ ≠ 0)

theorem map_neg (x : E) : ψ (-x) = star (ψ x) := by
  have h1 : ψ (-x) * ψ x = 1 := by
    rw [← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one]
  have h2 : star (ψ x) * ψ x = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ψ.norm_apply x]
    norm_num
  have hne : ψ x ≠ 0 := by
    intro h0
    have := ψ.norm_apply x
    rw [h0, norm_zero] at this
    norm_num at this
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem map_sub (x y : E) : ψ (x - y) = ψ x * star (ψ y) := by
  rw [sub_eq_add_neg, ψ.map_add_eq_mul, map_neg ψ]

theorem sum_mul_eq_ite [DecidableEq E] (hψ : ψ ≠ 0) (x : E) :
    (∑ h : E, ψ (h * x)) = if x = 0 then (Fintype.card E : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [ψ.map_zero_eq_one]
  · simp only [hx, ↓reduceIte]
    have hbij : (∑ h : E, ψ (h * x)) = ∑ y : E, ψ y :=
      Equiv.sum_comp (Equiv.mulRight₀ x hx) ψ
    have hsum : (∑ y : E, ψ y) = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hψ
    rw [hbij, hsum]

theorem sum_linearMap_eq_zero (hψ : ψ ≠ 0)
    {A : Type*} [AddCommGroup A] [Module E A] [Fintype A]
    (ℓ : A →ₗ[E] E) (hℓ : ℓ ≠ 0) : (∑ y : A, ψ (ℓ y)) = 0 := by
  have hex : ∃ y₀ : A, ℓ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (LinearMap.ext h)
  obtain ⟨y₀, hy₀⟩ := hex
  have hmul : ∀ c : E, ψ (c * ℓ y₀) * (∑ y : A, ψ (ℓ y)) =
      ∑ y : A, ψ (ℓ y) := by
    intro c
    rw [Finset.mul_sum]
    calc
      ∑ y : A, ψ (c * ℓ y₀) * ψ (ℓ y)
          = ∑ y : A, ψ (ℓ (c • y₀ + y)) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul, ψ.map_add_eq_mul]
      _ = ∑ y : A, ψ (ℓ y) :=
            Equiv.sum_comp (Equiv.addLeft (c • y₀)) (fun y => ψ (ℓ y))
  have hsum : (∑ c : E, ψ (c * ℓ y₀)) * (∑ y : A, ψ (ℓ y)) =
      (Fintype.card E : ℂ) * (∑ y : A, ψ (ℓ y)) := by
    rw [Finset.sum_mul]
    calc
      ∑ c : E, ψ (c * ℓ y₀) * (∑ y : A, ψ (ℓ y))
          = ∑ _c : E, ∑ y : A, ψ (ℓ y) := Finset.sum_congr rfl fun c _ => hmul c
      _ = (Fintype.card E : ℂ) * (∑ y : A, ψ (ℓ y)) := by simp
  classical
  rw [sum_mul_eq_ite ψ hψ (ℓ y₀)] at hsum
  simp only [hy₀, ↓reduceIte, zero_mul] at hsum
  have hcard : (Fintype.card E : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  exact (mul_eq_zero.mp hsum.symm).resolve_left hcard

end FiniteFieldAddChar

/-- **Lemma 3 (Parseval Identity for Nondegenerate Fourier Kernel)**:
For a right-nondegenerate bilinear form `b : A →ₗ[E] A →ₗ[E] E` and `h ≠ 0`, the Fourier
matrix `K(x, y) = ψ(h * b x y)` satisfies `‖K v‖₂² = |A| * ‖v‖₂²` identically. -/
theorem fourierKernel_parseval_sq
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0)
    (b : A →ₗ[E] A →ₗ[E] E)
    (hb : ∀ z : A, (∀ x : A, b x z = 0) → z = 0)
    {h : E} (hh : h ≠ 0) (v : A → ℂ) :
    (∑ x : A, ‖∑ y : A, ψ (h * b x y) * v y‖ ^ 2) =
      (Fintype.card A : ℝ) * (∑ y : A, ‖v y‖ ^ 2) := by
  classical
  have hC :
      ((∑ x : A, ‖∑ y : A, ψ (h * b x y) * v y‖ ^ 2 : ℝ) : ℂ) =
        ((Fintype.card A : ℝ) * (∑ y : A, ‖v y‖ ^ 2) : ℝ) := by
    push_cast
    calc
      ∑ x : A, (‖∑ y : A, ψ (h * b x y) * v y‖ : ℂ) ^ 2
          = ∑ x : A, (∑ y : A, ψ (h * b x y) * v y) *
              star (∑ z : A, ψ (h * b x z) * v z) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
            push_cast
            rfl
      _ = ∑ x : A, ∑ y : A, ∑ z : A,
            ψ (h * b x (y - z)) * (v y * star (v z)) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [star_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z _ => ?_
            calc
              ψ (h * b x y) * v y * star (ψ (h * b x z) * v z)
                  = (ψ (h * b x y) * star (ψ (h * b x z))) *
                      (v y * star (v z)) := by
                    rw [star_mul']
                    ring
              _ = ψ (h * b x y - h * b x z) * (v y * star (v z)) := by
                    rw [← FiniteFieldAddChar.map_sub ψ]
              _ = ψ (h * b x (y - z)) * (v y * star (v z)) := by
                    congr 2
                    simp [map_sub, mul_sub]
      _ = ∑ y : A, ∑ z : A,
            (∑ x : A, ψ (h * b x (y - z))) * (v y * star (v z)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ y : A, (Fintype.card A : ℂ) * (v y * star (v y)) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_eq_single y]
            · simp [ψ.map_zero_eq_one]
            · intro z _ hzy
              let ℓ : A →ₗ[E] E :=
                { toFun := fun x => h * b x (y - z)
                  map_add' := fun x₁ x₂ => by simp [mul_add]
                  map_smul' := fun c x => by simp [mul_left_comm] }
              have hℓ : ℓ ≠ 0 := by
                intro h0
                have hsub : y - z = 0 := hb (y - z) fun x => by
                  have hx : ℓ x = 0 := congrArg (fun f : A →ₗ[E] E => f x) h0
                  exact (mul_eq_zero.mp hx).resolve_left hh
                exact hzy (sub_eq_zero.mp hsub).symm
              have hzero : (∑ x : A, ψ (h * b x (y - z))) = 0 :=
                FiniteFieldAddChar.sum_linearMap_eq_zero ψ hψ ℓ hℓ
              rw [hzero, zero_mul]
            · intro hmem; exact (hmem (Finset.mem_univ y)).elim
      _ = (Fintype.card A : ℂ) * ∑ y : A, (‖v y‖ : ℂ) ^ 2 := by
            rw [← Finset.mul_sum]
            refine congrArg ((Fintype.card A : ℂ) * ·) ?_
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
            push_cast
            rfl
  exact Complex.ofReal_injective hC

/-- Diagonal multiplication by a function bounded by `T` scales the `ℓ²` norm squared
by at most `T ^ 2`. -/
theorem diag_mul_l2_sq_le
    {A : Type*} [Fintype A] (t v : A → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (ht : ∀ x : A, ‖t x‖ ≤ T) :
    (∑ x : A, ‖t x * v x‖ ^ 2) ≤ T ^ 2 * (∑ x : A, ‖v x‖ ^ 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [norm_mul, mul_pow]
  have hsq : ‖t x‖ ^ 2 ≤ T ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (t x), hT]) (ht x)
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- Recursive path-operator vector: each Fourier kernel is followed by a diagonal
weight at its destination. In the endpoint-weighted estimate the final weight acts
on the constant-one vector, producing the last site vector. -/
def pathPropagator
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (h : E) :
    (m : ℕ) → (Fin m → A →ₗ[E] A →ₗ[E] E) → (Fin m → A → ℂ) → (A → ℂ) → (A → ℂ)
  | 0, _, _, v => v
  | m + 1, b, t, v =>
      fun x => ∑ y : A, ψ (h * b 0 x y) * (t 0 y *
        pathPropagator ψ h m (fun i => b i.succ) (fun i => t i.succ) v y)

/-- The one-edge transfer matrix: its row is the source state and its column
is the destination state, with the destination site weight included. -/
def pathTransferMatrix
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A]
    [Fintype A] [DecidableEq A]
    (ψ : AddChar E ℂ) (h : E)
    (b : A →ₗ[E] A →ₗ[E] E) (t : A → ℂ) : Matrix A A ℂ :=
  fun x y => ψ (h * b x y) * t y

/-- Ordered transfer-matrix product for a finite chain. The first edge acts
after the product of the remaining edges, matching the recursive path order. -/
def pathTransferProduct
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A]
    [Fintype A] [DecidableEq A]
    (ψ : AddChar E ℂ) (h : E) :
    (m : ℕ) → (Fin m → A →ₗ[E] A →ₗ[E] E) → (Fin m → A → ℂ) → Matrix A A ℂ
  | 0, _, _ => 1
  | m + 1, b, t =>
      pathTransferMatrix ψ h (b 0) (t 0) *
        pathTransferProduct ψ h m (fun i => b i.succ) (fun i => t i.succ)

/-- The Euclidean operator norm of a finite nearest-neighbor transfer product
is bounded by the product of the local operator norms. This is the precise
submultiplicative estimate for the fixed state-space transfer representation;
it gives no length-independent bound unless the local factors themselves have
additional uniform control. -/
theorem pathTransferProduct_norm_le
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A]
    [Fintype A] [DecidableEq A]
    (ψ : AddChar E ℂ) (h : E) :
    ∀ (m : ℕ) (b : Fin m → A →ₗ[E] A →ₗ[E] E)
      (t : Fin m → A → ℂ),
      ‖pathTransferProduct ψ h m b t‖ ≤
        ∏ i : Fin m, ‖pathTransferMatrix ψ h (b i) (t i)‖ := by
  intro m
  induction m with
  | zero =>
      intro b t
      simp [pathTransferProduct]
  | succ m ih =>
      intro b t
      rw [pathTransferProduct.eq_def, Fin.prod_univ_succ]
      calc
        ‖pathTransferMatrix ψ h (b 0) (t 0) *
            pathTransferProduct ψ h m (fun i => b i.succ) (fun i => t i.succ)‖
            ≤ ‖pathTransferMatrix ψ h (b 0) (t 0)‖ *
                ‖pathTransferProduct ψ h m (fun i => b i.succ) (fun i => t i.succ)‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ ‖pathTransferMatrix ψ h (b 0) (t 0)‖ *
              (∏ i : Fin m,
                ‖pathTransferMatrix ψ h ((fun i => b i.succ) i)
                  ((fun i => t i.succ) i)‖) :=
          mul_le_mul_of_nonneg_left (ih _ _) (norm_nonneg _)

/-- The recursive nearest-neighbor path contraction is exactly an ordered product
of finite transfer matrices acting on the terminal vector. This is a genuine
matrix representation on the fixed state space `A`, including site-dependent
bilinear forms and weights; no tensor-rank or asymptotic bound is asserted. -/
theorem pathPropagator_eq_pathTransferProduct_mulVec
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A]
    [Fintype A] [DecidableEq A]
    (ψ : AddChar E ℂ) (h : E) :
    ∀ (m : ℕ) (b : Fin m → A →ₗ[E] A →ₗ[E] E)
      (t : Fin m → A → ℂ) (v : A → ℂ),
      pathPropagator ψ h m b t v =
        (pathTransferProduct ψ h m b t).mulVec v := by
  intro m
  induction m with
  | zero =>
      intro b t v
      funext x
      simp only [pathPropagator, pathTransferProduct]
      rw [Matrix.one_mulVec]
  | succ m ih =>
      intro b t v
      funext x
      simp only [pathPropagator, pathTransferProduct]
      rw [← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, pathTransferMatrix]
      apply Finset.sum_congr rfl
      intro y hy
      rw [ih]
      simp only [Matrix.mulVec, dotProduct]
      ring

/-- The literal nearest-neighbor character sum on paths with `m` edges and
`m + 1` vertices. Its edge factors use the ordered pair of consecutive vertices;
the vertex weights are kept as a separate product. -/
def nearestNeighborPathSum
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A]
    [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (h : E) (m : ℕ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E)
    (t₀ : A → ℂ) (t : Fin m → A → ℂ) : ℂ :=
  ∑ u : Fin (m + 1) → A,
    t₀ (u 0) * ∏ i : Fin m,
      (ψ (h * b i (u i.castSucc) (u i.succ)) * t i (u i.succ))

private def pathTupleEquiv {A : Type*} (m : ℕ) :
    (A × (Fin m → A)) ≃ (Fin (m + 1) → A) :=
  Fin.consEquiv (fun _ : Fin (m + 1) => A)

/-- Expanding the recursive path operator gives exactly the finite sum over
vertex tuples with consecutive bilinear edge phases. This is the typed bridge
from the path contraction estimate to the actual nearest-neighbor character sum. -/
theorem nearestNeighborPathSum_eq_pathPropagator
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A]
    [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (h : E) (m : ℕ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E)
    (t₀ : A → ℂ) (t : Fin m → A → ℂ) :
    nearestNeighborPathSum ψ h m b t₀ t =
      ∑ x : A, t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x := by
  induction m generalizing t₀ with
  | zero =>
      simp only [nearestNeighborPathSum, Fin.prod_univ_zero, mul_one, pathPropagator]
      let e := pathTupleEquiv (A := A) 0
      rw [← Equiv.sum_comp e (fun u : Fin 1 → A => t₀ (u 0))]
      calc
        (∑ p : A × (Fin 0 → A), t₀ p.1) =
            ∑ x : A, ∑ v : Fin 0 → A, t₀ x := Fintype.sum_prod_type _
        _ = ∑ x : A, t₀ x := by simp
  | succ m ih =>
      rw [nearestNeighborPathSum, pathPropagator]
      let e := pathTupleEquiv (A := A) (m := m + 1)
      have hsum :
          (∑ u : Fin (m + 2) → A,
            t₀ (u 0) * ∏ i : Fin (m + 1),
              (ψ (h * b i (u i.castSucc) (u i.succ)) * t i (u i.succ))) =
          ∑ p : A × (Fin (m + 1) → A),
            t₀ p.1 * ∏ i : Fin (m + 1),
              (ψ (h * b i ((e p) i.castSucc) ((e p) i.succ)) *
                t i ((e p) i.succ)) := by
        exact (Equiv.sum_comp e (fun u =>
          t₀ (u 0) * ∏ i : Fin (m + 1),
            (ψ (h * b i (u i.castSucc) (u i.succ)) * t i (u i.succ)))).symm
      rw [hsum, Fintype.sum_prod_type]
      dsimp [e, pathTupleEquiv]
      simp only [Fin.consEquiv_apply, Fin.cons_succ, Fin.prod_univ_succ]
      simp only [Fin.castSucc_zero']
      simp only [Fin.cons_zero]
      have hidx (a : A) (v : Fin (m + 1) → A) (i : Fin m) :
          (Fin.cons (α := fun _ : Fin (m + 2) => A) a v) i.succ.castSucc =
            v i.castSucc := by
        have h : i.succ.castSucc = i.castSucc.succ := Fin.ext (by simp)
        rw [h, Fin.cons_succ]
      simp_rw [hidx]
      have htail (x : A) :
          (∑ v : Fin (m + 1) → A,
            (ψ (h * b 0 x (v 0)) * t 0 (v 0)) *
              ∏ i : Fin m,
                (ψ (h * b i.succ (v i.castSucc) (v i.succ)) * t i.succ (v i.succ))) =
          ∑ y : A, (ψ (h * b 0 x y) * t 0 y) *
            pathPropagator ψ h m (fun i => b i.succ) (fun i => t i.succ)
              (fun _ => (1 : ℂ)) y := by
        simpa [nearestNeighborPathSum] using
          (ih (b := fun i => b i.succ)
            (t₀ := fun y => ψ (h * b 0 x y) * t 0 y)
            (t := fun i => t i.succ))
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.mul_sum, htail x]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      ring

/-- The literal finite path sum is the endpoint pairing with an ordered product
of transfer matrices on the fixed state space `A`. This exposes the exact
finite-dimensional chain representation of the nearest-neighbor sum. -/
theorem nearestNeighborPathSum_eq_transferProduct
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A]
    [Module E A] [Fintype A] [DecidableEq A]
    (ψ : AddChar E ℂ) (h : E) (m : ℕ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E)
    (t₀ : A → ℂ) (t : Fin m → A → ℂ) :
    nearestNeighborPathSum ψ h m b t₀ t =
      ∑ x : A, t₀ x *
        (pathTransferProduct ψ h m b t).mulVec (fun _ => (1 : ℂ)) x := by
  rw [nearestNeighborPathSum_eq_pathPropagator]
  apply Finset.sum_congr rfl
  intro x hx
  rw [pathPropagator_eq_pathTransferProduct_mulVec ψ h m b t (fun _ => (1 : ℂ))]

/-- **Lemma 3 (Iterated `ℓ²` Norm Bound Along a Path of Length `m`)**:
applying `m` nondegenerate Fourier kernels interlaced with `T`-bounded diagonal
weights scales the `ℓ²` norm squared by at most `(|A| * T ^ 2) ^ m`. -/
theorem pathPropagator_l2_sq_le
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) {h : E} (hh : h ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∀ (m : ℕ) (b : Fin m → A →ₗ[E] A →ₗ[E] E)
      (_hb : ∀ i z, (∀ x, b i x z = 0) → z = 0)
      (t : Fin m → A → ℂ) (_ht : ∀ i x, ‖t i x‖ ≤ T) (v : A → ℂ),
      (∑ x : A, ‖pathPropagator ψ h m b t v x‖ ^ 2) ≤
        ((Fintype.card A : ℝ) * T ^ 2) ^ m * (∑ y : A, ‖v y‖ ^ 2)
  | 0, _, _, _, _, v => by simp [pathPropagator]
  | m + 1, b, hb, t, ht, v => by
      dsimp only [pathPropagator]
      rw [fourierKernel_parseval_sq ψ hψ (b 0) (hb 0) hh]
      have hdiag := diag_mul_l2_sq_le (t 0)
        (pathPropagator ψ h m (fun i => b i.succ) (fun i => t i.succ) v) hT (ht 0)
      have hih := pathPropagator_l2_sq_le ψ hψ hh hT m
        (fun i => b i.succ) (fun i => hb i.succ)
        (fun i => t i.succ) (fun i => ht i.succ) v
      have hA : (0 : ℝ) ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
      calc
        (Fintype.card A : ℝ) *
            ∑ y : A, ‖t 0 y * pathPropagator ψ h m (fun i => b i.succ) (fun i => t i.succ) v y‖ ^ 2
            ≤ (Fintype.card A : ℝ) *
                (T ^ 2 * ∑ y : A,
                  ‖pathPropagator ψ h m (fun i => b i.succ) (fun i => t i.succ) v y‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hdiag hA
        _ ≤ (Fintype.card A : ℝ) *
              (T ^ 2 * (((Fintype.card A : ℝ) * T ^ 2) ^ m * ∑ y : A, ‖v y‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hih (sq_nonneg T)) hA
        _ = ((Fintype.card A : ℝ) * T ^ 2) ^ (m + 1) * ∑ y : A, ‖v y‖ ^ 2 := by
              rw [pow_succ']
              ring

/-- A path estimate with an additional terminal vector `v`, also bounded by `T`.
The endpoint-weighted estimate below avoids this extra terminal bound by taking `v = 1`. -/
theorem pathCharacterSum_pairing_norm_le
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) {h : E} (hh : h ≠ 0) (c : E)
    {T : ℝ} (hT : 0 ≤ T) (m : ℕ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E)
    (hb : ∀ i z, (∀ x, b i x z = 0) → z = 0)
    (t₀ : A → ℂ) (ht₀ : ∀ x, ‖t₀ x‖ ≤ T)
    (t : Fin m → A → ℂ) (ht : ∀ i x, ‖t i x‖ ≤ T)
    (v : A → ℂ) (hv : ∀ x, ‖v x‖ ≤ T) :
    ‖ψ (h * c) * ∑ x : A, t₀ x * pathPropagator ψ h m b t v x‖ ^ 2 ≤
      T ^ (2 * (m + 2)) * (Fintype.card A : ℝ) ^ (m + 2) := by
  rw [norm_mul, ψ.norm_apply, one_mul]
  have hcs :
      ‖∑ x : A, t₀ x * pathPropagator ψ h m b t v x‖ ^ 2 ≤
        (∑ x : A, ‖t₀ x‖ ^ 2) * (∑ x : A, ‖pathPropagator ψ h m b t v x‖ ^ 2) := by
    have htri :
        ‖∑ x : A, t₀ x * pathPropagator ψ h m b t v x‖ ≤
          ∑ x : A, ‖t₀ x‖ * ‖pathPropagator ψ h m b t v x‖ := by
      calc
        ‖∑ x : A, t₀ x * pathPropagator ψ h m b t v x‖
            ≤ ∑ x : A, ‖t₀ x * pathPropagator ψ h m b t v x‖ := norm_sum_le _ _
        _ = ∑ x : A, ‖t₀ x‖ * ‖pathPropagator ψ h m b t v x‖ := by
              refine Finset.sum_congr rfl fun x _ => norm_mul ..
    calc
      ‖∑ x : A, t₀ x * pathPropagator ψ h m b t v x‖ ^ 2
          ≤ (∑ x : A, ‖t₀ x‖ * ‖pathPropagator ψ h m b t v x‖) ^ 2 := by
            refine sq_le_sq' ?_ htri
            linarith [norm_nonneg (∑ x : A, t₀ x * pathPropagator ψ h m b t v x)]
      _ ≤ (∑ x : A, ‖t₀ x‖ ^ 2) * (∑ x : A, ‖pathPropagator ψ h m b t v x‖ ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have ht₀_sq : (∑ x : A, ‖t₀ x‖ ^ 2) ≤ (Fintype.card A : ℝ) * T ^ 2 := by
    calc
      (∑ x : A, ‖t₀ x‖ ^ 2) ≤ ∑ _x : A, T ^ 2 :=
        Finset.sum_le_sum fun x _ =>
          sq_le_sq' (by linarith [norm_nonneg (t₀ x), hT]) (ht₀ x)
      _ = (Fintype.card A : ℝ) * T ^ 2 := by simp
  have hv_sq : (∑ y : A, ‖v y‖ ^ 2) ≤ (Fintype.card A : ℝ) * T ^ 2 := by
    calc
      (∑ y : A, ‖v y‖ ^ 2) ≤ ∑ _y : A, T ^ 2 :=
        Finset.sum_le_sum fun y _ =>
          sq_le_sq' (by linarith [norm_nonneg (v y), hT]) (hv y)
      _ = (Fintype.card A : ℝ) * T ^ 2 := by simp
  have hprop := pathPropagator_l2_sq_le ψ hψ hh hT m b hb t ht v
  have hA : (0 : ℝ) ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hprop2 :
      (∑ x : A, ‖pathPropagator ψ h m b t v x‖ ^ 2) ≤
        ((Fintype.card A : ℝ) * T ^ 2) ^ m * ((Fintype.card A : ℝ) * T ^ 2) :=
    hprop.trans (mul_le_mul_of_nonneg_left hv_sq (pow_nonneg (mul_nonneg hA (sq_nonneg T)) m))
  calc
    ‖∑ x : A, t₀ x * pathPropagator ψ h m b t v x‖ ^ 2
        ≤ (∑ x : A, ‖t₀ x‖ ^ 2) * (∑ x : A, ‖pathPropagator ψ h m b t v x‖ ^ 2) := hcs
    _ ≤ ((Fintype.card A : ℝ) * T ^ 2) *
          (((Fintype.card A : ℝ) * T ^ 2) ^ m * ((Fintype.card A : ℝ) * T ^ 2)) :=
          mul_le_mul ht₀_sq hprop2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (mul_nonneg hA (sq_nonneg T))
    _ = T ^ (2 * (m + 2)) * (Fintype.card A : ℝ) ^ (m + 2) := by
          rw [mul_pow, pow_mul]
          ring

/-- **Endpoint-weighted path estimate**: the `m` diagonal weights account for all
`m + 1` sites when the terminal vector is constant one. In norm form the bound is
`T ^ (m + 1) * |A| ^ ((m + 2) / 2)`; the theorem states its square to avoid square
roots. -/
theorem pathCharacterSum_pairing_unitTerminal_norm_sq_le
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) {h : E} (hh : h ≠ 0) (c : E)
    {T : ℝ} (hT : 0 ≤ T) (m : ℕ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E)
    (hb : ∀ i z, (∀ x, b i x z = 0) → z = 0)
    (t₀ : A → ℂ) (ht₀ : ∀ x, ‖t₀ x‖ ≤ T)
    (t : Fin m → A → ℂ) (ht : ∀ i x, ‖t i x‖ ≤ T) :
    ‖ψ (h * c) * ∑ x : A,
        t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2 ≤
      T ^ (2 * (m + 1)) * (Fintype.card A : ℝ) ^ (m + 2) := by
  rw [norm_mul, ψ.norm_apply, one_mul]
  have hcs :
      ‖∑ x : A, t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2 ≤
        (∑ x : A, ‖t₀ x‖ ^ 2) *
          (∑ x : A, ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2) := by
    have htri :
        ‖∑ x : A, t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ≤
          ∑ x : A, ‖t₀ x‖ *
            ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ := by
      calc
        ‖∑ x : A, t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖
            ≤ ∑ x : A,
                ‖t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ := norm_sum_le _ _
        _ = ∑ x : A, ‖t₀ x‖ *
              ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ := by
                refine Finset.sum_congr rfl fun x _ => norm_mul ..
    calc
      ‖∑ x : A, t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2
          ≤ (∑ x : A, ‖t₀ x‖ *
              ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖) ^ 2 := by
                refine sq_le_sq' ?_ htri
                have hsum_nonneg :
                    0 ≤ ∑ x : A, ‖t₀ x‖ *
                      ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ :=
                  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
                linarith [norm_nonneg
                  (∑ x : A, t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x)]
      _ ≤ (∑ x : A, ‖t₀ x‖ ^ 2) *
            (∑ x : A, ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2) :=
              Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have ht₀_sq :
      (∑ x : A, ‖t₀ x‖ ^ 2) ≤ (Fintype.card A : ℝ) * T ^ 2 := by
    calc
      (∑ x : A, ‖t₀ x‖ ^ 2) ≤ ∑ _x : A, T ^ 2 :=
        Finset.sum_le_sum fun x _ =>
          sq_le_sq' (by linarith [norm_nonneg (t₀ x), hT]) (ht₀ x)
      _ = (Fintype.card A : ℝ) * T ^ 2 := by simp
  have hprop := pathPropagator_l2_sq_le ψ hψ hh hT m b hb t ht
    (fun _ => (1 : ℂ))
  have hprop' :
      (∑ x : A, ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2) ≤
        ((Fintype.card A : ℝ) * T ^ 2) ^ m * (Fintype.card A : ℝ) := by
    simpa using hprop
  have hA : (0 : ℝ) ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  calc
    ‖∑ x : A, t₀ x * pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2
        ≤ (∑ x : A, ‖t₀ x‖ ^ 2) *
            (∑ x : A, ‖pathPropagator ψ h m b t (fun _ => (1 : ℂ)) x‖ ^ 2) := hcs
    _ ≤ ((Fintype.card A : ℝ) * T ^ 2) *
          (((Fintype.card A : ℝ) * T ^ 2) ^ m * (Fintype.card A : ℝ)) :=
        mul_le_mul ht₀_sq hprop'
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (mul_nonneg hA (sq_nonneg T))
    _ = T ^ (2 * (m + 1)) * (Fintype.card A : ℝ) ^ (m + 2) := by
          rw [mul_pow, pow_mul]
          ring

/-- The recursive transfer estimate applies to the literal finite sum over
nearest-neighbor vertex configurations. This theorem packages the proved tuple
expansion with the endpoint-weighted bound; it makes no claim about a general
hypersurface sum or about a uniform-in-length operator norm. -/
theorem nearestNeighborPathSum_norm_sq_le
    {E A : Type*} [Field E] [Fintype E] [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) {h : E} (hh : h ≠ 0)
    {T : ℝ} (hT : 0 ≤ T) (m : ℕ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E)
    (hb : ∀ i z, (∀ x, b i x z = 0) → z = 0)
    (t₀ : A → ℂ) (ht₀ : ∀ x, ‖t₀ x‖ ≤ T)
    (t : Fin m → A → ℂ) (ht : ∀ i x, ‖t i x‖ ≤ T) :
    ‖nearestNeighborPathSum ψ h m b t₀ t‖ ^ 2 ≤
      T ^ (2 * (m + 1)) * (Fintype.card A : ℝ) ^ (m + 2) := by
  simpa [nearestNeighborPathSum_eq_pathPropagator] using
    (pathCharacterSum_pairing_unitTerminal_norm_sq_le ψ hψ hh (0 : E) hT m b hb
      t₀ ht₀ t ht)

/-- **Section 7 Remainder Identity (`Q * N - M ^ k`)**:
Detecting the hypersurface `{u | P u = 0}` by additive characters `ψ(h * P u)`
splits the `h = 0` term (`M ^ k`) from `Q * N`, expressing `R = Q * N - M ^ k`
as the exact sum over nonzero characters `h ∈ E \ {0}`. -/
theorem remainder_eq_sum_nonzero_characters
    {E U : Type*} [Field E] [Fintype E] [DecidableEq E] [Fintype U]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) (k : ℕ) (τ : U → ℂ) (P : (Fin k → U) → E) :
    let M : ℂ := ∑ u : U, τ u
    let N : ℂ := ∑ u : Fin k → U, if P u = 0 then (∏ i : Fin k, τ (u i)) else 0
    (Fintype.card E : ℂ) * N - M ^ k =
      ∑ h ∈ Finset.univ.erase (0 : E),
        ∑ u : Fin k → U, (∏ i : Fin k, τ (u i)) * ψ (h * P u) := by
  intro M N
  have hQN :
      (Fintype.card E : ℂ) * N =
        ∑ h : E, ∑ u : Fin k → U, (∏ i : Fin k, τ (u i)) * ψ (h * P u) := by
    dsimp [N]
    rw [Finset.mul_sum]
    calc
      ∑ u : Fin k → U, (Fintype.card E : ℂ) * (if P u = 0 then ∏ i : Fin k, τ (u i) else 0)
          = ∑ u : Fin k → U, (∏ i : Fin k, τ (u i)) * (∑ h : E, ψ (h * P u)) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [FiniteFieldAddChar.sum_mul_eq_ite ψ hψ (P u)]
            split_ifs <;> ring
      _ = ∑ u : Fin k → U, ∑ h : E, (∏ i : Fin k, τ (u i)) * ψ (h * P u) := by
            refine Finset.sum_congr rfl fun u _ => Finset.mul_sum ..
      _ = ∑ h : E, ∑ u : Fin k → U, (∏ i : Fin k, τ (u i)) * ψ (h * P u) :=
            Finset.sum_comm
  have h0 :
      (∑ u : Fin k → U, (∏ i : Fin k, τ (u i)) * ψ ((0 : E) * P u)) = M ^ k := by
    simp only [zero_mul, ψ.map_zero_eq_one, mul_one]
    dsimp [M]
    rw [← Fintype.prod_sum (fun (_ : Fin k) (u : U) => τ u)]
    simp [Finset.prod_const, Finset.card_univ]
  rw [hQN, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : E)), h0, add_sub_cancel_left]

/-- Specialize the Fourier remainder identity to a genuinely nearest-neighbor
path hypersurface. The scalar remainder is exactly the sum of the nontrivial
character-weighted path contractions; this is an algebraic identity and does
not assert a Frobenius trace interpretation or positive spectral residues. -/
theorem nearestNeighborRemainder_eq_character_path_sums
    {E A : Type*} [Field E] [Fintype E] [DecidableEq E]
    [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) (m : ℕ) (c : E)
    (τ : A → ℂ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E) :
    let M : ℂ := ∑ x : A, τ x
    let pathValue : (Fin (m + 1) → A) → E := fun u =>
      c + ∑ i : Fin m, b i (u i.castSucc) (u i.succ)
    let N : ℂ := ∑ u : Fin (m + 1) → A,
      if pathValue u = 0 then ∏ i : Fin (m + 1), τ (u i) else 0
    (Fintype.card E : ℂ) * N - M ^ (m + 1) =
      ∑ r ∈ Finset.univ.erase (0 : E), ψ (r * c) *
        nearestNeighborPathSum ψ r m b (fun x => τ x) (fun _ x => τ x) := by
  classical
  intro M pathValue N
  have hmapSum (s : Finset (Fin m)) (f : Fin m → E) :
      ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ.map_add_eq_mul, ih]
  have hphase (r : E) (u : Fin (m + 1) → A) :
      ψ (r * pathValue u) = ψ (r * c) *
        ∏ i : Fin m, ψ (r * b i (u i.castSucc) (u i.succ)) := by
    change ψ (r * (c +
      ∑ i : Fin m, b i (u i.castSucc) (u i.succ))) = _
    rw [mul_add, Finset.mul_sum, ψ.map_add_eq_mul]
    congr 1
    exact hmapSum Finset.univ (fun i => r * b i (u i.castSucc) (u i.succ))
  have hweight (u : Fin (m + 1) → A) :
      ∏ i : Fin (m + 1), τ (u i) = τ (u 0) *
        ∏ i : Fin m, τ (u i.succ) := by
    rw [Fin.prod_univ_succ]
  have hterm (r : E) (u : Fin (m + 1) → A) :
      (∏ i : Fin (m + 1), τ (u i)) * ψ (r * pathValue u) =
        ψ (r * c) * (τ (u 0) * ∏ i : Fin m,
          (ψ (r * b i (u i.castSucc) (u i.succ)) * τ (u i.succ))) := by
    rw [hweight u, hphase r u, Finset.prod_mul_distrib]
    ring
  have hpath (r : E) :
      (∑ u : Fin (m + 1) → A,
        (∏ i : Fin (m + 1), τ (u i)) * ψ (r * pathValue u)) =
      ψ (r * c) * nearestNeighborPathSum ψ r m b (fun x => τ x) (fun _ x => τ x) := by
    rw [Finset.sum_congr rfl (fun u _ => hterm r u), ← Finset.mul_sum]
    rfl
  have hrem := remainder_eq_sum_nonzero_characters ψ hψ (m + 1) τ pathValue
  dsimp [M, N] at hrem ⊢
  rw [hrem]
  refine Finset.sum_congr rfl ?_
  intro r hr
  exact hpath r

/-- Express the nontrivial-character remainder as a sum of ordered transfer-matrix
products on the fixed state space `A`. This composes the finite Fourier
decomposition with the path-to-matrix representation; it makes no claim about
Frobenius traces, positive residues, or bounds uniform in the path length. -/
theorem nearestNeighborRemainder_eq_character_transfer_products
    {E A : Type*} [Field E] [Fintype E] [DecidableEq E]
    [AddCommGroup A] [Module E A] [Fintype A] [DecidableEq A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) (m : ℕ) (c : E)
    (τ : A → ℂ)
    (b : Fin m → A →ₗ[E] A →ₗ[E] E) :
    let M : ℂ := ∑ x : A, τ x
    let pathValue : (Fin (m + 1) → A) → E := fun u =>
      c + ∑ i : Fin m, b i (u i.castSucc) (u i.succ)
    let N : ℂ := ∑ u : Fin (m + 1) → A,
      if pathValue u = 0 then ∏ i : Fin (m + 1), τ (u i) else 0
    (Fintype.card E : ℂ) * N - M ^ (m + 1) =
      ∑ r ∈ Finset.univ.erase (0 : E), ψ (r * c) *
        ∑ x : A, τ x *
          (pathTransferProduct ψ r m b (fun _ x => τ x)).mulVec
            (fun _ => (1 : ℂ)) x := by
  classical
  intro M pathValue N
  rw [nearestNeighborRemainder_eq_character_path_sums ψ hψ m c τ b]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [nearestNeighborPathSum_eq_transferProduct]

/-- Uniform finite bound for the nearest-neighbor remainder. Its only inputs are
the nondegenerate bilinear edge kernels and the site-weight bound; no spectral
decomposition, residue positivity, or cohomological interpretation is assumed. -/
theorem nearestNeighborRemainder_norm_sq_le
    {E A : Type*} [Field E] [Fintype E] [DecidableEq E]
    [AddCommGroup A] [Module E A] [Fintype A]
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 0) (m : ℕ) (c : E)
    (τ : A → ℂ) (b : Fin m → A →ₗ[E] A →ₗ[E] E)
    (hb : ∀ i z, (∀ x, b i x z = 0) → z = 0)
    {T : ℝ} (hT : 0 ≤ T) (hτ : ∀ x, ‖τ x‖ ≤ T) :
    let M : ℂ := ∑ x : A, τ x
    let pathValue : (Fin (m + 1) → A) → E := fun u =>
      c + ∑ i : Fin m, b i (u i.castSucc) (u i.succ)
    let N : ℂ := ∑ u : Fin (m + 1) → A,
      if pathValue u = 0 then ∏ i : Fin (m + 1), τ (u i) else 0
    ‖(Fintype.card E : ℂ) * N - M ^ (m + 1)‖ ^ 2 ≤
      (Fintype.card E : ℝ) ^ 2 * T ^ (2 * (m + 1)) *
        (Fintype.card A : ℝ) ^ (m + 2) := by
  classical
  intro M pathValue N
  rw [nearestNeighborRemainder_eq_character_path_sums ψ hψ m c τ b]
  let S : Finset E := Finset.univ.erase (0 : E)
  let term : E → ℂ := fun r =>
    ψ (r * c) * nearestNeighborPathSum ψ r m b (fun x => τ x) (fun _ x => τ x)
  let K : ℝ := T ^ (2 * (m + 1)) * (Fintype.card A : ℝ) ^ (m + 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (pow_nonneg hT _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hterm (r : E) (hr : r ∈ S) : ‖term r‖ ^ 2 ≤ K := by
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have hbound := nearestNeighborPathSum_norm_sq_le ψ hψ hr0 hT m b hb
      (fun x => τ x) hτ (fun _ x => τ x) (fun _ x => hτ x)
    dsimp [term, K]
    rw [norm_mul, ψ.norm_apply, one_mul]
    exact hbound
  have hsumSq : (∑ r ∈ S, ‖term r‖ ^ 2) ≤ (S.card : ℝ) * K := by
    calc
      (∑ r ∈ S, ‖term r‖ ^ 2) ≤ ∑ _r ∈ S, K :=
        Finset.sum_le_sum fun r hr => hterm r hr
      _ = (S.card : ℝ) * K := by simp
  have hcs :
      (∑ r ∈ S, ‖term r‖) ^ 2 ≤
        (S.card : ℝ) * (∑ r ∈ S, ‖term r‖ ^ 2) := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : E => (1 : ℝ))
        (fun r => ‖term r‖))
  have hSle : S.card ≤ Fintype.card E := Finset.card_le_univ S
  have hsumBound : (∑ r ∈ S, ‖term r‖) ^ 2 ≤ (Fintype.card E : ℝ) ^ 2 * K := by
    calc
      (∑ r ∈ S, ‖term r‖) ^ 2 ≤ (S.card : ℝ) * ((S.card : ℝ) * K) :=
        hcs.trans (mul_le_mul_of_nonneg_left hsumSq (Nat.cast_nonneg _))
      _ = (S.card : ℝ) ^ 2 * K := by ring
      _ ≤ (Fintype.card E : ℝ) ^ 2 * K := by
        have hcardSq : (S.card : ℝ) ^ 2 ≤ (Fintype.card E : ℝ) ^ 2 := by
          exact_mod_cast (show S.card ^ 2 ≤ Fintype.card E ^ 2 by nlinarith)
        exact mul_le_mul_of_nonneg_right hcardSq hK
  have htriangle :
      ‖∑ r ∈ S, term r‖ ≤ ∑ r ∈ S, ‖term r‖ := norm_sum_le _ _
  have hfinal : ‖∑ r ∈ S, term r‖ ^ 2 ≤ (Fintype.card E : ℝ) ^ 2 * K := by
    calc
      ‖∑ r ∈ S, term r‖ ^ 2 ≤ (∑ r ∈ S, ‖term r‖) ^ 2 := by
        nlinarith [norm_nonneg (∑ r ∈ S, term r), htriangle]
      _ ≤ (Fintype.card E : ℝ) ^ 2 * K := hsumBound
  simpa [S, term, K, mul_assoc] using hfinal

/-! ## 3. Section 5 / Proposition 4: Gysin `+2` in relative indices -/

/-- **Scalar form of Proposition 4 (Gysin degree `+2`)**:
the indices are relative to the lowest possible compactly supported degrees:
`tX b` denotes degree `D + b` on `X`, and `tY a` denotes degree `D - 1 + a`
on `Y`. The relation `tY a = tX (a + 1)` therefore models the absolute Gysin
map from degree `j` on `Y` to degree `j + 2` on `X`. With these scalar trace
identities, the two surviving terms enter with the same sign. The theorem does
not construct the cohomology groups, Gysin map, or Frobenius action. -/
theorem gysin_alternating_trace_telescoping
    (D m : ℕ) (hD : 1 ≤ D) (hm : 2 ≤ m)
    (tX tY : ℕ → ℂ) (tK : ℂ)
    (hiso : ∀ a : ℕ, 1 ≤ a → tY a = tX (a + 1))
    (hborder : tY 0 = tK + tX 1) :
    let Mk : ℂ := ∑ b ∈ Finset.range m, (-1 : ℂ) ^ (D + b) * tX b
    let QN : ℂ := ∑ a ∈ Finset.range (m - 1), (-1 : ℂ) ^ (D - 1 + a) * tY a
    (-1 : ℂ) ^ (D - 1) * (QN - Mk) = tX 0 + tK := by
  intro Mk QN
  have hsign_cancel : ∀ k : ℕ, (-1 : ℂ) ^ (D - 1) * (-1 : ℂ) ^ (D - 1 + k) = (-1 : ℂ) ^ k := by
    intro k
    rw [← pow_add, show (D - 1) + (D - 1 + k) = 2 * (D - 1) + k by omega, pow_add, pow_mul]
    norm_num
  have hsign_X : ∀ b : ℕ, (-1 : ℂ) ^ (D - 1) * (-1 : ℂ) ^ (D + b) = -((-1 : ℂ) ^ b) := by
    intro b
    have hDsub : D - 1 + 1 = D := Nat.sub_add_cancel hD
    rw [← pow_add, show (D - 1) + (D + b) = 2 * (D - 1) + (b + 1) by
      rw [← hDsub]
      omega,
      pow_add, pow_mul, pow_succ]
    ring
  have hQN : (-1 : ℂ) ^ (D - 1) * QN = ∑ a ∈ Finset.range (m - 1), (-1 : ℂ) ^ a * tY a := by
    dsimp [QN]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_assoc, hsign_cancel]
  have hMk : (-1 : ℂ) ^ (D - 1) * Mk = -(∑ b ∈ Finset.range m, (-1 : ℂ) ^ b * tX b) := by
    dsimp [Mk]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, hsign_X, neg_mul]
  rw [mul_sub, hQN, hMk, sub_neg_eq_add]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 :=
    ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  rw [show m' + 2 - 1 = m' + 1 by omega]
  rw [Finset.sum_range_succ' (fun a => (-1 : ℂ) ^ a * tY a) m',
    Finset.sum_range_succ' (fun b => (-1 : ℂ) ^ b * tX b) (m' + 1),
    Finset.sum_range_succ' (fun b => (-1 : ℂ) ^ (b + 1) * tX (b + 1)) m']
  have hcancel :
      (∑ k ∈ Finset.range m', (-1 : ℂ) ^ (k + 1) * tY (k + 1)) +
        (∑ k ∈ Finset.range m', (-1 : ℂ) ^ (k + 1 + 1) * tX (k + 1 + 1)) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hiso (k + 1) (Nat.succ_le_succ (Nat.zero_le k)), pow_succ (-1 : ℂ) (k + 1)]
    ring
  simp only [pow_zero, one_mul, hborder]
  linear_combination hcancel

/-- **Example 5 (`U = 𝔸¹`, `k = 2`, conic `xy + ax + by + c = 0`, `ab ≠ c`)**:
`N_n = r^n - 1`, `M_n = r^n`, `R_n = r^n N_n - M_n^2 = -r^n`, and
`(-1)^(2 - 1) R_n = r^n`. -/
theorem example5_conic_remainder (r : ℂ) (n : ℕ) :
    (-1 : ℂ) ^ (2 - 1) * (r ^ n * (r ^ n - 1) - (r ^ n) ^ 2) = r ^ n := by
  ring

/-! ## 4. Section 8 / Theorem 1(b): Poincaré-duality purity upgrade -/

/-- **Theorem 1(b) (Poincaré-Duality Purity Upgrade)**:
If `q > 0`, `α ≠ 0`, `‖α‖ ≤ q ^ ((w + i) / 2)`, and the Poincaré-dual eigenvalue
`q ^ d / α` satisfies `‖q ^ d / α‖ ≤ q ^ ((-w + 2 * d - i) / 2)`, then
`‖α‖ = q ^ ((w + i) / 2)` identically. -/
theorem poincareDuality_purity_eq
    {q w i d : ℝ} (hq : 0 < q) {α : ℂ} (hα : α ≠ 0)
    (hupper : ‖α‖ ≤ q ^ ((w + i) / 2))
    (hdual : ‖((q ^ d : ℝ) : ℂ) / α‖ ≤ q ^ ((-w + 2 * d - i) / 2)) :
    ‖α‖ = q ^ ((w + i) / 2) := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hqd_norm : ‖((q ^ d : ℝ) : ℂ)‖ = q ^ d := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le d)]
  rw [norm_div, hqd_norm, div_le_iff₀ hαpos] at hdual
  have hlower : q ^ ((w + i) / 2) ≤ ‖α‖ := by
    have hmul : q ^ ((-w + 2 * d - i) / 2) * q ^ ((w + i) / 2) = q ^ d := by
      rw [← Real.rpow_add hq]
      congr 1
      ring
    have hpos : 0 < q ^ ((-w + 2 * d - i) / 2) := Real.rpow_pos_of_pos hq _
    rw [← hmul] at hdual
    exact le_of_mul_le_mul_left hdual hpos
  exact le_antisymm hupper hlower

/-! ## 5. Pairing-derived dual eigenvalues

The preceding scalar purity lemma assumes a dual eigenvalue of the form
`q^d / α`. The next result derives that relation from an actual bilinear
pairing and an operator scaling law. It is an abstract linear-algebra bridge;
it does not identify a scheme's pro-étale cohomology with a classical
constructible étale-cohomology group. -/

/-- If a linear operator scales a bilinear pairing by `c`, then two eigenvalues
whose eigenvectors pair nontrivially have product `c`. -/
theorem eigenvalue_product_of_scaled_pairing
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    {x y : V} {α β c : ℂ}
    (hx : F x = α • x) (hy : F y = β • y)
    (hpair : B x y ≠ 0)
    (hscale : B (F x) (F y) = c * B x y) :
    α * β = c := by
  have hbilinear : B (F x) (F y) = α * (β * B x y) := by
    rw [hx, hy]
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hmul : (α * β) * B x y = c * B x y := by
    calc
      (α * β) * B x y = α * (β * B x y) := by ring
      _ = B (F x) (F y) := hbilinear.symm
      _ = c * B x y := hscale
  exact (mul_right_cancel₀ hpair) hmul

/-- The eigenvalue paired with `α` under a `q^d`-similitude is exactly
`q^d / α`, provided `α` is nonzero and the eigenvectors pair nontrivially. -/
theorem dual_eigenvalue_eq_rpow_div
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    {x y : V} {α β : ℂ} {q d : ℝ}
    (hx : F x = α • x) (hy : F y = β • y)
    (hpair : B x y ≠ 0) (hα : α ≠ 0)
    (hscale : B (F x) (F y) = ((q ^ d : ℝ) : ℂ) * B x y) :
    β = ((q ^ d : ℝ) : ℂ) / α := by
  have hprod := eigenvalue_product_of_scaled_pairing F B hx hy hpair hscale
  apply (eq_div_iff hα).2
  simpa [mul_comm] using hprod

/-- Pairing-derived dual eigenvalue input followed by the scalar purity squeeze.
Both norm bounds remain explicit hypotheses; this theorem does not derive
Deligne's geometric weight bounds from a scheme or a sheaf. -/
theorem poincareDuality_purity_of_scaled_eigenvector_pair
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    {x y : V} {α β : ℂ} {q w i d : ℝ}
    (hq : 0 < q) (hx : F x = α • x) (hy : F y = β • y)
    (hpair : B x y ≠ 0) (hα : α ≠ 0)
    (hscale : B (F x) (F y) = ((q ^ d : ℝ) : ℂ) * B x y)
    (hupper : ‖α‖ ≤ q ^ ((w + i) / 2))
    (hdual : ‖β‖ ≤ q ^ ((-w + 2 * d - i) / 2)) :
    ‖α‖ = q ^ ((w + i) / 2) := by
  have hβ : β = ((q ^ d : ℝ) : ℂ) / α :=
    dual_eigenvalue_eq_rpow_div F B hx hy hpair hα hscale
  rw [hβ] at hdual
  exact poincareDuality_purity_eq hq hα hupper hdual

/-- A nontrivial additive character `ψ : E → ℂ` on a finite field `E`,
with unit-modulus values and vanishing full sum. -/
structure NontrivialAddChar (E : Type*) [Field E] [Fintype E] where
  toFun : E → ℂ
  map_zero : toFun 0 = 1
  map_add : ∀ x y, toFun (x + y) = toFun x * toFun y
  norm_eq_one : ∀ x, ‖toFun x‖ = 1
  sum_eq_zero : ∑ x : E, toFun x = 0

/-- Concrete inhabitant: the nontrivial additive character on `ZMod 2` (`0 ↦ 1`, `1 ↦ -1`). -/
def zmod2AddChar : NontrivialAddChar (ZMod 2) where
  toFun x := if x = 0 then 1 else -1
  map_zero := by simp
  map_add x y := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := fun z => by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases x with rfl | rfl <;> rcases hcases y with rfl | rfl
    · simp
    · simp
    · simp
    · have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [h2]
  norm_eq_one x := by
    by_cases hx : x = 0 <;> simp [hx]
  sum_eq_zero := by
    change (∑ x : Fin 2, if (x : ZMod 2) = 0 then (1 : ℂ) else -1) = 0
    rw [Fin.sum_univ_two]
    simp

namespace NontrivialAddChar

variable {E : Type*} [Field E] [Fintype E] (ψ : NontrivialAddChar E)

theorem map_neg (x : E) : ψ.toFun (-x) = star (ψ.toFun x) := by
  have h1 : ψ.toFun (-x) * ψ.toFun x = 1 := by
    rw [← ψ.map_add, neg_add_cancel, ψ.map_zero]
  have h2 : star (ψ.toFun x) * ψ.toFun x = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ψ.norm_eq_one]
    norm_num
  have hne : ψ.toFun x ≠ 0 := by
    intro h0
    have := ψ.norm_eq_one x
    rw [h0, norm_zero] at this
    norm_num at this
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem map_sub (x y : E) : ψ.toFun (x - y) = ψ.toFun x * star (ψ.toFun y) := by
  rw [sub_eq_add_neg, ψ.map_add, ψ.map_neg]

/-- **Section 7 Character-Orthogonality Indicator**:
`∑ h : E, ψ(h * x)` equals `|E|` if `x = 0` and `0` otherwise. -/
theorem sum_mul_eq_ite [DecidableEq E] (x : E) :
    (∑ h : E, ψ.toFun (h * x)) = if x = 0 then (Fintype.card E : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [ψ.map_zero]
  · simp only [hx, ↓reduceIte]
    have hbij : (∑ h : E, ψ.toFun (h * x)) = ∑ y : E, ψ.toFun y := by
      exact Equiv.sum_comp (Equiv.mulRight₀ x hx) ψ.toFun
    rw [hbij, ψ.sum_eq_zero]

/-- Any nonzero linear functional `ℓ : A →ₗ[E] E` on a finite `E`-vector space `A`
has vanishing character sum `∑ y : A, ψ (ℓ y) = 0`. -/
theorem sum_linearMap_eq_zero
    {A : Type*} [AddCommGroup A] [Module E A] [Fintype A]
    (ℓ : A →ₗ[E] E) (hℓ : ℓ ≠ 0) :
    (∑ y : A, ψ.toFun (ℓ y)) = 0 := by
  have hex : ∃ y₀ : A, ℓ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (LinearMap.ext h)
  obtain ⟨y₀, hy₀⟩ := hex
  have hmul : ∀ c : E, ψ.toFun (c * ℓ y₀) * (∑ y : A, ψ.toFun (ℓ y)) =
      ∑ y : A, ψ.toFun (ℓ y) := by
    intro c
    rw [Finset.mul_sum]
    calc
      ∑ y : A, ψ.toFun (c * ℓ y₀) * ψ.toFun (ℓ y)
          = ∑ y : A, ψ.toFun (ℓ (c • y₀ + y)) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul, ψ.map_add]
      _ = ∑ y : A, ψ.toFun (ℓ y) :=
            Equiv.sum_comp (Equiv.addLeft (c • y₀)) (fun y => ψ.toFun (ℓ y))
  have hsum : (∑ c : E, ψ.toFun (c * ℓ y₀)) * (∑ y : A, ψ.toFun (ℓ y)) =
      (Fintype.card E : ℂ) * (∑ y : A, ψ.toFun (ℓ y)) := by
    rw [Finset.sum_mul]
    calc
      ∑ c : E, ψ.toFun (c * ℓ y₀) * (∑ y : A, ψ.toFun (ℓ y))
          = ∑ _c : E, ∑ y : A, ψ.toFun (ℓ y) := Finset.sum_congr rfl fun c _ => hmul c
      _ = (Fintype.card E : ℂ) * (∑ y : A, ψ.toFun (ℓ y)) := by simp
  classical
  rw [ψ.sum_mul_eq_ite (ℓ y₀)] at hsum
  simp only [hy₀, ↓reduceIte, zero_mul] at hsum
  have hcard : (Fintype.card E : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  exact (mul_eq_zero.mp hsum.symm).resolve_left hcard

end NontrivialAddChar

end InfoGeometry.Arithmetic.AlpogeDeligneFrobeniusBoundBridge
