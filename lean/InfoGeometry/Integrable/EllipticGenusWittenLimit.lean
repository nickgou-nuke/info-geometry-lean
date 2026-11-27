/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Elliptic genus Witten limit ($z \to 0$) and Jacobi $\theta_1$ pole truncation

Formalization of the elliptic genus Witten index limit and JK-pole truncation
from Shu, Zhao, Zhu, and Zou, *Bethe-state counting and Witten index*,
SciPost Phys. 15, 103 (2023) (Eqs. 5, A.6, A.9, A.14–A.15):

1. Holomorphic odd Jacobi theta function `jacobiTheta1 τ z` constructed from
   Mathlib's two-variable `jacobiTheta₂`, together with oddness, vanishing at
   `z = 0`, quasi-periodicity (`z + 1`, `z + τ`), entire `ℂ`-differentiability
   and continuity in `z`, and a constructive non-degeneracy witness
   `jacobiTheta1 (2 * Complex.I) (1 / 2) ≠ 0`.
2. Rank-1 JK-pole summand `rank1EllipticSummand` (Eq. 5) and its equivalence
   with Eq. (A.9) under Eq. (A.6), exact pole truncation when `twoS α < n α`,
   and the Witten limit `z → 0` tending to `1` per surviving configuration and
   to `(survivingPoleConfigs2D L P.twoS M).card` for the full sum.
3. Higher-rank `SU(r + 1)` JK-pole summand `higherRankEllipticSummand` (Eq. A.14),
   consistency with rank 1, nested pole truncation when
   `n a.castSucc α < n a.succ α` (Eq. A.15), and the Witten limit `z → 0`.
-/

namespace InfoGeometry.Integrable.EllipticGenusWittenLimit

open Complex Filter
open scoped BigOperators Topology

/-! ### 1. Odd Jacobi Theta Function `jacobiTheta1` -/

/-- The odd Jacobi theta function `θ₁(τ, z)` constructed from Mathlib's
two-variable `jacobiTheta₂ z τ` (whose first argument is `z` and second is `τ`):
`θ₁(τ, z) = -i exp(π i τ / 4 + π i z) θ₂(z + 1/2 + τ/2, τ)`. -/
noncomputable def jacobiTheta1 (τ z : ℂ) : ℂ :=
  -Complex.I * Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) *
    jacobiTheta₂ (z + 1 / 2 + τ / 2) τ

lemma jacobiTheta1_undef {τ : ℂ} (hτ : τ.im ≤ 0) (z : ℂ) : jacobiTheta1 τ z = 0 := by
  simp [jacobiTheta1, jacobiTheta₂_undef _ hτ]

/-- Oddness of `θ₁`: `θ₁(τ, -z) = -θ₁(τ, z)`. -/
theorem jacobiTheta1_neg (τ z : ℂ) : jacobiTheta1 τ (-z) = -jacobiTheta1 τ z := by
  unfold jacobiTheta1
  have hneg : -z + 1 / 2 + τ / 2 = -(z - 1 / 2 - τ / 2) := by ring
  have hadd1 : z - 1 / 2 - τ / 2 + 1 = z + 1 / 2 - τ / 2 := by ring
  have haddτ : z + 1 / 2 + τ / 2 = (z + 1 / 2 - τ / 2) + τ := by ring
  have hθ : jacobiTheta₂ (z + 1 / 2 + τ / 2) τ =
      -Complex.exp (-2 * Real.pi * Complex.I * z) * jacobiTheta₂ (z + 1 / 2 - τ / 2) τ := by
    rw [haddτ, jacobiTheta₂_add_left' (z + 1 / 2 - τ / 2) τ]
    have hexp :
        Complex.exp (-Real.pi * Complex.I * (τ + 2 * (z + 1 / 2 - τ / 2))) =
          -Complex.exp (-2 * Real.pi * Complex.I * z) := by
      have harg :
          -Real.pi * Complex.I * (τ + 2 * (z + 1 / 2 - τ / 2)) =
            (-2 * Real.pi * Complex.I * z) + (-(Real.pi * Complex.I)) := by ring
      have hpi : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
        rw [Complex.exp_neg, Complex.exp_pi_mul_I]
        norm_num
      rw [harg, Complex.exp_add, hpi, mul_neg_one]
    rw [hexp]
  have hθ_neg : jacobiTheta₂ (-z + 1 / 2 + τ / 2) τ = jacobiTheta₂ (z + 1 / 2 - τ / 2) τ := by
    rw [hneg, jacobiTheta₂_neg_left, ← jacobiTheta₂_add_left (z - 1 / 2 - τ / 2) τ, hadd1]
  rw [hθ_neg, hθ]
  have hexp2 :
      Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) *
          (-Complex.exp (-2 * Real.pi * Complex.I * z)) =
        -Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * -z) := by
    rw [mul_neg, ← Complex.exp_add]
    congr 1
    congr 1
    ring
  calc
    -Complex.I * Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * -z) *
        jacobiTheta₂ (z + 1 / 2 - τ / 2) τ
      = -(-Complex.I * (-Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * -z)) *
          jacobiTheta₂ (z + 1 / 2 - τ / 2) τ) := by ring
    _ = -(-Complex.I * (Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) *
          (-Complex.exp (-2 * Real.pi * Complex.I * z))) *
          jacobiTheta₂ (z + 1 / 2 - τ / 2) τ) := by rw [hexp2]
    _ = -(-Complex.I * Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) *
          (-Complex.exp (-2 * Real.pi * Complex.I * z) *
            jacobiTheta₂ (z + 1 / 2 - τ / 2) τ)) := by ring

/-- `θ₁(τ, 0) = 0`, which drives JK-pole truncation whenever a shift hits `0`. -/
@[simp]
theorem jacobiTheta1_zero (τ : ℂ) : jacobiTheta1 τ 0 = 0 := by
  have h := jacobiTheta1_neg τ 0
  rw [neg_zero] at h
  have h2 : jacobiTheta1 τ 0 + jacobiTheta1 τ 0 = 0 := by
    calc
      jacobiTheta1 τ 0 + jacobiTheta1 τ 0 = -jacobiTheta1 τ 0 + jacobiTheta1 τ 0 := by rw [← h]
      _ = 0 := neg_add_cancel _
  have hmul : (2 : ℂ) * jacobiTheta1 τ 0 = 0 := by
    calc
      (2 : ℂ) * jacobiTheta1 τ 0 = jacobiTheta1 τ 0 + jacobiTheta1 τ 0 := two_mul _
      _ = 0 := h2
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

/-- Lattice periodicity `θ₁(τ, z + 1) = -θ₁(τ, z)`. -/
theorem jacobiTheta1_add_one (τ z : ℂ) : jacobiTheta1 τ (z + 1) = -jacobiTheta1 τ z := by
  unfold jacobiTheta1
  have hadd : z + 1 + 1 / 2 + τ / 2 = (z + 1 / 2 + τ / 2) + 1 := by ring
  rw [hadd, jacobiTheta₂_add_left]
  have hexp :
      Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * (z + 1)) =
        -Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) := by
    have harg :
        Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * (z + 1) =
          (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) + Real.pi * Complex.I := by ring
    rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hexp]
  ring

/-- Quasi-periodicity `θ₁(τ, z + τ) = -exp(-π i (τ + 2 z)) θ₁(τ, z)`. -/
theorem jacobiTheta1_add_tau (τ z : ℂ) :
    jacobiTheta1 τ (z + τ) = -Complex.exp (-Real.pi * Complex.I * (τ + 2 * z)) * jacobiTheta1 τ z := by
  unfold jacobiTheta1
  have hadd : z + τ + 1 / 2 + τ / 2 = (z + 1 / 2 + τ / 2) + τ := by ring
  rw [hadd, jacobiTheta₂_add_left']
  have hexp :
      Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * (z + τ)) *
          Complex.exp (-Real.pi * Complex.I * (τ + 2 * (z + 1 / 2 + τ / 2))) =
        -Complex.exp (-Real.pi * Complex.I * (τ + 2 * z)) *
          Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) := by
    rw [← Complex.exp_add]
    have hpi : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have harg :
        (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * (z + τ)) +
            (-Real.pi * Complex.I * (τ + 2 * (z + 1 / 2 + τ / 2))) =
          (-Real.pi * Complex.I * (τ + 2 * z) +
              (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z)) +
            (-(Real.pi * Complex.I)) := by ring
    rw [harg, Complex.exp_add, hpi, Complex.exp_add]
    ring
  calc
    -Complex.I * Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * (z + τ)) *
        (Complex.exp (-Real.pi * Complex.I * (τ + 2 * (z + 1 / 2 + τ / 2))) *
          jacobiTheta₂ (z + 1 / 2 + τ / 2) τ)
      = -Complex.I *
          (Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * (z + τ)) *
            Complex.exp (-Real.pi * Complex.I * (τ + 2 * (z + 1 / 2 + τ / 2)))) *
          jacobiTheta₂ (z + 1 / 2 + τ / 2) τ := by ring
    _ = -Complex.I *
          (-Complex.exp (-Real.pi * Complex.I * (τ + 2 * z)) *
            Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z)) *
          jacobiTheta₂ (z + 1 / 2 + τ / 2) τ := by rw [hexp]
    _ = -Complex.exp (-Real.pi * Complex.I * (τ + 2 * z)) *
          (-Complex.I * Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * z) *
            jacobiTheta₂ (z + 1 / 2 + τ / 2) τ) := by ring

/-- `z ↦ θ₁(τ, z)` is complex-differentiable everywhere on `ℂ` (identically `0` for `im τ ≤ 0`). -/
theorem differentiableAt_jacobiTheta1 (τ z : ℂ) : DifferentiableAt ℂ (jacobiTheta1 τ) z := by
  rcases le_or_gt τ.im 0 with hτ | hτ
  · have hfun : jacobiTheta1 τ = fun _ => 0 := funext (jacobiTheta1_undef hτ)
    rw [hfun]
    exact differentiableAt_const 0
  · have hlin1 : DifferentiableAt ℂ (fun w : ℂ => Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * w) z :=
      (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)
    have hexp : DifferentiableAt ℂ (fun w : ℂ =>
        -Complex.I * Complex.exp (Real.pi * Complex.I * τ / 4 + Real.pi * Complex.I * w)) z :=
      (differentiableAt_const _).mul (Complex.differentiableAt_exp.comp z hlin1)
    have hlin2 : DifferentiableAt ℂ (fun w : ℂ => w + 1 / 2 + τ / 2) z :=
      (differentiableAt_id.add (differentiableAt_const _)).add (differentiableAt_const _)
    have hθ : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ (w + 1 / 2 + τ / 2) τ) z := by
      change DifferentiableAt ℂ ((fun w : ℂ => jacobiTheta₂ w τ) ∘ (fun w : ℂ => w + 1 / 2 + τ / 2)) z
      exact (differentiableAt_jacobiTheta₂_fst (z + 1 / 2 + τ / 2) hτ).comp z hlin2
    exact hexp.mul hθ

theorem differentiable_jacobiTheta1 (τ : ℂ) : Differentiable ℂ (jacobiTheta1 τ) :=
  fun z => differentiableAt_jacobiTheta1 τ z

theorem continuous_jacobiTheta1 (τ : ℂ) : Continuous (jacobiTheta1 τ) :=
  (differentiable_jacobiTheta1 τ).continuous

theorem continuousAt_jacobiTheta1 (τ z : ℂ) : ContinuousAt (jacobiTheta1 τ) z :=
  (continuous_jacobiTheta1 τ).continuousAt

/-- Constructive non-degeneracy witness proving `jacobiTheta1` is not identically zero:
at `τ = 2 * i` and `z = 1 / 2`, every term of `jacobiTheta₂ i (2 i)` is real and positive
with `n = 0` term equal to `1`. -/
theorem jacobiTheta1_twoI_half_ne_zero : jacobiTheta1 (2 * Complex.I) (1 / 2) ≠ 0 := by
  unfold jacobiTheta1
  have hshift : (1 / 2 : ℂ) + 1 / 2 + 2 * Complex.I / 2 = Complex.I + 1 := by ring
  rw [hshift, jacobiTheta₂_add_left]
  have him : 0 < (2 * Complex.I).im := by simp
  have hsum : HasSum (fun n : ℤ => jacobiTheta₂_term n Complex.I (2 * Complex.I))
      (jacobiTheta₂ Complex.I (2 * Complex.I)) :=
    hasSum_jacobiTheta₂_term Complex.I him
  have hre : HasSum (fun n : ℤ => (jacobiTheta₂_term n Complex.I (2 * Complex.I)).re)
      (jacobiTheta₂ Complex.I (2 * Complex.I)).re :=
    Complex.reCLM.hasSum hsum
  have hterm : ∀ n : ℤ,
      (jacobiTheta₂_term n Complex.I (2 * Complex.I)).re =
        Real.exp (-(2 * Real.pi * (n : ℝ) + 2 * Real.pi * (n : ℝ) ^ 2)) := by
    intro n
    unfold jacobiTheta₂_term
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * Complex.I +
            (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (2 * Complex.I) =
          ((-(2 * Real.pi * (n : ℝ) + 2 * Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
      push_cast
      calc
        2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * Complex.I +
            (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (2 * Complex.I)
          = (2 * (Real.pi : ℂ) * (n : ℂ) + 2 * (Real.pi : ℂ) * (n : ℂ) ^ 2) *
              (Complex.I * Complex.I) := by ring
        _ = (2 * (Real.pi : ℂ) * (n : ℂ) + 2 * (Real.pi : ℂ) * (n : ℂ) ^ 2) * (-1) := by
            rw [Complex.I_mul_I]
        _ = -(2 * (Real.pi : ℂ) * (n : ℂ) + 2 * (Real.pi : ℂ) * (n : ℂ) ^ 2) := by ring
    rw [harg, Complex.exp_ofReal_re]
  have hnonneg : ∀ n : ℤ, 0 ≤ (jacobiTheta₂_term n Complex.I (2 * Complex.I)).re := by
    intro n
    rw [hterm n]
    exact le_of_lt (Real.exp_pos _)
  have hle : (1 : ℝ) ≤ (jacobiTheta₂ Complex.I (2 * Complex.I)).re := by
    have h0 : (jacobiTheta₂_term (0 : ℤ) Complex.I (2 * Complex.I)).re = 1 := by
      rw [hterm 0]
      simp
    have hle' := hre.summable.le_tsum (0 : ℤ) (fun n _ => hnonneg n)
    rw [h0, hre.tsum_eq] at hle'
    exact hle'
  have hθ_ne : jacobiTheta₂ Complex.I (2 * Complex.I) ≠ 0 := by
    intro hz
    have hre0 : (jacobiTheta₂ Complex.I (2 * Complex.I)).re = 0 := by rw [hz]; simp
    linarith
  apply mul_ne_zero
  · apply mul_ne_zero
    · simp [Complex.I_ne_zero]
    · exact Complex.exp_ne_zero _
  · exact hθ_ne

/-! ### 2. Rank-1 JK-Pole Summand & Witten Limit (Source #5 Eqs. 5, A.6, A.9) -/

/-- Parameters for the rank-1 (`SU(2)`) elliptic genus JK-pole expansion
(Source #5 Eqs. 5, A.6, A.9), where `twoS α = 2 s_α ∈ ℕ` allows half-integer spins. -/
structure RankOneEllipticParams (L : ℕ) where
  τ : ℂ
  ξ : Fin L → ℂ
  lam : ℂ
  twoS : Fin L → ℕ

/-- T17 constructive inhabitant for `RankOneEllipticParams`. -/
noncomputable instance (L : ℕ) : Inhabited (RankOneEllipticParams L) where
  default := ⟨2 * Complex.I, fun _ => 0, 1, fun _ => 1⟩

/-- Concrete witness for `RankOneEllipticParams 2`. -/
noncomputable def witnessRankOneEllipticParams : RankOneEllipticParams 2 :=
  ⟨2 * Complex.I, ![0, 1 / 4], 1 / 3, ![1, 1]⟩

/-- Single `(α, β, m)` factor in the rank-1 elliptic genus JK-pole summand (Eq. 5). -/
noncomputable def rank1Factor {L : ℕ} (P : RankOneEllipticParams L)
    (n : Fin L → ℕ) (α β : Fin L) (m : ℕ) (z : ℂ) : ℂ :=
  let A := P.ξ α - P.ξ β + ((n β : ℂ) - (m : ℂ)) * P.lam
  let B := -(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam
  (jacobiTheta1 P.τ (A - z) / jacobiTheta1 P.τ A) *
    (jacobiTheta1 P.τ B / jacobiTheta1 P.τ (B + z))

/-- Full rank-1 JK-pole summand for pole configuration `n : Fin L → ℕ` (Eq. 5). -/
noncomputable def rank1EllipticSummand {L : ℕ} (P : RankOneEllipticParams L)
    (n : Fin L → ℕ) (z : ℂ) : ℂ :=
  ∏ α : Fin L, ∏ β : Fin L, ∏ m ∈ Finset.range (n α), rank1Factor P n α β m z

/-- Alternative parameterization of the rank-1 summand in terms of flavor fugacities `χ`
(Source #5 Eq. A.9). -/
noncomputable def rank1EllipticSummandA9 {L : ℕ} (τ : ℂ) (ξ χ : Fin L → ℂ)
    (lam : ℂ) (n : Fin L → ℕ) (z : ℂ) : ℂ :=
  ∏ α : Fin L, ∏ β : Fin L, ∏ m ∈ Finset.range (n α),
    (jacobiTheta1 τ (ξ α - ξ β + ((n β : ℂ) - (m : ℂ)) * lam - z) /
      jacobiTheta1 τ (ξ α - ξ β + ((n β : ℂ) - (m : ℂ)) * lam)) *
    (jacobiTheta1 τ (-(ξ α - ξ β) + χ α + χ β - z + (m : ℂ) * lam) /
      jacobiTheta1 τ (-(ξ α - ξ β) + χ α + χ β + (m : ℂ) * lam))

/-- Equivalence of Eq. (A.9) and Eq. (5) under the specialization Eq. (A.6):
`2 χ_α + 2 s_α λ = z`. -/
theorem rank1EllipticSummandA9_eq_rank1EllipticSummand {L : ℕ}
    (P : RankOneEllipticParams L) (χ : Fin L → ℂ) (n : Fin L → ℕ) (z : ℂ)
    (hA6 : ∀ α : Fin L, 2 * χ α + (P.twoS α : ℂ) * P.lam = z) :
    rank1EllipticSummandA9 P.τ P.ξ χ P.lam n z = rank1EllipticSummand P n z := by
  unfold rank1EllipticSummandA9 rank1EllipticSummand rank1Factor
  refine Finset.prod_congr rfl fun α _ => ?_
  refine Finset.prod_congr rfl fun β _ => ?_
  refine Finset.prod_congr rfl fun m _ => ?_
  have hχ : χ α + χ β - z = -(((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam := by
    have hα := hA6 α
    have hβ := hA6 β
    linear_combination (hα + hβ) / 2
  have harg1 :
      -(P.ξ α - P.ξ β) + χ α + χ β - z + (m : ℂ) * P.lam =
        -(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam := by
    calc
      -(P.ξ α - P.ξ β) + χ α + χ β - z + (m : ℂ) * P.lam
        = -(P.ξ α - P.ξ β) + (χ α + χ β - z) + (m : ℂ) * P.lam := by ring
      _ = -(P.ξ α - P.ξ β) + (-(((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam) +
            (m : ℂ) * P.lam := by rw [hχ]
      _ = -(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam := by
          ring
  have harg2 :
      -(P.ξ α - P.ξ β) + χ α + χ β + (m : ℂ) * P.lam =
        -(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam + z := by
    calc
      -(P.ξ α - P.ξ β) + χ α + χ β + (m : ℂ) * P.lam
        = (-(P.ξ α - P.ξ β) + χ α + χ β - z + (m : ℂ) * P.lam) + z := by ring
      _ = -(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam + z := by
          rw [harg1]
  rw [harg1, harg2]

/-- Explicit generic non-vanishing of the `z = 0` denominators for a rank-1 pole `n`. -/
def RankOneNonDegenerate {L : ℕ} (P : RankOneEllipticParams L) (n : Fin L → ℕ) : Prop :=
  ∀ α β : Fin L, ∀ m ∈ Finset.range (n α),
    jacobiTheta1 P.τ (P.ξ α - P.ξ β + ((n β : ℂ) - (m : ℂ)) * P.lam) ≠ 0 ∧
    jacobiTheta1 P.τ (-(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam) ≠ 0

/-- Exact pole truncation for rank-1 elliptic genus: if `twoS α < n α` for some site `α`,
then the `(α, α, twoS α)` factor contains `θ₁(τ, 0) = 0`, so the summand vanishes identically
for all `z : ℂ`. -/
theorem rank1EllipticSummand_eq_zero_of_lt {L : ℕ} (P : RankOneEllipticParams L)
    (n : Fin L → ℕ) (h : ∃ α : Fin L, P.twoS α < n α) (z : ℂ) :
    rank1EllipticSummand P n z = 0 := by
  obtain ⟨α₀, hlt⟩ := h
  unfold rank1EllipticSummand
  refine Finset.prod_eq_zero (Finset.mem_univ α₀) ?_
  refine Finset.prod_eq_zero (Finset.mem_univ α₀) ?_
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hlt) ?_
  unfold rank1Factor
  dsimp only
  have hB :
      -(P.ξ α₀ - P.ξ α₀) +
          ((P.twoS α₀ : ℂ) - ((P.twoS α₀ : ℂ) + (P.twoS α₀ : ℂ)) / 2) * P.lam = 0 := by
    ring
  rw [hB, jacobiTheta1_zero, zero_div, mul_zero]

/-- Conversely, denominator non-degeneracy forces the restricted occupancy bound `n α ≤ 2 s_α`
at every site `α`. -/
theorem rank1_le_twoS_of_nonDegenerate {L : ℕ} (P : RankOneEllipticParams L)
    (n : Fin L → ℕ) (hnd : RankOneNonDegenerate P n) :
    ∀ α : Fin L, n α ≤ P.twoS α := by
  intro α
  by_contra hnot
  have hlt : P.twoS α < n α := Nat.lt_of_not_le hnot
  have hne := (hnd α α (P.twoS α) (Finset.mem_range.mpr hlt)).2
  have hB :
      -(P.ξ α - P.ξ α) +
          ((P.twoS α : ℂ) - ((P.twoS α : ℂ) + (P.twoS α : ℂ)) / 2) * P.lam = 0 := by
    ring
  rw [hB, jacobiTheta1_zero] at hne
  exact hne rfl

/-- In the Witten limit `z → 0`, every non-degenerate rank-1 JK-pole summand tends to `1`. -/
theorem tendsto_rank1EllipticSummand_nhds_zero {L : ℕ} (P : RankOneEllipticParams L)
    (n : Fin L → ℕ) (hnd : RankOneNonDegenerate P n) :
    Tendsto (rank1EllipticSummand P n) (𝓝 0) (𝓝 1) := by
  unfold rank1EllipticSummand
  have h1 : (1 : ℂ) = ∏ _α : Fin L, ∏ _β : Fin L, ∏ _m ∈ Finset.range (n _α), (1 : ℂ) := by
    simp
  rw [h1]
  refine tendsto_finsetProd Finset.univ fun α _ => ?_
  refine tendsto_finsetProd Finset.univ fun β _ => ?_
  refine tendsto_finsetProd (Finset.range (n α)) fun m hm => ?_
  have hA_ne := (hnd α β m hm).1
  have hB_ne := (hnd α β m hm).2
  set A : ℂ := P.ξ α - P.ξ β + ((n β : ℂ) - (m : ℂ)) * P.lam
  set B : ℂ := -(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS α : ℂ) + (P.twoS β : ℂ)) / 2) * P.lam
  have hsub : Tendsto (fun z : ℂ => A - z) (𝓝 0) (𝓝 A) := by
    simpa using (tendsto_const_nhds (x := A)).sub (tendsto_id (x := 𝓝 (0 : ℂ)))
  have hnum1 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ (A - z)) (𝓝 0) (𝓝 (jacobiTheta1 P.τ A)) :=
    (continuousAt_jacobiTheta1 P.τ A).tendsto.comp hsub
  have hadd : Tendsto (fun z : ℂ => B + z) (𝓝 0) (𝓝 B) := by
    simpa using (tendsto_const_nhds (x := B)).add (tendsto_id (x := 𝓝 (0 : ℂ)))
  have hden2 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ (B + z)) (𝓝 0) (𝓝 (jacobiTheta1 P.τ B)) :=
    (continuousAt_jacobiTheta1 P.τ B).tendsto.comp hadd
  have hratio1 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ (A - z) / jacobiTheta1 P.τ A) (𝓝 0) (𝓝 1) := by
    have h := hnum1.div (tendsto_const_nhds (x := jacobiTheta1 P.τ A)) hA_ne
    rw [div_self hA_ne] at h
    exact h
  have hratio2 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ B / jacobiTheta1 P.τ (B + z)) (𝓝 0) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := jacobiTheta1 P.τ B)).div hden2 hB_ne
    rw [div_self hB_ne] at h
    exact h
  have hmul := hratio1.mul hratio2
  rw [mul_one] at hmul
  exact hmul

/-- All rank-1 JK-pole configurations `n : Fin L → ℕ` with total occupancy `∑ α, n α = M`. -/
def allPoleConfigs2D (L M : ℕ) : Finset (Fin L → ℕ) :=
  (Fintype.piFinset (fun _ : Fin L => Finset.range (M + 1))).filter
    (fun n => ∑ α : Fin L, n α = M)

/-- Surviving (non-truncated) rank-1 pole configurations satisfying `n α ≤ twoS α`. -/
def survivingPoleConfigs2D (L : ℕ) (twoS : Fin L → ℕ) (M : ℕ) : Finset (Fin L → ℕ) :=
  (allPoleConfigs2D L M).filter (fun n => ∀ α : Fin L, n α ≤ twoS α)

/-- Full rank-1 elliptic genus Witten limit: as `z → 0`, the sum over all JK poles
tends to the cardinality of surviving restricted-occupancy configurations. -/
theorem tendsto_rank1EllipticGenus_nhds_zero {L : ℕ} (P : RankOneEllipticParams L) (M : ℕ)
    (hnd : ∀ n ∈ survivingPoleConfigs2D L P.twoS M, RankOneNonDegenerate P n) :
    Tendsto (fun z => ∑ n ∈ allPoleConfigs2D L M, rank1EllipticSummand P n z)
      (𝓝 0) (𝓝 ((survivingPoleConfigs2D L P.twoS M).card : ℂ)) := by
  have hlim_sum :
      ((survivingPoleConfigs2D L P.twoS M).card : ℂ) =
        ∑ n ∈ allPoleConfigs2D L M, if ∀ α : Fin L, n α ≤ P.twoS α then (1 : ℂ) else 0 := by
    rw [survivingPoleConfigs2D, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  rw [hlim_sum]
  refine tendsto_finsetSum (allPoleConfigs2D L M) fun n hn => ?_
  by_cases hle : ∀ α : Fin L, n α ≤ P.twoS α
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hle)]
    have hmem : n ∈ survivingPoleConfigs2D L P.twoS M :=
      Finset.mem_filter.mpr ⟨hn, hle⟩
    exact tendsto_rank1EllipticSummand_nhds_zero P n (hnd n hmem)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hle)]
    have hlt : ∃ α : Fin L, P.twoS α < n α := by
      rcases not_forall.mp hle with ⟨α, hα⟩
      exact ⟨α, Nat.lt_of_not_le hα⟩
    have hzero : rank1EllipticSummand P n = fun _ => 0 :=
      funext (rank1EllipticSummand_eq_zero_of_lt P n hlt)
    rw [hzero]
    exact tendsto_const_nhds

/-! ### 3. Higher-Rank `SU(r + 1)` JK-Pole Summand & Witten Limit (Source #5 Eqs. A.14–A.15) -/

/-- Parameters for the nested `SU(r + 1)` elliptic genus JK-pole expansion
(Source #5 Eqs. A.14–A.15) with uniform spin `twoS = 2 s ∈ ℕ`. -/
structure HigherRankEllipticParams (r L : ℕ) where
  τ : ℂ
  ξ : Fin L → ℂ
  lam : ℂ
  twoS : ℕ

/-- T17 constructive inhabitant for `HigherRankEllipticParams`. -/
noncomputable instance (r L : ℕ) : Inhabited (HigherRankEllipticParams r L) where
  default := ⟨2 * Complex.I, fun _ => 0, 1, 1⟩

/-- Concrete witness for `HigherRankEllipticParams 2 2`. -/
noncomputable def witnessHigherRankEllipticParams : HigherRankEllipticParams 2 2 :=
  ⟨2 * Complex.I, ![0, 1 / 4], 1 / 3, 1⟩

/-- Single `(a, α, β, m)` factor in the higher-rank JK-pole summand (Eq. A.14). -/
noncomputable def higherRankFactor {r L : ℕ} (P : HigherRankEllipticParams r L)
    (n : Fin (r + 1) → Fin L → ℕ) (a : Fin r) (α β : Fin L) (m : ℕ) (z : ℂ) : ℂ :=
  let A := P.ξ α - P.ξ β + ((n a.succ β : ℂ) - (m : ℂ)) * P.lam
  let B := P.ξ α - P.ξ β + ((n a.castSucc β : ℂ) - (m : ℂ)) * P.lam
  (jacobiTheta1 P.τ (A - z) / jacobiTheta1 P.τ A) *
    (jacobiTheta1 P.τ B / jacobiTheta1 P.τ (B - z))

/-- Full higher-rank `SU(r + 1)` JK-pole summand (Source #5 Eq. A.14). -/
noncomputable def higherRankEllipticSummand {r L : ℕ} (P : HigherRankEllipticParams r L)
    (n : Fin (r + 1) → Fin L → ℕ) (z : ℂ) : ℂ :=
  ∏ a : Fin r, ∏ α : Fin L, ∏ β : Fin L, ∏ m ∈ Finset.range (n a.succ α),
    higherRankFactor P n a α β m z

/-- Rank-1 consistency: for `r = 1` and boundary condition `n 0 = fun _ => P.twoS`,
the higher-rank summand (Eq. A.14) equals the rank-1 summand (Eq. 5) with uniform
spin `P.twoS` via oddness `θ₁(τ, -w) = -θ₁(τ, w)` on the second ratio. -/
theorem higherRankEllipticSummand_one_eq_rank1 {L : ℕ}
    (P : HigherRankEllipticParams 1 L) (n : Fin 2 → Fin L → ℕ)
    (hn0 : n 0 = fun _ => P.twoS) (z : ℂ) :
    higherRankEllipticSummand P n z =
      rank1EllipticSummand ⟨P.τ, P.ξ, P.lam, fun _ => P.twoS⟩ (n 1) z := by
  unfold higherRankEllipticSummand rank1EllipticSummand
  rw [Fin.prod_univ_one]
  refine Finset.prod_congr rfl fun α _ => ?_
  refine Finset.prod_congr rfl fun β _ => ?_
  refine Finset.prod_congr rfl fun m _ => ?_
  unfold higherRankFactor rank1Factor
  dsimp only
  have h0succ : ((0 : Fin 1).succ : Fin 2) = 1 := rfl
  have h0cast : ((0 : Fin 1).castSucc : Fin 2) = 0 := rfl
  rw [h0succ, h0cast, hn0]
  have hB :
      P.ξ α - P.ξ β + ((P.twoS : ℂ) - (m : ℂ)) * P.lam =
        -(-(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS : ℂ) + (P.twoS : ℂ)) / 2) * P.lam) := by
    ring
  have hBz :
      P.ξ α - P.ξ β + ((P.twoS : ℂ) - (m : ℂ)) * P.lam - z =
        -(-(P.ξ α - P.ξ β) + ((m : ℂ) - ((P.twoS : ℂ) + (P.twoS : ℂ)) / 2) * P.lam + z) := by
    ring
  rw [hBz, jacobiTheta1_neg, hB, jacobiTheta1_neg, neg_div_neg_eq]

/-- Explicit generic non-vanishing of `z = 0` denominators for a higher-rank pole `n`. -/
def HigherRankNonDegenerate {r L : ℕ} (P : HigherRankEllipticParams r L)
    (n : Fin (r + 1) → Fin L → ℕ) : Prop :=
  ∀ a : Fin r, ∀ α β : Fin L, ∀ m ∈ Finset.range (n a.succ α),
    jacobiTheta1 P.τ (P.ξ α - P.ξ β + ((n a.succ β : ℂ) - (m : ℂ)) * P.lam) ≠ 0 ∧
    jacobiTheta1 P.τ (P.ξ α - P.ξ β + ((n a.castSucc β : ℂ) - (m : ℂ)) * P.lam) ≠ 0

/-- Exact higher-rank pole truncation (Source #5 Eq. A.15): if `n a.castSucc α < n a.succ α`
for some level `a` and site `α`, the `(a, α, α, n a.castSucc α)` factor contains `θ₁(τ, 0) = 0`,
so the entire summand vanishes identically for all `z : ℂ`. -/
theorem higherRankEllipticSummand_eq_zero_of_lt {r L : ℕ}
    (P : HigherRankEllipticParams r L) (n : Fin (r + 1) → Fin L → ℕ)
    (h : ∃ a : Fin r, ∃ α : Fin L, n a.castSucc α < n a.succ α) (z : ℂ) :
    higherRankEllipticSummand P n z = 0 := by
  obtain ⟨a₀, α₀, hlt⟩ := h
  unfold higherRankEllipticSummand
  refine Finset.prod_eq_zero (Finset.mem_univ a₀) ?_
  refine Finset.prod_eq_zero (Finset.mem_univ α₀) ?_
  refine Finset.prod_eq_zero (Finset.mem_univ α₀) ?_
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hlt) ?_
  unfold higherRankFactor
  dsimp only
  have hB :
      P.ξ α₀ - P.ξ α₀ + ((n a₀.castSucc α₀ : ℂ) - (n a₀.castSucc α₀ : ℂ)) * P.lam = 0 := by
    ring
  rw [hB, jacobiTheta1_zero, zero_div, mul_zero]

/-- Conversely, denominator non-degeneracy forces the nesting bound `n a.succ α ≤ n a.castSucc α`
at every level `a` and site `α`. -/
theorem higherRank_nested_le_of_nonDegenerate {r L : ℕ}
    (P : HigherRankEllipticParams r L) (n : Fin (r + 1) → Fin L → ℕ)
    (hnd : HigherRankNonDegenerate P n) :
    ∀ a : Fin r, ∀ α : Fin L, n a.succ α ≤ n a.castSucc α := by
  intro a α
  by_contra hnot
  have hlt : n a.castSucc α < n a.succ α := Nat.lt_of_not_le hnot
  have hne := (hnd a α α (n a.castSucc α) (Finset.mem_range.mpr hlt)).2
  have hB :
      P.ξ α - P.ξ α + ((n a.castSucc α : ℂ) - (n a.castSucc α : ℂ)) * P.lam = 0 := by
    ring
  rw [hB, jacobiTheta1_zero] at hne
  exact hne rfl

/-- In the Witten limit `z → 0`, every non-degenerate higher-rank JK-pole summand tends to `1`. -/
theorem tendsto_higherRankEllipticSummand_nhds_zero {r L : ℕ}
    (P : HigherRankEllipticParams r L) (n : Fin (r + 1) → Fin L → ℕ)
    (hnd : HigherRankNonDegenerate P n) :
    Tendsto (higherRankEllipticSummand P n) (𝓝 0) (𝓝 1) := by
  unfold higherRankEllipticSummand
  have h1 :
      (1 : ℂ) = ∏ _a : Fin r, ∏ _α : Fin L, ∏ _β : Fin L,
        ∏ _m ∈ Finset.range (n _a.succ _α), (1 : ℂ) := by
    simp
  rw [h1]
  refine tendsto_finsetProd Finset.univ fun a _ => ?_
  refine tendsto_finsetProd Finset.univ fun α _ => ?_
  refine tendsto_finsetProd Finset.univ fun β _ => ?_
  refine tendsto_finsetProd (Finset.range (n a.succ α)) fun m hm => ?_
  have hA_ne := (hnd a α β m hm).1
  have hB_ne := (hnd a α β m hm).2
  set A : ℂ := P.ξ α - P.ξ β + ((n a.succ β : ℂ) - (m : ℂ)) * P.lam
  set B : ℂ := P.ξ α - P.ξ β + ((n a.castSucc β : ℂ) - (m : ℂ)) * P.lam
  have hsubA : Tendsto (fun z : ℂ => A - z) (𝓝 0) (𝓝 A) := by
    simpa using (tendsto_const_nhds (x := A)).sub (tendsto_id (x := 𝓝 (0 : ℂ)))
  have hnum1 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ (A - z)) (𝓝 0) (𝓝 (jacobiTheta1 P.τ A)) :=
    (continuousAt_jacobiTheta1 P.τ A).tendsto.comp hsubA
  have hsubB : Tendsto (fun z : ℂ => B - z) (𝓝 0) (𝓝 B) := by
    simpa using (tendsto_const_nhds (x := B)).sub (tendsto_id (x := 𝓝 (0 : ℂ)))
  have hden2 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ (B - z)) (𝓝 0) (𝓝 (jacobiTheta1 P.τ B)) :=
    (continuousAt_jacobiTheta1 P.τ B).tendsto.comp hsubB
  have hratio1 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ (A - z) / jacobiTheta1 P.τ A) (𝓝 0) (𝓝 1) := by
    have h := hnum1.div (tendsto_const_nhds (x := jacobiTheta1 P.τ A)) hA_ne
    rw [div_self hA_ne] at h
    exact h
  have hratio2 : Tendsto (fun z : ℂ => jacobiTheta1 P.τ B / jacobiTheta1 P.τ (B - z)) (𝓝 0) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := jacobiTheta1 P.τ B)).div hden2 hB_ne
    rw [div_self hB_ne] at h
    exact h
  have hmul := hratio1.mul hratio2
  rw [mul_one] at hmul
  exact hmul

/-- All higher-rank JK-pole configurations `n : Fin (r + 1) → Fin L → ℕ` with boundary
`n 0 = fun _ => twoS` and level totals `∑ α, n a.succ α = M a`. -/
def allPoleConfigs3D (r L twoS : ℕ) (M : Fin r → ℕ) : Finset (Fin (r + 1) → Fin L → ℕ) :=
  (Fintype.piFinset (fun a : Fin (r + 1) =>
    Fintype.piFinset (fun _ : Fin L => Finset.range (Fin.cases twoS M a + 1)))).filter
    (fun n => n 0 = (fun _ => twoS) ∧ ∀ a : Fin r, ∑ α : Fin L, n a.succ α = M a)

/-- Surviving (nested) higher-rank pole configurations satisfying `n a.succ α ≤ n a.castSucc α`. -/
def survivingPoleConfigs3D (r L twoS : ℕ) (M : Fin r → ℕ) : Finset (Fin (r + 1) → Fin L → ℕ) :=
  (allPoleConfigs3D r L twoS M).filter
    (fun n => ∀ a : Fin r, ∀ α : Fin L, n a.succ α ≤ n a.castSucc α)

/-- Full higher-rank elliptic genus Witten limit: as `z → 0`, the sum over all JK poles
tends to the cardinality of surviving nested restricted-occupancy configurations. -/
theorem tendsto_higherRankEllipticGenus_nhds_zero {r L : ℕ}
    (P : HigherRankEllipticParams r L) (M : Fin r → ℕ)
    (hnd : ∀ n ∈ survivingPoleConfigs3D r L P.twoS M, HigherRankNonDegenerate P n) :
    Tendsto (fun z => ∑ n ∈ allPoleConfigs3D r L P.twoS M, higherRankEllipticSummand P n z)
      (𝓝 0) (𝓝 ((survivingPoleConfigs3D r L P.twoS M).card : ℂ)) := by
  have hlim_sum :
      ((survivingPoleConfigs3D r L P.twoS M).card : ℂ) =
        ∑ n ∈ allPoleConfigs3D r L P.twoS M,
          if ∀ a : Fin r, ∀ α : Fin L, n a.succ α ≤ n a.castSucc α then (1 : ℂ) else 0 := by
    rw [survivingPoleConfigs3D, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  rw [hlim_sum]
  refine tendsto_finsetSum (allPoleConfigs3D r L P.twoS M) fun n hn => ?_
  by_cases hle : ∀ a : Fin r, ∀ α : Fin L, n a.succ α ≤ n a.castSucc α
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hle)]
    have hmem : n ∈ survivingPoleConfigs3D r L P.twoS M :=
      Finset.mem_filter.mpr ⟨hn, hle⟩
    exact tendsto_higherRankEllipticSummand_nhds_zero P n (hnd n hmem)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hle)]
    have hlt : ∃ a : Fin r, ∃ α : Fin L, n a.castSucc α < n a.succ α := by
      rcases not_forall.mp hle with ⟨a, ha⟩
      rcases not_forall.mp ha with ⟨α, hα⟩
      exact ⟨a, α, Nat.lt_of_not_le hα⟩
    have hzero : higherRankEllipticSummand P n = fun _ => 0 :=
      funext (higherRankEllipticSummand_eq_zero_of_lt P n hlt)
    rw [hzero]
    exact tendsto_const_nhds

end InfoGeometry.Integrable.EllipticGenusWittenLimit
