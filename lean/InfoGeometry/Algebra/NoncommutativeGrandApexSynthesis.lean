/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Noncommutative Grand Apex Synthesis (`X₁`–`X₅`)

Formalizes over arbitrary noncommutative rings `[Ring B]` and `[Ring A] [StarRing A]`
the five cross-domain apex theorems (`X₁`–`X₅`):
1. `X₁`: Maurer–Cartan winding cocycle `ω_D(uv)` as right-covariant gauge dressing
   `dressConnR D v (windingForm D u)` and Dikin–Burg–Stein self-concordance.
2. `X₂`: Parseval Gabor frame realization of noncommutative bimodule Jaynesian Gibbs
   variance in the `⋆`-positive cone (`∑ D_i D_i⋆ = second moment - |mean|²`).
3. `X₃`: Square-zero chiral Hodge leakage `e_harm Q (d δ + δ d) Q e_harm` equal to
   harmonic commutator variance `(e_harm ⁅e_harm, Q⁆⋆)(⁅e_harm, Q⁆ e_harm)`.
4. `X₄` & `X₅`: Noncommutative 4-channel Hilbert–Schmidt Helmholtz Pythagoras,
   nested Witt chiral Hodge projections in `M₂(M₂(A))`, Clifford–Artin braid relation
   `R₁₂ R₂₃ R₁₂ = R₂₃ R₁₂ R₂₃` with quaternion curvature `⁅R₁₂, R₂₃⁆ = 2 E₃`, and
   the 4-step Sierpiński-to-Cantor contraction ladder `(4 → 3 → 2 → 1) • (D Δ)`.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

/-- Explicit `2 × 2` matrix constructor avoiding `vecCons`/`vecMul` simp expansion. -/
def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  fun i j => match i, j with
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

omit [Ring A] in @[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
omit [Ring A] in @[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
omit [Ring A] in @[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
omit [Ring A] in @[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

omit [Ring A] in @[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 0 = star (M 0 0) := rfl
omit [Ring A] in @[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 1 = star (M 1 0) := rfl
omit [Ring A] in @[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 0 = star (M 0 1) := rfl
omit [Ring A] in @[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 1 = star (M 1 1) := rfl

omit [Ring A] in @[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 0 0 = star (M 0 0) := rfl
omit [Ring A] in @[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 0 1 = star (M 1 0) := rfl
omit [Ring A] in @[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 1 0 = star (M 0 1) := rfl
omit [Ring A] in @[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op            : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def chiralSheetPlus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def chiralSheetMinus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def isotropicSheetPlus  : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
def kleinTwist (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 (-a)

end Matrix2Simp

/-!
## Apex X₁: Winding Cocycle as Right Gauge Dressing & Dikin–Burg–Stein Self-Concordance
-/

section ApexX1_WindingGaugeDressingAndSelfConcordance

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

theorem IsRingDeriv.map_one {D : B →+ B} (hD : IsRingDeriv D) : D 1 = 0 := by
  have h : D (1 * 1) = D 1 * 1 + 1 * D 1 := hD 1 1
  simp only [mul_one, one_mul] at h
  calc D 1 = D 1 + D 1 - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self (D 1)

theorem IsRingDeriv.map_units_inv {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) :
    D (↑X⁻¹ : B) = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by
  have h1 : D ((X : B) * (↑X⁻¹ : B)) = D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B) :=
    hD (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hD.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) = D (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc D (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by noncomm_ring

def windingForm (D : B →+ B) (u : Bˣ) : B := (↑u⁻¹ : B) * D (u : B)
def rightWindingForm (D : B →+ B) (u : Bˣ) : B := D (u : B) * (↑u⁻¹ : B)
def covOpR (D : B →+ B) (A ψ : B) : B := D ψ - ψ * A
def dressConnR (D : B →+ B) (v : Bˣ) (A : B) : B := (↑v⁻¹ : B) * A * (v : B) + windingForm D v
def burgSteinHessian (X : Bˣ) (V : B) : B := (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Winding Cocycle as Right Gauge Dressing & Burg–Stein Self-Concordance (`X₁`)**:
1. Right affine gauge dressing `dressConnR D v A` intertwines `covOpR D`:
   `covOpR D (dressConnR D v A) (ψ * v) = covOpR D A ψ * v`.
2. The noncommutative winding cocycle `windingForm D (u * v)` is the right gauge dressing
   of `windingForm D u` by `v`.
3. The third-order Burg–Stein self-concordance derivative `D (burgSteinHessian X V)` (`D V = 0`)
   satisfies `X * D (burgSteinHessian X V) * X = -(rightWindingForm D X * V + V * windingForm D X)`. -/
theorem winding_gauge_dressing_and_burg_stein_self_concordance
    {D : B →+ B} (hD : IsRingDeriv D) (u v X : Bˣ) (A ψ : B) {V : B} (hV : D V = 0) :
    covOpR D (dressConnR D v A) (ψ * (v : B)) = covOpR D A ψ * (v : B) ∧
    windingForm D (u * v) = dressConnR D v (windingForm D u) ∧
    D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) ∧
    (X : B) * D (burgSteinHessian X V) * (X : B) =
      -(rightWindingForm D X * V + V * windingForm D X) := by
  have h_self : D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) := by
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    rw [hD ((↑X⁻¹ : B) * V) (↑X⁻¹ : B), hD (↑X⁻¹ : B) V, hV, hD.map_units_inv X]
    noncomm_ring
  refine ⟨?_, ?_, h_self, ?_⟩
  · dsimp [covOpR, dressConnR, windingForm]
    rw [hD ψ (v : B)]
    have hv : (v : B) * (↑v⁻¹ : B) = 1 := Units.mul_inv v
    calc D ψ * (v : B) + ψ * D (v : B) -
          ψ * (v : B) * ((↑v⁻¹ : B) * A * (v : B) + (↑v⁻¹ : B) * D (v : B))
      _ = D ψ * (v : B) + ψ * D (v : B) -
          ψ * ((v : B) * (↑v⁻¹ : B)) * A * (v : B) -
          ψ * ((v : B) * (↑v⁻¹ : B)) * D (v : B) := by noncomm_ring
      _ = (D ψ - ψ * A) * (v : B) := by rw [hv]; noncomm_ring
  · dsimp [windingForm, dressConnR]
    have h_inv : ((↑(u * v)⁻¹ : Bˣ) : B) = (↑v⁻¹ : B) * (↑u⁻¹ : B) := by
      rw [_root_.mul_inv_rev]; rfl
    have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
    rw [h_inv, hD (u : B) (v : B)]
    calc (↑v⁻¹ : B) * (↑u⁻¹ : B) * (D (u : B) * (v : B) + (u : B) * D (v : B))
      _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
          (↑v⁻¹ : B) * ((↑u⁻¹ : B) * (u : B)) * D (v : B) := by noncomm_ring
      _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
          (↑v⁻¹ : B) * D (v : B) := by rw [hu]; noncomm_ring
  · rw [h_self]
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    have hX1 : (X : B) * (↑X⁻¹ : B) = 1 := Units.mul_inv X
    have hX2 : (↑X⁻¹ : B) * (X : B) = 1 := Units.inv_mul X
    calc (X : B) * -((↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) +
          ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) * (D (X : B) * (↑X⁻¹ : B))) * (X : B)
      _ = -(((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) * V * ((↑X⁻¹ : B) * (X : B)) +
            ((X : B) * (↑X⁻¹ : B)) * V * (↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * (X : B))) := by
          noncomm_ring
      _ = -(D (X : B) * (↑X⁻¹ : B) * V + V * ((↑X⁻¹ : B) * D (X : B))) := by
          rw [hX1, hX2]; noncomm_ring

end ApexX1_WindingGaugeDressingAndSelfConcordance

/-!
## Apex X₂: Parseval Gabor Frame Realization of Bimodule Jaynesian Gibbs Variance in the ⋆-Positive Cone
-/

section ApexX2_GaborParsevalGibbsVariance

variable {B : Type*} [Ring B] [StarRing B] {n : ℕ}

def gibbsExpectationR (w f : Fin n → B) : B := ∑ i : Fin n, f i * w i
def gibbsExpectationL (w g : Fin n → B) : B := ∑ i : Fin n, w i * g i
def gibbsCrossMoment (w f g : Fin n → B) : B := ∑ i : Fin n, f i * w i * g i
def gibbsCovariance (w f g : Fin n → B) : B :=
  ∑ i : Fin n, (f i - gibbsExpectationR w f) * w i * (g i - gibbsExpectationL w g)

/-- **Parseval Gabor Frame Realization of Noncommutative Jaynesian Gibbs Variance (`X₂`)**:
For any Parseval Gabor frame `φ : Fin n → B` (`∑ i, φ i * star (φ i) = 1`) with weights
`w i = φ i * star (φ i)` and any noncommuting observable `f : Fin n → B`:
1. `gibbsExpectationL w f_star = star (gibbsExpectationR w f)`.
2. `gibbsCovariance w f f_star` is a sum of Hermitian squares `∑ i, D_i * star D_i`.
3. `gibbsCovariance w f f_star = gibbsCrossMoment w f f_star - gibbsExpectationR w f * star (gibbsExpectationR w f)`. -/
theorem parseval_gabor_jaynes_gibbs_variance_positivity
    (φ f : Fin n → B) (h_pars : ∑ i : Fin n, φ i * star (φ i) = 1) :
    let w := fun i => φ i * star (φ i)
    let f_star := fun i => star (f i)
    gibbsExpectationL w f_star = star (gibbsExpectationR w f) ∧
    gibbsCovariance w f f_star =
      ∑ i : Fin n, ((f i - gibbsExpectationR w f) * φ i) *
                   star ((f i - gibbsExpectationR w f) * φ i) ∧
    gibbsCovariance w f f_star =
      gibbsCrossMoment w f f_star -
      gibbsExpectationR w f * star (gibbsExpectationR w f) := by
  intro w f_star
  have h_adj : gibbsExpectationL w f_star = star (gibbsExpectationR w f) := by
    dsimp [gibbsExpectationL, gibbsExpectationR, w, f_star]
    rw [star_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [star_mul, mul_assoc]
  refine ⟨h_adj, ?_, ?_⟩
  · dsimp [gibbsCovariance]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_adj]
    dsimp [w, f_star]
    simp only [star_mul, star_sub]
    noncomm_ring
  · dsimp [gibbsCovariance, gibbsCrossMoment]
    have h_expand : ∀ i : Fin n,
        (f i - gibbsExpectationR w f) * w i * (f_star i - gibbsExpectationL w f_star) =
        (f i * w i * f_star i - gibbsExpectationR w f * (w i * f_star i)) +
        (-(f i * w i) * gibbsExpectationL w f_star +
         gibbsExpectationR w f * w i * gibbsExpectationL w f_star) := fun i => by noncomm_ring
    simp_rw [h_expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    have h_neg : (∑ x : Fin n, -(f x * w x)) = -gibbsExpectationR w f := by
      dsimp [gibbsExpectationR]; rw [Finset.sum_neg_distrib]
    have h_L : (∑ x : Fin n, w x * f_star x) = gibbsExpectationL w f_star := rfl
    have hw : ∑ x : Fin n, w x = 1 := h_pars
    rw [h_neg, h_L, hw, h_adj]
    noncomm_ring

end ApexX2_GaborParsevalGibbsVariance

/-!
## Apex X₃: Square-Zero Chiral Hodge Leakage & Harmonic Commutator Variance
-/

section ApexX3_ChiralHodgeCommutatorVariance

variable {B : Type*} [Ring B] [StarRing B]

/-- **Square-Zero Chiral Hodge Leakage & Harmonic Commutator Variance Theorem (`X₃`)**:
For any square-zero partial-isometry pair `d, δ ∈ B` (`d² = δ² = 0, d δ d = d, δ d δ = δ`)
with self-adjoint harmonic projection `e_harm = 1 - (d δ + δ d)` and any projection
`Q² = Q = Q⋆`, the variance of `T_harm = e_harm Q e_harm` equals both the exact ⊕ coexact
leakage `e_harm Q (d δ + δ d) Q e_harm` and `(e_harm * star ⁅e_harm, Q⁆) * (⁅e_harm, Q⁆ * e_harm)`. -/
theorem chiral_hodge_leakage_eq_commutator_variance
    {d δ Q : B} (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ)
    (h_harm_sa : star (1 - (d * δ + δ * d)) = 1 - (d * δ + δ * d))
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    let e_harm := 1 - (d * δ + δ * d)
    let T_harm := e_harm * Q * e_harm
    T_harm - T_harm * T_harm = e_harm * Q * (d * δ + δ * d) * Q * e_harm ∧
    T_harm - T_harm * T_harm = (e_harm * star ⁅e_harm, Q⁆) * (⁅e_harm, Q⁆ * e_harm) := by
  intro e_harm T_harm
  have he_sa : star e_harm = e_harm := h_harm_sa
  have h_harm_idem : e_harm * e_harm = e_harm := by
    dsimp [e_harm]
    calc (1 - (d * δ + δ * d)) * (1 - (d * δ + δ * d))
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + (d * δ * d) * δ + (δ * d * δ) * d +
          d * (δ * δ) * d + δ * (d * d) * δ := by noncomm_ring
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + d * δ + δ * d +
          d * 0 * d + δ * 0 * δ := by rw [hdδd, hδdδ, hδ2, hd2]
      _ = 1 - (d * δ + δ * d) := by noncomm_ring
  have h_leak : T_harm - T_harm * T_harm = e_harm * Q * (d * δ + δ * d) * Q * e_harm := by
    dsimp [T_harm]
    have h_comp : 1 - e_harm = d * δ + δ * d := by dsimp [e_harm]; noncomm_ring
    have h_sq : (e_harm * Q * e_harm) * (e_harm * Q * e_harm) = e_harm * Q * e_harm * Q * e_harm := by
      calc (e_harm * Q * e_harm) * (e_harm * Q * e_harm)
        _ = e_harm * Q * (e_harm * e_harm) * Q * e_harm := by noncomm_ring
        _ = e_harm * Q * e_harm * Q * e_harm := by rw [h_harm_idem]
    have hQ2 : e_harm * Q * e_harm = e_harm * (Q * Q) * e_harm := by rw [hQ_idem]
    calc e_harm * Q * e_harm - (e_harm * Q * e_harm) * (e_harm * Q * e_harm)
      _ = e_harm * (Q * Q) * e_harm - e_harm * Q * e_harm * Q * e_harm := by rw [h_sq, ← hQ2]
      _ = e_harm * Q * (1 - e_harm) * Q * e_harm := by noncomm_ring
      _ = e_harm * Q * (d * δ + δ * d) * Q * e_harm := by rw [h_comp]
  refine ⟨h_leak, ?_⟩
  rw [h_leak]
  have h_comm : ⁅e_harm, Q⁆ * e_harm = -((1 - e_harm) * Q * e_harm) := by
    rw [Ring.lie_def]
    calc (e_harm * Q - Q * e_harm) * e_harm
      _ = e_harm * Q * e_harm - Q * (e_harm * e_harm) := by noncomm_ring
      _ = e_harm * Q * e_harm - Q * e_harm := by rw [h_harm_idem]
      _ = -((1 - e_harm) * Q * e_harm) := by noncomm_ring
  have h_star : e_harm * star ⁅e_harm, Q⁆ = -star ((1 - e_harm) * Q * e_harm) := by
    calc e_harm * star ⁅e_harm, Q⁆ = star (⁅e_harm, Q⁆ * e_harm) := by
          simp [star_mul, he_sa]
      _ = -star ((1 - e_harm) * Q * e_harm) := by rw [h_comm, star_neg]
  rw [h_comm, h_star, neg_mul_neg]
  simp only [star_mul, star_sub, star_one, he_sa, hQ_sa]
  have h1e : (1 - e_harm) * (1 - e_harm) = d * δ + δ * d := by
    calc (1 - e_harm) * (1 - e_harm)
      _ = 1 - e_harm - e_harm + e_harm * e_harm := by noncomm_ring
      _ = 1 - e_harm := by rw [h_harm_idem]; noncomm_ring
      _ = d * δ + δ * d := by dsimp [e_harm]; noncomm_ring
  calc e_harm * Q * (d * δ + δ * d) * Q * e_harm
    _ = e_harm * Q * ((1 - e_harm) * (1 - e_harm)) * Q * e_harm := by rw [h1e]
    _ = e_harm * (Q * (1 - e_harm)) * ((1 - e_harm) * Q * e_harm) := by noncomm_ring

end ApexX3_ChiralHodgeCommutatorVariance

/-!
## Apex X₄ & X₅: 4-Channel Pythagoras & Nested Witt Hodge–Braid–Cantor Synthesis
-/

section ApexX4_X5_MasterNestedWittHodgeBraidCantor

variable {A : Type*} [Ring A] [StarRing A]

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Nested coupled isotropic Witt differentials `D = diag(I₊, 0)` and
`Δ = diag(I₋, 0)` in `M₂(M₂(A))`. -/
def nestedD     : NestedMat A := mat2 isotropicSheetPlus 0 0 0
def nestedDelta : NestedMat A := mat2 isotropicSheetMinus 0 0 0

/-- Nested quaternion curvature generators `E₁, E₂, E₃`, Clifford–Artin braid generators
`R₁₂, R₂₃`, composite 2-scale transform `U_braid = R₁₂ R₂₃`, and Sierpiński projection `Pi_S2`. -/
def E₁      : NestedMat A := omegaOp
def E₂      : NestedMat A := kleinTwist omegaOp
def E₃      : NestedMat A := (E₁ : NestedMat A) * E₂
def R₁₂     : NestedMat A := 1 + E₁
def R₂₃     : NestedMat A := 1 + E₂
def U_braid : NestedMat A := R₁₂ * R₂₃
def Pi_S2   : NestedMat A := mat2 1 0 0 chiralSheetPlus

omit [StarRing A] in
private lemma nested_ex_eq :
    (nestedD : NestedMat A) * nestedDelta = mat2 chiralSheetPlus 0 0 0 := by
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus, chiralSheetPlus]

omit [StarRing A] in
private lemma nested_nonh_eq :
    (nestedD : NestedMat A) * nestedDelta + nestedDelta * nestedD = mat2 1 0 0 0 := by
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]

omit [StarRing A] in
private lemma nested_u_braid_eq :
    (U_braid : NestedMat A) =
      mat2 (1 + omegaOp) (-1 + omegaOp) (1 + omegaOp) (1 - omegaOp) := by
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, omegaOp]

private lemma nested_contraction_4 :
    (U_braid * (nestedD * nestedDelta) : NestedMat A)ᴴ * (U_braid * (nestedD * nestedDelta)) =
      4 • (nestedD * nestedDelta) := by
  have h_ue : (U_braid : NestedMat A) * (nestedD * nestedDelta) =
      mat2 ((1 + omegaOp) * chiralSheetPlus) 0 ((1 + omegaOp) * chiralSheetPlus) 0 := by
    rw [nested_u_braid_eq, nested_ex_eq]
    apply ext_fin2 <;> apply ext_fin2 <;> simp
  rw [h_ue, nested_ex_eq]
  apply ext_fin2 <;> apply ext_fin2 <;>
    (simp [chiralSheetPlus, omegaOp]; try (abel_nf; simp))

private lemma nested_contraction_3 :
    (Pi_S2 * U_braid * (nestedD * nestedDelta) : NestedMat A)ᴴ *
      (Pi_S2 * U_braid * (nestedD * nestedDelta)) =
      3 • (nestedD * nestedDelta) := by
  have h_pue : (Pi_S2 : NestedMat A) * U_braid * (nestedD * nestedDelta) =
      mat2 ((1 + omegaOp) * chiralSheetPlus) 0 (chiralSheetPlus * (1 + omegaOp) * chiralSheetPlus) 0 := by
    rw [mul_assoc, nested_u_braid_eq, nested_ex_eq]
    apply ext_fin2 <;> apply ext_fin2 <;> simp [Pi_S2, mul_assoc]
  rw [h_pue, nested_ex_eq]
  apply ext_fin2 <;> apply ext_fin2 <;>
    (simp [chiralSheetPlus, omegaOp]; try (abel_nf; simp))

private lemma nested_contraction_2 :
    ((nestedD * nestedDelta + nestedDelta * nestedD) * U_braid * (nestedD * nestedDelta) : NestedMat A)ᴴ *
      ((nestedD * nestedDelta + nestedDelta * nestedD) * U_braid * (nestedD * nestedDelta)) =
      2 • (nestedD * nestedDelta) := by
  have h_nue : ((nestedD : NestedMat A) * nestedDelta + nestedDelta * nestedD) *
        U_braid * (nestedD * nestedDelta) =
      mat2 ((1 + omegaOp) * chiralSheetPlus) 0 0 0 := by
    rw [mul_assoc, nested_u_braid_eq, nested_nonh_eq, nested_ex_eq]
    apply ext_fin2 <;> apply ext_fin2 <;> simp
  rw [h_nue, nested_ex_eq]
  apply ext_fin2 <;> apply ext_fin2 <;>
    (simp [chiralSheetPlus, omegaOp]; try (abel_nf; simp))

private lemma nested_contraction_1 :
    ((nestedD * nestedDelta) * U_braid * (nestedD * nestedDelta) : NestedMat A)ᴴ *
      ((nestedD * nestedDelta) * U_braid * (nestedD * nestedDelta)) =
      (nestedD * nestedDelta) := by
  have h_eue : ((nestedD : NestedMat A) * nestedDelta) * U_braid * (nestedD * nestedDelta) =
      mat2 (chiralSheetPlus * (1 + omegaOp) * chiralSheetPlus) 0 0 0 := by
    rw [mul_assoc, nested_u_braid_eq, nested_ex_eq]
    apply ext_fin2 <;> apply ext_fin2 <;> simp [mul_assoc]
  rw [h_eue, nested_ex_eq]
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [chiralSheetPlus, omegaOp]

/-- **Grand Apex Theorem in `M₂(M₂(A))` (`X₄` & `X₅`)**:
Over any noncommutative `⋆`-ring `A`:
1. The four Helmholtz–Tetraktys channels `M_I, M_Γ, M_Σ, M_Ω ∈ M₂(A)` satisfy the
   exact Hilbert–Schmidt Pythagorean identity without commutativity or self-adjointness assumptions.
2. The nested coupled isotropic Witt differentials `D, Δ ∈ M₂(M₂(A))` satisfy
   `D² = Δ² = 0`, `D Δ D = D`, `Δ D Δ = Δ`.
3. The Clifford–Artin braid operators `R₁₂, R₂₃` satisfy `R₁₂ R₂₃ R₁₂ = R₂₃ R₁₂ R₂₃`
   and `⁅R₁₂, R₂₃⁆ = 2 E₃`.
4. Compressing `U_braid (D Δ)` across the full space `1`, the Sierpiński mask `Pi_S2`,
   the non-harmonic Hodge support `D Δ + Δ D`, and the exact Hodge projection `D Δ`
   contracts the Gram square strictly along `4 • (D Δ) → 3 • (D Δ) → 2 • (D Δ) → 1 • (D Δ)`. -/
theorem grand_apex_witt_hodge_braid_cantor_synthesis (cI cGamma cSigma cOmega : A) :
    let M_I     : Matrix (Fin 2) (Fin 2) A := fiberEmbed cI * 1
    let M_Gamma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cGamma * gamma1Op
    let M_Sigma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cSigma * sigmaOp
    let M_Omega : Matrix (Fin 2) (Fin 2) A := fiberEmbed cOmega * omegaOp
    let e_ex    : NestedMat A := nestedD * nestedDelta
    let e_nonh  : NestedMat A := nestedD * nestedDelta + nestedDelta * nestedD
    Matrix.trace ((M_I + M_Gamma + M_Sigma + M_Omega)ᴴ * (M_I + M_Gamma + M_Sigma + M_Omega)) =
      Matrix.trace (M_Iᴴ * M_I) + Matrix.trace (M_Gammaᴴ * M_Gamma) +
      Matrix.trace (M_Sigmaᴴ * M_Sigma) + Matrix.trace (M_Omegaᴴ * M_Omega) ∧
    (nestedD : NestedMat A) * nestedD = 0 ∧
    (nestedDelta : NestedMat A) * nestedDelta = 0 ∧
    (nestedD : NestedMat A) * nestedDelta * nestedD = nestedD ∧
    (nestedDelta : NestedMat A) * nestedD * nestedDelta = nestedDelta ∧
    (R₁₂ : NestedMat A) * R₂₃ * R₁₂ = R₂₃ * R₁₂ * R₂₃ ∧
    ⁅(R₁₂ : NestedMat A), R₂₃⁆ = 2 • (E₃ : NestedMat A) ∧
    (U_braid * e_ex : NestedMat A)ᴴ * (U_braid * e_ex) = 4 • e_ex ∧
    (Pi_S2 * U_braid * e_ex : NestedMat A)ᴴ * (Pi_S2 * U_braid * e_ex) = 3 • e_ex ∧
    (e_nonh * U_braid * e_ex : NestedMat A)ᴴ * (e_nonh * U_braid * e_ex) = 2 • e_ex ∧
    (e_ex * U_braid * e_ex : NestedMat A)ᴴ * (e_ex * U_braid * e_ex) = e_ex := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    nested_contraction_4, nested_contraction_3, nested_contraction_2, nested_contraction_1⟩
  · simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]
    noncomm_ring
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, isotropicSheetPlus]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedDelta, isotropicSheetMinus]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [R₁₂, R₂₃, E₁, E₂, kleinTwist, omegaOp]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [R₁₂, R₂₃, E₁, E₂, E₃, kleinTwist, omegaOp, two_smul] <;> abel

end ApexX4_X5_MasterNestedWittHodgeBraidCantor


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis
