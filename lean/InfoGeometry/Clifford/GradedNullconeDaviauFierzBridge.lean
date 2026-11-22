/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Clifford.LochakRodichevFierzKrein

/-!
# $\mathbb{Z}/2$-Graded Differential Operator Algebra Over Dual Isotropic Nullcones: Daviau–Fierz Bridge

Connects the 5-axiom core `(V = N₊ ⊕ N₋, Γ, J, D)` directly to Daviau (2001) and Lochak (2007)
in real `M₈(ℝ)`:

* **Part 0 (Axioms 1–2: Cut vs. Mirror)**: formalizes `etaNullcone`, `gammaCut`, and `mirrorJ`
  on `Fin n ⊕ Fin n`, proving that confusing the cut with the mirror (`η Γ`) is skew-symmetric and
  causes total null collapse `⟨u, Γ u⟩_η = 0`, whereas indefinite negative-norm cancellation occurs
  in the diagonal form `⟨u, γ_cut u⟩` while `η J = I` restores strict positivity.
* **Part 1 (Axiom 3: Parabolic Unipotent Limit)**: formalizes `parabolicFlow Y t = 1 + t • Y`
  for unilateral nilpotent bridges `Y² = 0` (`parabolic_unipotent_monodromy` and concrete `n = 1`
  matrix witness).
* **Part 2 (Axioms 1–3 at `k = 2`: Daviau–Lochak Chiral Carrier & `SU(2)_V`)**: proves
  `lochak_fierz_takabayasi_and_proca_coupling` and diagonal unitary invariance
  `daviau_vector_su2_preserves_chiral_pairing` on `ChiralDiracSpinor = EuclideanSpace ℂ (Fin 2)²`.
* **Part 3 (Real `M₈(ℝ)` Bridge)**: maps any `Φ : Vec8R` canonically to `vec8ToChiralDiracSpinor Φ`
  using `weylXi` and `weylEta`, establishing exact equality with `omega1 Φ`, `-omega2 Φ`,
  `electricCurrentJ Φ 0`, and `axialCurrentSigma Φ 0`, plus massless collapse on `daviauPhiL`
  and `daviauPhiR`.
-/

noncomputable section

open scoped BigOperators
open Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Clifford.DaviauChiralPeirceSU2
open InfoGeometry.Clifford.LochakRodichevFierzKrein

namespace InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge

/-! ### Part 0: Nullcone Substrate, Ghost Collapse (`η Γ`), Indefinite `Γ`, & Intertwined Metric (`η J = 1`) -/

/-- Nullcone cross-pairing form `η = [[0, I], [I, 0]]` on `N₊ ⊕ N₋` (`Fin n ⊕ Fin n`). -/
def etaNullcone (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 1 1 0

/-- Perspectival $\mathbb{Z}/2$-grading / cut involution `Γ = [[I, 0], [0, -I]]` (`Γ² = 1`). -/
def gammaCut (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Nullcone swap mirror involution `J = [[0, I], [I, 0]]` (`J² = 1`, `J ≠ Γ`). -/
def mirrorJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 1 1 0

/-- **Nullcone Ghost Collapse & Intertwined Positivity Theorem**:
1. `Γ² = 1`, `J² = 1`, and `{Γ, J} = 0` (`Γ J + J Γ = 0`).
2. Replacing `J` by `Γ` inside `η` produces a skew-symmetric matrix `(η Γ)ᵀ = -(η Γ)` with
   identically vanishing quadratic form `u ⬝ᵥ (η Γ) *ᵥ u = 0` (total null collapse).
3. Inserting the true mirror `J` gives the positive-definite identity metric `η J = 1` with
   `u ⬝ᵥ (η J) *ᵥ u ≥ 0` and equality iff `u = 0`.
4. The diagonalized cut form `u ⬝ᵥ Γ *ᵥ u` is indefinite (`‖u₊‖² - ‖u₋‖²`). -/
theorem nullcone_ghost_collapse_and_intertwined_positivity (n : ℕ) :
    gammaCut n * gammaCut n = 1 ∧
    mirrorJ n * mirrorJ n = 1 ∧
    gammaCut n * mirrorJ n + mirrorJ n * gammaCut n = 0 ∧
    (etaNullcone n * gammaCut n)ᵀ = -(etaNullcone n * gammaCut n) ∧
    (∀ u : Fin n ⊕ Fin n → ℝ, dotProduct u ((etaNullcone n * gammaCut n).mulVec u) = 0) ∧
    etaNullcone n * mirrorJ n = 1 ∧
    (∀ u : Fin n ⊕ Fin n → ℝ,
      0 ≤ dotProduct u ((etaNullcone n * mirrorJ n).mulVec u) ∧
      (dotProduct u ((etaNullcone n * mirrorJ n).mulVec u) = 0 ↔ u = 0)) ∧
    (∀ u : Fin n ⊕ Fin n → ℝ,
      dotProduct u ((gammaCut n).mulVec u) =
        dotProduct (u ∘ Sum.inl) (u ∘ Sum.inl) - dotProduct (u ∘ Sum.inr) (u ∘ Sum.inr)) := by
  have hG2 : gammaCut n * gammaCut n = 1 := by
    dsimp [gammaCut]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hJ2 : mirrorJ n * mirrorJ n = 1 := by
    dsimp [mirrorJ]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hAnti : gammaCut n * mirrorJ n + mirrorJ n * gammaCut n = 0 := by
    dsimp [gammaCut, mirrorJ]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp
  have hSkew : (etaNullcone n * gammaCut n)ᵀ = -(etaNullcone n * gammaCut n) := by
    dsimp [etaNullcone, gammaCut]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
    simp
  have hCollapse : ∀ u : Fin n ⊕ Fin n → ℝ,
      dotProduct u ((etaNullcone n * gammaCut n).mulVec u) = 0 := by
    intro u
    set A := etaNullcone n * gammaCut n
    have h1 : dotProduct u (A.mulVec u) = dotProduct u (Aᵀ.mulVec u) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have h2 : dotProduct u (Aᵀ.mulVec u) = -dotProduct u (A.mulVec u) := by
      rw [hSkew, Matrix.neg_mulVec, dotProduct_neg]
    linarith
  have hPosMat : etaNullcone n * mirrorJ n = 1 := by
    dsimp [etaNullcone, mirrorJ]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hPos : ∀ u : Fin n ⊕ Fin n → ℝ,
      0 ≤ dotProduct u ((etaNullcone n * mirrorJ n).mulVec u) ∧
      (dotProduct u ((etaNullcone n * mirrorJ n).mulVec u) = 0 ↔ u = 0) := by
    intro u
    rw [hPosMat, Matrix.one_mulVec]
    have hNonneg : 0 ≤ dotProduct u u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
    refine ⟨hNonneg, ?_⟩
    constructor
    · intro hZero
      ext i
      have hTerm : u i * u i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (u j)).mp hZero i
          (Finset.mem_univ i)
      exact mul_self_eq_zero.mp hTerm
    · rintro rfl
      simp
  have hDiag : ∀ u : Fin n ⊕ Fin n → ℝ,
      dotProduct u ((gammaCut n).mulVec u) =
        dotProduct (u ∘ Sum.inl) (u ∘ Sum.inl) - dotProduct (u ∘ Sum.inr) (u ∘ Sum.inr) := by
    intro u
    dsimp [gammaCut, dotProduct, Matrix.mulVec]
    simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Matrix.one_apply, Matrix.neg_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    have hL : ∀ x : Fin n,
        (∑ y : Fin n, (if x = y then (1 : ℝ) else 0) * u (Sum.inl y)) = u (Sum.inl x) := by
      intro x
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    have hR : ∀ x : Fin n,
        (∑ y : Fin n, -(if x = y then (1 : ℝ) else 0) * u (Sum.inr y)) = -u (Sum.inr x) := by
      intro x
      simp [Finset.sum_ite_eq, Finset.mem_univ, neg_mul]
    simp_rw [hL, hR, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  exact ⟨hG2, hJ2, hAnti, hSkew, hCollapse, hPosMat, hPos, hDiag⟩

/-- When `n > 0`, `Γ ≠ J`, `Γ` and `J` do not commute, and balanced modes cancel in the
indefinite diagonal metric `⟨u, Γ u⟩ = 0` while remaining strictly positive under `⟨u, η J u⟩ = 2`. -/
theorem gammaCut_ne_mirrorJ_and_noncomm (n : ℕ) (hn : 0 < n) :
    gammaCut n ≠ mirrorJ n ∧
    gammaCut n * mirrorJ n ≠ mirrorJ n * gammaCut n ∧
    ∃ u : Fin n ⊕ Fin n → ℝ,
      dotProduct u ((gammaCut n).mulVec u) = 0 ∧
      dotProduct u ((etaNullcone n * mirrorJ n).mulVec u) = 2 := by
  let i0 : Fin n := ⟨0, hn⟩
  have hne : gammaCut n ≠ mirrorJ n := by
    intro h
    have he := congrArg (fun M => M (Sum.inl i0) (Sum.inl i0)) h
    simp [gammaCut, mirrorJ] at he
  have hnc : gammaCut n * mirrorJ n ≠ mirrorJ n * gammaCut n := by
    intro h
    have he := congrArg (fun M => M (Sum.inl i0) (Sum.inr i0)) h
    dsimp [gammaCut, mirrorJ] at he
    simp [Matrix.fromBlocks_multiply] at he
    norm_num at he
  let e0 : Fin n → ℝ := fun i => if i = i0 then 1 else 0
  let u : Fin n ⊕ Fin n → ℝ := Sum.elim e0 e0
  have he0 : dotProduct e0 e0 = 1 := by
    dsimp [dotProduct, e0]
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; simp [hb]
    · intro hm; exact False.elim (hm (Finset.mem_univ _))
  have hDiag := (nullcone_ghost_collapse_and_intertwined_positivity n).2.2.2.2.2.2.2 u
  have hPosMat : etaNullcone n * mirrorJ n = 1 :=
    (nullcone_ghost_collapse_and_intertwined_positivity n).2.2.2.2.2.1
  have huL : u ∘ Sum.inl = e0 := rfl
  have huR : u ∘ Sum.inr = e0 := rfl
  have hIndef : dotProduct u ((gammaCut n).mulVec u) = 0 := by
    rw [hDiag, huL, huR, sub_self]
  have hInt : dotProduct u ((etaNullcone n * mirrorJ n).mulVec u) = 2 := by
    rw [hPosMat, Matrix.one_mulVec]
    dsimp [dotProduct, u]
    rw [Fintype.sum_sum_type]
    change dotProduct e0 e0 + dotProduct e0 e0 = 2
    rw [he0]
    norm_num
  exact ⟨hne, hnc, u, hIndef, hInt⟩

/-- Concrete `n = 1` cut involution `Γ₁ = diag(1, -1)` on `ℝ ⊕ ℝ`. -/
def gammaCut1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := gammaCut 1

/-- Concrete `n = 1` mirror involution `J₁ = [[0, 1], [1, 0]]` on `ℝ ⊕ ℝ`. -/
def mirrorJ1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := mirrorJ 1

theorem gammaCut1_mul_mirrorJ1_ne : gammaCut1 * mirrorJ1 ≠ mirrorJ1 * gammaCut1 :=
  (gammaCut_ne_mirrorJ_and_noncomm 1 Nat.one_pos).2.1

/-! ### Part 1: Axiom 3 Unilateral Parabolic Limit -> Unipotent Jordan Monodromy U(t) = 1 + t Y -/

/-- Unipotent parabolic flow `U(t) = 1 + t • Y` generated by a unilateral nilpotent corner `Y`
(`Y * Y = 0`). -/
def parabolicFlow {R B : Type*} [CommRing R] [Ring B] [Algebra R B] (Y : B) (t : R) : B :=
  1 + t • Y

/-- **Parabolic Unipotent Monodromy Theorem**:
When the off-diagonal bridge is unilateral (`X = 0`, `F = Y`, `Y² = 0`), the flow `U(t) = 1 + t Y`
forms an additive 1-parameter subgroup (`U(t₁) U(t₂) = U(t₁ + t₂)`, `U(0) = 1`, `U(-t) = U(t)⁻¹`)
with index-2 Jordan defect `(U(t) - 1)² = 0`. -/
theorem parabolic_unipotent_monodromy {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (Y : B) (hY2 : Y * Y = 0) (t₁ t₂ : R) :
    parabolicFlow Y (0 : R) = 1 ∧
    parabolicFlow Y t₁ * parabolicFlow Y t₂ = parabolicFlow Y (t₁ + t₂) ∧
    (parabolicFlow Y t₁ - 1) * (parabolicFlow Y t₁ - 1) = 0 := by
  unfold parabolicFlow
  refine ⟨by rw [zero_smul, add_zero], ?_, ?_⟩
  · calc (1 + t₁ • Y) * (1 + t₂ • Y)
        = (1 + t₁ • Y) + t₂ • (Y + t₁ • (Y * Y)) := by
            rw [mul_add, mul_one, Algebra.mul_smul_comm, add_mul, one_mul, Algebra.smul_mul_assoc]
      _ = 1 + (t₁ + t₂) • Y := by
            rw [hY2, smul_zero, add_zero, add_assoc, ← add_smul]
  · calc (1 + t₁ • Y - 1) * (1 + t₁ • Y - 1)
        = (t₁ • Y) * (t₁ • Y) := by noncomm_ring
      _ = (t₁ * t₁) • (Y * Y) := by
            rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      _ = 0 := by rw [hY2, smul_zero]

/-- Two-sided inverse law `U(t) U(-t) = U(-t) U(t) = 1` for parabolic unipotent monodromy. -/
theorem parabolicFlow_inv_right_left {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (Y : B) (hY2 : Y * Y = 0) (t : R) :
    parabolicFlow Y t * parabolicFlow Y (-t) = 1 ∧
    parabolicFlow Y (-t) * parabolicFlow Y t = 1 := by
  have h1 := parabolic_unipotent_monodromy Y hY2 t (-t)
  have h2 := parabolic_unipotent_monodromy Y hY2 (-t) t
  refine ⟨?_, ?_⟩
  · rw [h1.2.1, add_neg_cancel, h1.1]
  · rw [h2.2.1, neg_add_cancel, h2.1]

/-- Concrete `n = 1` unilateral Jordan bridge witness `Y = [[0, 1], [0, 0]]`:
`Y ≠ 0`, `Y² = 0`, `{Γ, Y} = 0`, and `U(t) = 1 + t Y` obeys `U(t₁) U(t₂) = U(t₁ + t₂)`. -/
theorem unilateral_jordan_block_witness (t₁ t₂ : ℝ) :
    let Y : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := Matrix.fromBlocks 0 1 0 0
    Y ≠ 0 ∧
    Y * Y = 0 ∧
    gammaCut 1 * Y + Y * gammaCut 1 = 0 ∧
    parabolicFlow Y t₁ * parabolicFlow Y t₂ = parabolicFlow Y (t₁ + t₂) := by
  intro Y
  have hne : Y ≠ 0 := by
    intro h
    have he := congrArg (fun M => M (Sum.inl 0) (Sum.inr 0)) h
    simp [Y] at he
  have hY2 : Y * Y = 0 := by
    dsimp [Y]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hOdd : gammaCut 1 * Y + Y * gammaCut 1 = 0 := by
    dsimp [gammaCut, Y]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp
  exact ⟨hne, hY2, hOdd, (parabolic_unipotent_monodromy Y hY2 t₁ t₂).2.1⟩

/-! ### Part 2: k = 2 Daviau Chiral Peirce Carrier, Lochak-Fierz Invariants, & SU(2)_V Symmetry -/

/-- Doubled chiral Dirac/Daviau spinor `(ψ₊, ψ₋) ∈ ℂ² × ℂ²` sitting on the two null sheets `N₊ ⊕ N₋`. -/
abbrev ChiralDiracSpinor := EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)

/-- Fierz scalar bilinear `Ω₁(ψ) = 2 Re⟨ψ₊, ψ₋⟩ = ⟨ψ, J ψ⟩` generated by the mirror `J = γ⁰`. -/
def fierzScalar (ψ : ChiralDiracSpinor) : ℝ :=
  2 * (inner ℂ ψ.1 ψ.2).re

/-- Fierz pseudoscalar bilinear `Ω₂(ψ) = 2 Im⟨ψ₊, ψ₋⟩` generated by `J Γ = γ⁰ γ⁵`. -/
def fierzPseudoscalar (ψ : ChiralDiracSpinor) : ℝ :=
  2 * (inner ℂ ψ.1 ψ.2).im

/-- Positive-definite Krein-intertwined probability density `j⁰(ψ) = ‖ψ₊‖² + ‖ψ₋‖²`. -/
def kreinProbDensity (ψ : ChiralDiracSpinor) : ℝ :=
  ‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2

/-- Chiral axial density `k⁰(ψ) = ‖ψ₊‖² - ‖ψ₋‖²` (cut expectation `⟨ψ, Γ ψ⟩_ℋ`). -/
def chiralAxialDensity (ψ : ChiralDiracSpinor) : ℝ :=
  ‖ψ.1‖ ^ 2 - ‖ψ.2‖ ^ 2

/-- **Lochak–Rodichev–Fierz–Krein Identity & Proca Mass Coupling Theorem**:
1. Exact Fierz–Takabayasi identity: `Ω₁² + Ω₂² = 4 ‖⟨ψ₊, ψ₋⟩‖²`.
2. **Fierz–Pauli–Kofink Inequality**:
   `Ω₁² + Ω₂² ≤ (j⁰)² - (k⁰)² = 4 ‖ψ₊‖² ‖ψ₋‖²`.
3. **Weyl/Photon Massless Decoupling**: if either chiral nullcone vanishes (`ψ₊ = 0 ∨ ψ₋ = 0`),
   then `Ω₁² + Ω₂² = 0` and `(k⁰)² = (j⁰)²` (null chiral lightlike regime). -/
theorem lochak_fierz_takabayasi_and_proca_coupling (ψ : ChiralDiracSpinor) :
    fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 = 4 * ‖inner ℂ ψ.1 ψ.2‖ ^ 2 ∧
    fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 ≤
      kreinProbDensity ψ ^ 2 - chiralAxialDensity ψ ^ 2 ∧
    (ψ.1 = 0 ∨ ψ.2 = 0 →
      fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 = 0 ∧
      chiralAxialDensity ψ ^ 2 = kreinProbDensity ψ ^ 2) := by
  have hMod : fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 = 4 * ‖inner ℂ ψ.1 ψ.2‖ ^ 2 := by
    unfold fierzScalar fierzPseudoscalar
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hCS : ‖inner ℂ ψ.1 ψ.2‖ ^ 2 ≤ ‖ψ.1‖ ^ 2 * ‖ψ.2‖ ^ 2 := by
    calc ‖inner ℂ ψ.1 ψ.2‖ ^ 2 ≤ (‖ψ.1‖ * ‖ψ.2‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ψ.1 ψ.2) 2
      _ = ‖ψ.1‖ ^ 2 * ‖ψ.2‖ ^ 2 := by ring
  have hDiff : kreinProbDensity ψ ^ 2 - chiralAxialDensity ψ ^ 2 =
      4 * (‖ψ.1‖ ^ 2 * ‖ψ.2‖ ^ 2) := by
    unfold kreinProbDensity chiralAxialDensity
    ring
  refine ⟨hMod, ?_, ?_⟩
  · rw [hMod, hDiff]
    linarith
  · intro hNull
    rcases hNull with h1 | h2
    · have h0 : inner ℂ ψ.1 ψ.2 = 0 := by rw [h1, inner_zero_left]
      have hNorm0 : ‖ψ.1‖ = 0 := by rw [h1, norm_zero]
      refine ⟨by rw [hMod, h0, norm_zero]; norm_num, ?_⟩
      unfold kreinProbDensity chiralAxialDensity
      rw [hNorm0]; ring
    · have h0 : inner ℂ ψ.1 ψ.2 = 0 := by rw [h2, inner_zero_right]
      have hNorm0 : ‖ψ.2‖ = 0 := by rw [h2, norm_zero]
      refine ⟨by rw [hMod, h0, norm_zero]; norm_num, ?_⟩
      unfold kreinProbDensity chiralAxialDensity
      rw [hNorm0]; ring

/-- Diagonal unitary gauge invariance on the complex chiral cross-pairing:
any `U ∈ U(2)` (in particular `SU(2)_V`) acting simultaneously on both chiral sheets
`ψ₊ ↦ U ψ₊`, `ψ₋ ↦ U ψ₋` preserves the complex Fierz pairing `⟨ψ₊, ψ₋⟩ = ∑ conj(ψ₊ᵢ) ψ₋ᵢ`
and therefore preserves both `Ω₁` and `Ω₂`. -/
theorem daviau_vector_su2_preserves_chiral_pairing
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (u v : Fin 2 → ℂ) :
    dotProduct (star (U.mulVec u)) (U.mulVec v) = dotProduct (star u) v := by
  have hStar : star (U.mulVec u) = (Uᴴ).vecMul (star u) := by
    ext j
    simp only [Pi.star_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, star_sum, star_mul']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [hStar, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/-- Concrete `2 × 2` Pauli `X` matrix on `ℂ²`. -/
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Concrete `2 × 2` Pauli `Z` matrix on `ℂ²`. -/
def pauliZ2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauliX2_mul_pauliZ2_ne : pauliX2 * pauliZ2 ≠ pauliZ2 * pauliX2 := by
  intro h
  have he := congrArg (fun M => (M 0 1).re) h
  simp [pauliX2, pauliZ2, Matrix.mul_apply, Fin.sum_univ_two] at he
  norm_num at he

private lemma norm_sq_euclidean2 (x : EuclideanSpace ℂ (Fin 2)) :
    ‖x‖ ^ 2 = (dotProduct (star x.ofLp) x.ofLp).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    dotProduct, Pi.star_apply, Complex.add_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Full bilinear invariance of `(Ω₁, Ω₂, j⁰, k⁰)` under diagonal `U(2)` / `SU(2)_V` transformations
`ψ₊ ↦ U ψ₊`, `ψ₋ ↦ U ψ₋`. -/
theorem daviau_vector_su2_preserves_fierz_invariants
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (ψ : ChiralDiracSpinor) :
    let ψ' : ChiralDiracSpinor :=
      (WithLp.toLp 2 (U.mulVec ψ.1.ofLp), WithLp.toLp 2 (U.mulVec ψ.2.ofLp))
    fierzScalar ψ' = fierzScalar ψ ∧
    fierzPseudoscalar ψ' = fierzPseudoscalar ψ ∧
    kreinProbDensity ψ' = kreinProbDensity ψ ∧
    chiralAxialDensity ψ' = chiralAxialDensity ψ := by
  intro ψ'
  have hInner : inner ℂ ψ'.1 ψ'.2 = inner ℂ ψ.1 ψ.2 := by
    dsimp [ψ']
    rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm _ (star (U.mulVec ψ.1.ofLp)),
      daviau_vector_su2_preserves_chiral_pairing U hU ψ.1.ofLp ψ.2.ofLp, dotProduct_comm]
  have hN1 : ‖ψ'.1‖ ^ 2 = ‖ψ.1‖ ^ 2 := by
    rw [norm_sq_euclidean2 ψ'.1, norm_sq_euclidean2 ψ.1]
    change (dotProduct (star (U.mulVec ψ.1.ofLp)) (U.mulVec ψ.1.ofLp)).re =
      (dotProduct (star ψ.1.ofLp) ψ.1.ofLp).re
    rw [daviau_vector_su2_preserves_chiral_pairing U hU ψ.1.ofLp ψ.1.ofLp]
  have hN2 : ‖ψ'.2‖ ^ 2 = ‖ψ.2‖ ^ 2 := by
    rw [norm_sq_euclidean2 ψ'.2, norm_sq_euclidean2 ψ.2]
    change (dotProduct (star (U.mulVec ψ.2.ofLp)) (U.mulVec ψ.2.ofLp)).re =
      (dotProduct (star ψ.2.ofLp) ψ.2.ofLp).re
    rw [daviau_vector_su2_preserves_chiral_pairing U hU ψ.2.ofLp ψ.2.ofLp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [fierzScalar, hInner]
  · simp [fierzPseudoscalar, hInner]
  · simp [kreinProbDensity, hN1, hN2]
  · simp [chiralAxialDensity, hN1, hN2]

/-! ### Part 3: Canonical Bridge from Real `M₈(ℝ)` Spinors (`LochakRodichevFierzKrein`) -/

/-- Canonical map sending a real 8-component Dirac spinor `Φ ∈ ℝ⁸` to the complex Weyl/chiral
nullcone pair `(ξ(Φ), η(Φ)) ∈ EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)`. -/
def vec8ToChiralDiracSpinor (Φ : Vec8R) : ChiralDiracSpinor :=
  (WithLp.toLp 2 (weylXi Φ), WithLp.toLp 2 (weylEta Φ))

theorem inner_vec8ToChiralDiracSpinor (Φ : Vec8R) :
    inner ℂ (vec8ToChiralDiracSpinor Φ).1 (vec8ToChiralDiracSpinor Φ).2 = weylCrossInner Φ := by
  dsimp [vec8ToChiralDiracSpinor, weylCrossInner]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Fin.sum_univ_two]
  rw [mul_comm (weylEta Φ 0), mul_comm (weylEta Φ 1)]
  rfl

theorem fierzScalar_vec8ToChiralDiracSpinor (Φ : Vec8R) :
    fierzScalar (vec8ToChiralDiracSpinor Φ) = omega1 Φ := by
  dsimp [fierzScalar]
  rw [inner_vec8ToChiralDiracSpinor, weylCrossInner_re]
  ring

theorem fierzPseudoscalar_vec8ToChiralDiracSpinor (Φ : Vec8R) :
    fierzPseudoscalar (vec8ToChiralDiracSpinor Φ) = -omega2 Φ := by
  dsimp [fierzPseudoscalar]
  rw [inner_vec8ToChiralDiracSpinor, weylCrossInner_im]
  ring

theorem kreinProbDensity_vec8ToChiralDiracSpinor (Φ : Vec8R) :
    kreinProbDensity (vec8ToChiralDiracSpinor Φ) = electricCurrentJ Φ 0 := by
  dsimp [kreinProbDensity, vec8ToChiralDiracSpinor]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, electricCurrentJ0_expand]
  simp only [Fin.sum_univ_two, weylXi, weylEta, phiToPsi,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul, add_zero]
  linear_combination 2 * (Φ 0 ^ 2 + Φ 1 ^ 2 + Φ 2 ^ 2 + Φ 3 ^ 2 +
    Φ 4 ^ 2 + Φ 5 ^ 2 + Φ 6 ^ 2 + Φ 7 ^ 2) * inv_sqrt2_sq

theorem chiralAxialDensity_vec8ToChiralDiracSpinor (Φ : Vec8R) :
    chiralAxialDensity (vec8ToChiralDiracSpinor Φ) = axialCurrentSigma Φ 0 := by
  dsimp [chiralAxialDensity, vec8ToChiralDiracSpinor]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axialCurrentSigma0_expand]
  simp only [Fin.sum_univ_two, weylXi, weylEta, phiToPsi,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul, add_zero]
  linear_combination 4 * (Φ 0 * Φ 7 - Φ 1 * Φ 6 - Φ 2 * Φ 5 + Φ 3 * Φ 4) * inv_sqrt2_sq

/-- Daviau's left-chiral neutrino spinor `Φ_L` maps to the unilateral nullcone `(0, η)`. -/
theorem vec8ToChiralDiracSpinor_daviauPhiL (a : Fin 4 → ℝ) :
    (vec8ToChiralDiracSpinor (daviauPhiL a)).1 = 0 := by
  ext k
  fin_cases k <;>
    simp [vec8ToChiralDiracSpinor, weylXi, phiToPsi, daviauPhiL] <;>
    exact Complex.ext (by simp) (by simp)

/-- Daviau's right-chiral antineutrino spinor `Φ_R` maps to the opposite unilateral nullcone `(ξ, 0)`. -/
theorem vec8ToChiralDiracSpinor_daviauPhiR (b : Fin 4 → ℝ) :
    (vec8ToChiralDiracSpinor (daviauPhiR b)).2 = 0 := by
  ext k
  fin_cases k <;>
    simp [vec8ToChiralDiracSpinor, weylEta, phiToPsi, daviauPhiR]

/-- **Unified Real `M₈(ℝ)` Graded-Nullcone Fierz Bridge Theorem**:
Connects the Hilbert-space Fierz invariants on `ChiralDiracSpinor = ℂ²₊ ⊕ ℂ²₋` directly back
to Daviau's and Lochak's real `M₈(ℝ)` densities `(Ω₁, Ω₂, J⁰, Σ⁰)` for every `Φ ∈ ℝ⁸`,
establishing:
1. Exact identification `fierzScalar = Ω₁`, `fierzPseudoscalar = -Ω₂`, `kreinProbDensity = J⁰`,
   `chiralAxialDensity = Σ⁰`,
2. Real `M₈(ℝ)` Fierz–Pauli–Kofink inequality `Ω₁² + Ω₂² ≤ (J⁰)² - (Σ⁰)²`,
3. Unilateral massless chiral collapse `Ω₁² + Ω₂² = 0` and `(Σ⁰)² = (J⁰)²` on both `Φ_L` and `Φ_R`. -/
theorem realDirac8_gradedNullcone_fierz_bridge :
    (∀ Φ : Vec8R,
      fierzScalar (vec8ToChiralDiracSpinor Φ) = omega1 Φ ∧
      fierzPseudoscalar (vec8ToChiralDiracSpinor Φ) = -omega2 Φ ∧
      kreinProbDensity (vec8ToChiralDiracSpinor Φ) = electricCurrentJ Φ 0 ∧
      chiralAxialDensity (vec8ToChiralDiracSpinor Φ) = axialCurrentSigma Φ 0 ∧
      omega1 Φ ^ 2 + omega2 Φ ^ 2 ≤ electricCurrentJ Φ 0 ^ 2 - axialCurrentSigma Φ 0 ^ 2) ∧
    (∀ a : Fin 4 → ℝ,
      omega1 (daviauPhiL a) ^ 2 + omega2 (daviauPhiL a) ^ 2 = 0 ∧
      axialCurrentSigma (daviauPhiL a) 0 ^ 2 = electricCurrentJ (daviauPhiL a) 0 ^ 2) ∧
    (∀ b : Fin 4 → ℝ,
      omega1 (daviauPhiR b) ^ 2 + omega2 (daviauPhiR b) ^ 2 = 0 ∧
      axialCurrentSigma (daviauPhiR b) 0 ^ 2 = electricCurrentJ (daviauPhiR b) 0 ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ
    have hMain := lochak_fierz_takabayasi_and_proca_coupling (vec8ToChiralDiracSpinor Φ)
    have h1 := fierzScalar_vec8ToChiralDiracSpinor Φ
    have h2 := fierzPseudoscalar_vec8ToChiralDiracSpinor Φ
    have hJ := kreinProbDensity_vec8ToChiralDiracSpinor Φ
    have hS := chiralAxialDensity_vec8ToChiralDiracSpinor Φ
    have hIneq : omega1 Φ ^ 2 + omega2 Φ ^ 2 ≤
        electricCurrentJ Φ 0 ^ 2 - axialCurrentSigma Φ 0 ^ 2 := by
      have hle := hMain.2.1
      rw [h1, h2, hJ, hS] at hle
      simpa [neg_sq] using hle
    exact ⟨h1, h2, hJ, hS, hIneq⟩
  · intro a
    have hL := (lochak_fierz_takabayasi_and_proca_coupling
      (vec8ToChiralDiracSpinor (daviauPhiL a))).2.2
      (Or.inl (vec8ToChiralDiracSpinor_daviauPhiL a))
    rw [fierzScalar_vec8ToChiralDiracSpinor, fierzPseudoscalar_vec8ToChiralDiracSpinor,
      kreinProbDensity_vec8ToChiralDiracSpinor, chiralAxialDensity_vec8ToChiralDiracSpinor] at hL
    simpa [neg_sq] using hL
  · intro b
    have hR := (lochak_fierz_takabayasi_and_proca_coupling
      (vec8ToChiralDiracSpinor (daviauPhiR b))).2.2
      (Or.inr (vec8ToChiralDiracSpinor_daviauPhiR b))
    rw [fierzScalar_vec8ToChiralDiracSpinor, fierzPseudoscalar_vec8ToChiralDiracSpinor,
      kreinProbDensity_vec8ToChiralDiracSpinor, chiralAxialDensity_vec8ToChiralDiracSpinor] at hR
    simpa [neg_sq] using hR

end InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge
