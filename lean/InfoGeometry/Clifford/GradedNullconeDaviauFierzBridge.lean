/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import InfoGeometry.Clifford.SplitCl11GradedTensorTower

/-!
# $\mathbb{Z}/2$-Graded Differential Operator Algebra Over Dual Isotropic Nullcones: Daviau–Fierz Bridge

Connects the 5-axiom core `(V = N₊ ⊕ N₋, Γ, J, D)` directly to Daviau (2001) and Lochak (2007)
in real `M₈(ℝ)`:

* **Part 0 (Axioms 1–2: Cut vs. Mirror)**: formalizes `etaNullcone`, `gammaCut`, and `mirrorJ`
  on `Fin n ⊕ Fin n`, proving that confusing the cut with the mirror (`η Γ`) is skew-symmetric and
  causes total null collapse `⟨u, Γ u⟩_η = 0`, whereas indefinite negative-norm cancellation occurs
  in the diagonal form `⟨u, γ_cut u⟩` while `η J = I` restores strict positivity.
* **Part 1 (Axiom 3: Parabolic Unipotent Limit)**: formalizes `parabolicFlow Y t = 1 + t • Y`
  for square-zero bridges `Y² = 0` (`parabolic_unipotent_flow_laws`, a separate inverse law, and
  a concrete `n = 1` matrix witness). These algebraic laws do not construct topological monodromy.
* **Part 2 (Axioms 1–3 at `k = 2`: Daviau–Lochak Chiral Carrier & `U(2)`)**: proves
  algebraic Fierz–Takabayasi identities and diagonal unitary invariance
  `daviau_vector_su2_preserves_chiral_pairing` on `ChiralDiracSpinor = EuclideanSpace ℂ (Fin 2)²`.
  These are finite-dimensional bilinear identities, not Proca field equations or dynamics.
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
open InfoGeometry.Clifford.SplitCl11GradedTensorTower

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

/-- The diagonal cut form has an explicit positive and negative unit direction whenever
`n > 0`. This is the indefinite-signature phenomenon; it is distinct from the
identically-zero null-cone pairing obtained by inserting `Γ` into `η`. -/
theorem gammaCut_has_both_signs (n : ℕ) (hn : 0 < n) :
    ∃ u v : Fin n ⊕ Fin n → ℝ,
      dotProduct u ((gammaCut n).mulVec u) = 1 ∧
      dotProduct v ((gammaCut n).mulVec v) = -1 := by
  let i0 : Fin n := ⟨0, hn⟩
  let e0 : Fin n → ℝ := fun i => if i = i0 then 1 else 0
  let u : Fin n ⊕ Fin n → ℝ := Sum.elim e0 (fun _ => 0)
  let v : Fin n ⊕ Fin n → ℝ := Sum.elim (fun _ => 0) e0
  have he0 : dotProduct e0 e0 = 1 := by
    dsimp [dotProduct, e0]
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hm
      exact False.elim (hm (Finset.mem_univ _))
  have hDiag := (nullcone_ghost_collapse_and_intertwined_positivity n).2.2.2.2.2.2.2
  have huL : u ∘ Sum.inl = e0 := rfl
  have huR : u ∘ Sum.inr = 0 := rfl
  have hvL : v ∘ Sum.inl = 0 := rfl
  have hvR : v ∘ Sum.inr = e0 := rfl
  refine ⟨u, v, ?_, ?_⟩
  · rw [hDiag u, huL, huR, dotProduct_zero, he0]
    norm_num
  · rw [hDiag v, hvL, hvR, dotProduct_zero, he0]
    norm_num

/-- Concrete `n = 1` cut involution `Γ₁ = diag(1, -1)` on `ℝ ⊕ ℝ`. -/
def gammaCut1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := gammaCut 1

/-- Concrete `n = 1` mirror involution `J₁ = [[0, 1], [1, 0]]` on `ℝ ⊕ ℝ`. -/
def mirrorJ1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := mirrorJ 1

theorem gammaCut1_mul_mirrorJ1_ne : gammaCut1 * mirrorJ1 ≠ mirrorJ1 * gammaCut1 :=
  (gammaCut_ne_mirrorJ_and_noncomm 1 Nat.one_pos).2.1

/-! ### Part 1: Axiom 3 Unilateral Parabolic Limit -> Unipotent Additive Flow U(t) = 1 + t Y -/

/-- Unipotent parabolic flow `U(t) = 1 + t • Y` generated by a unilateral nilpotent corner `Y`
(`Y * Y = 0`). -/
def parabolicFlow {R B : Type*} [CommRing R] [Ring B] [Algebra R B] (Y : B) (t : R) : B :=
  1 + t • Y

/-- **Parabolic unipotent additive-flow laws**:
For a square-zero element `Y`, `U(t) = 1 + t Y` has unit `U(0)`, satisfies
`U(t₁) U(t₂) = U(t₁ + t₂)`, and has square-zero displacement `(U(t) - 1)²`.
The inverse law is proved separately; this statement constructs no topological monodromy. -/
theorem parabolic_unipotent_flow_laws {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
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

/-- Two-sided inverse law `U(t) U(-t) = U(-t) U(t) = 1` for the unipotent additive flow. -/
theorem parabolicFlow_inv_right_left {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (Y : B) (hY2 : Y * Y = 0) (t : R) :
    parabolicFlow Y t * parabolicFlow Y (-t) = 1 ∧
    parabolicFlow Y (-t) * parabolicFlow Y t = 1 := by
  have h1 := parabolic_unipotent_flow_laws Y hY2 t (-t)
  have h2 := parabolic_unipotent_flow_laws Y hY2 (-t) t
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
  exact ⟨hne, hY2, hOdd, (parabolic_unipotent_flow_laws Y hY2 t₁ t₂).2.1⟩

/-! ### Part 2: k = 2 Daviau Chiral Peirce Carrier, Lochak-Fierz Invariants, & SU(2)_V Symmetry -/

/-- Doubled chiral Dirac/Daviau spinor `(ψ₊, ψ₋) ∈ ℂ² × ℂ²` sitting on the two null sheets `N₊ ⊕ N₋`. -/
abbrev ChiralDiracSpinor := EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)

/-- Fierz scalar bilinear `Ω₁(ψ) = 2 Re⟨ψ₊, ψ₋⟩ = ⟨ψ, J ψ⟩` generated by the mirror `J = γ⁰`. -/
def fierzScalar (ψ : ChiralDiracSpinor) : ℝ :=
  2 * (inner ℂ ψ.1 ψ.2).re

/-- Real pseudoscalar readout `Ω₂(ψ) = 2 Im⟨ψ₊, ψ₋⟩` under the repository's
`-i ψ† γ⁰ γ⁵ ψ` convention. The factor `-i` makes the Dirac bilinear real. -/
def fierzPseudoscalar (ψ : ChiralDiracSpinor) : ℝ :=
  2 * (inner ℂ ψ.1 ψ.2).im

/-- Positive-definite Krein-intertwined probability density `j⁰(ψ) = ‖ψ₊‖² + ‖ψ₋‖²`. -/
def kreinProbDensity (ψ : ChiralDiracSpinor) : ℝ :=
  ‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2

/-- Chiral axial density `k⁰(ψ) = ‖ψ₊‖² - ‖ψ₋‖²` (cut expectation `⟨ψ, Γ ψ⟩_ℋ`). -/
def chiralAxialDensity (ψ : ChiralDiracSpinor) : ℝ :=
  ‖ψ.1‖ ^ 2 - ‖ψ.2‖ ^ 2

/-- Chiral cut/grading: it is `+1` on the first Weyl component and `-1` on the second. -/
def chiralGrading (ψ : ChiralDiracSpinor) : ChiralDiracSpinor := (ψ.1, -ψ.2)

/-- Chiral mirror: it swaps the two Weyl components. -/
def chiralMirror (ψ : ChiralDiracSpinor) : ChiralDiracSpinor := (ψ.2, ψ.1)

/-- Positive Hilbert pairing on the doubled Weyl carrier. -/
def chiralHilbertPairing (ψ χ : ChiralDiracSpinor) : ℂ :=
  inner ℂ ψ.1 χ.1 + inner ℂ ψ.2 χ.2

/-- The real Fierz readouts are the mirror and mirror-after-cut components of the positive
Hilbert pairing. The `I` factor fixes the repository's real pseudoscalar convention. -/
theorem fierz_readouts_from_mirror_and_cut (ψ : ChiralDiracSpinor) :
    fierzScalar ψ = (chiralHilbertPairing ψ (chiralMirror ψ)).re ∧
    fierzPseudoscalar ψ =
      (Complex.I * chiralHilbertPairing ψ (chiralMirror (chiralGrading ψ))).re := by
  have hSymm : inner ℂ ψ.2 ψ.1 = star (inner ℂ ψ.1 ψ.2) :=
    (inner_conj_symm ψ.2 ψ.1).symm
  have hIm : (inner ℂ ψ.2 ψ.1).im = -(inner ℂ ψ.1 ψ.2).im := by
    rw [hSymm, Complex.star_def, Complex.conj_im]
  have hRe : (inner ℂ ψ.2 ψ.1).re = (inner ℂ ψ.1 ψ.2).re := by
    simpa only [Complex.star_def, Complex.conj_re] using
      congrArg Complex.re hSymm
  constructor
  · simp only [fierzScalar, chiralHilbertPairing, chiralMirror, Complex.add_re]
    rw [hRe]
    ring
  · simp only [fierzPseudoscalar, chiralHilbertPairing, chiralMirror,
      chiralGrading, inner_neg_right, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.add_im, Complex.neg_im]
    rw [hIm]
    ring

/-- **Lochak–Rodichev–Fierz–Krein bilinear identities and chiral decoupling**:
1. Exact Fierz–Takabayasi identity: `Ω₁² + Ω₂² = 4 ‖⟨ψ₊, ψ₋⟩‖²`.
2. **Fierz–Pauli–Kofink Inequality**:
   `Ω₁² + Ω₂² ≤ (j⁰)² - (k⁰)² = 4 ‖ψ₊‖² ‖ψ₋‖²`.
3. If either chiral component vanishes (`ψ₊ = 0 ∨ ψ₋ = 0`), then
   `Ω₁² + Ω₂² = 0` and `(k⁰)² = (j⁰)²`. This is an algebraic statement and does not
   establish photon/Proca dynamics. -/
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

/-- The scalar-pseudoscalar invariant is positive exactly when the two chiral
components have nonzero cross inner product. Nonzero components alone do not suffice. -/
theorem fierz_invariant_pos_iff_cross_inner_ne_zero (ψ : ChiralDiracSpinor) :
    0 < fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 ↔
      inner ℂ ψ.1 ψ.2 ≠ 0 := by
  have hMod : fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 =
      4 * ‖inner ℂ ψ.1 ψ.2‖ ^ 2 := by
    unfold fierzScalar fierzPseudoscalar
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hMod]
  constructor
  · intro h
    apply norm_pos_iff.mp
    nlinarith [norm_nonneg (inner ℂ ψ.1 ψ.2)]
  · intro h
    have hn : 0 < ‖inner ℂ ψ.1 ψ.2‖ := norm_pos_iff.mpr h
    nlinarith

/-- Both chiral sheets can be nonzero while the Fierz invariant vanishes:
orthogonal coordinate spinors have zero cross inner product. -/
theorem nonzero_chiral_sheets_can_have_zero_fierz_invariant :
    ∃ ψ : ChiralDiracSpinor,
      ψ.1 ≠ 0 ∧ ψ.2 ≠ 0 ∧
        fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 = 0 := by
  let u : EuclideanSpace ℂ (Fin 2) :=
    WithLp.toLp 2 (fun i => if i = 0 then (1 : ℂ) else 0)
  let v : EuclideanSpace ℂ (Fin 2) :=
    WithLp.toLp 2 (fun i => if i = 1 then (1 : ℂ) else 0)
  have hu : u ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x.ofLp 0) h
    norm_num [u] at h0
  have hv : v ≠ 0 := by
    intro h
    have h1 := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x.ofLp 1) h
    norm_num [v] at h1
  have huv : inner ℂ u v = 0 := by
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct]
  refine ⟨(u, v), hu, hv, ?_⟩
  rw [(lochak_fierz_takabayasi_and_proca_coupling (u, v)).1, huv]
  norm_num

/-- The Fierz upper bound is sharp: equal chiral components attain equality. In particular
the general inequality is not strict. -/
theorem lochak_fierz_bound_attained_on_equal_sheets
    (u : EuclideanSpace ℂ (Fin 2)) :
    let ψ : ChiralDiracSpinor := (u, u)
    fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 =
      kreinProbDensity ψ ^ 2 - chiralAxialDensity ψ ^ 2 := by
  have hRe : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    exact RCLike.re_ofReal_pow (K := ℂ) ‖u‖ 2
  have hIm : (inner ℂ u u).im = 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    exact RCLike.im_ofReal_pow (K := ℂ) ‖u‖ 2
  dsimp
  simp only [fierzScalar, fierzPseudoscalar, kreinProbDensity, chiralAxialDensity]
  rw [hRe, hIm]
  ring

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

/-- The diagonal vector action applies one matrix to both chiral sheets. -/
def diagonalVectorAction (U : Matrix (Fin 2) (Fin 2) ℂ) (ψ : ChiralDiracSpinor) :
    ChiralDiracSpinor :=
  (WithLp.toLp 2 (U.mulVec ψ.1.ofLp), WithLp.toLp 2 (U.mulVec ψ.2.ofLp))

/-- Applying the same matrix on both sheets commutes with the sheet-swap mirror. -/
theorem diagonalVectorAction_commutes_mirror
    (U : Matrix (Fin 2) (Fin 2) ℂ) (ψ : ChiralDiracSpinor) :
    diagonalVectorAction U (chiralMirror ψ) = chiralMirror (diagonalVectorAction U ψ) := by
  rfl

/-- Applying the same matrix on both sheets commutes with the chiral cut. -/
theorem diagonalVectorAction_commutes_grading
    (U : Matrix (Fin 2) (Fin 2) ℂ) (ψ : ChiralDiracSpinor) :
    diagonalVectorAction U (chiralGrading ψ) = chiralGrading (diagonalVectorAction U ψ) := by
  simp [diagonalVectorAction, chiralGrading, Matrix.mulVec_neg, WithLp.toLp_neg]

/-- Full bilinear invariance of `(Ω₁, Ω₂, j⁰, k⁰)` under diagonal `U(2)` / `SU(2)_V` transformations
`ψ₊ ↦ U ψ₊`, `ψ₋ ↦ U ψ₋`. -/
theorem daviau_vector_su2_preserves_fierz_invariants
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (ψ : ChiralDiracSpinor) :
    let ψ' : ChiralDiracSpinor := diagonalVectorAction U ψ
    fierzScalar ψ' = fierzScalar ψ ∧
    fierzPseudoscalar ψ' = fierzPseudoscalar ψ ∧
    kreinProbDensity ψ' = kreinProbDensity ψ ∧
    chiralAxialDensity ψ' = chiralAxialDensity ψ := by
  intro ψ'
  have hInner : inner ℂ ψ'.1 ψ'.2 = inner ℂ ψ.1 ψ.2 := by
    dsimp [ψ', diagonalVectorAction]
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

/-- The coordinate map from real 8-spinors to the two Weyl sheets is injective.
The sum and difference of the two readouts recover the upper and lower Dirac
components, and `phiToPsi` is a coordinate permutation with signs. -/
theorem phiToPsi_injective : Function.Injective phiToPsi := by
  intro Φ Ψ h
  funext i
  fin_cases i
  · have h0 := congrArg Complex.re (congrFun h 0)
    simpa [phiToPsi] using h0
  · have h1 := congrArg Complex.im (congrFun h 1)
    have h1' : -Φ 1 = -Ψ 1 := by simpa [phiToPsi] using h1
    exact neg_injective h1'
  · have h2 := congrArg Complex.re (congrFun h 1)
    have h2' : -Φ 2 = -Ψ 2 := by simpa [phiToPsi] using h2
    exact neg_injective h2'
  · have h3 := congrArg Complex.im (congrFun h 0)
    simpa [phiToPsi] using h3
  · have h4 := congrArg Complex.im (congrFun h 2)
    simpa [phiToPsi] using h4
  · have h5 := congrArg Complex.re (congrFun h 3)
    simpa [phiToPsi] using h5
  · have h6 := congrArg Complex.im (congrFun h 3)
    simpa [phiToPsi] using h6
  · have h7 := congrArg Complex.re (congrFun h 2)
    simpa [phiToPsi] using h7

/-- Injectivity of the real-spinor embedding into the doubled complex Weyl carrier.
This proves a representation map is faithful on vectors; it does not identify
the acting Clifford algebra with the full endomorphism algebra. -/
theorem vec8ToChiralDiracSpinor_injective :
    Function.Injective vec8ToChiralDiracSpinor := by
  intro Φ Ψ h
  have hXi : weylXi Φ = weylXi Ψ := by
    apply funext
    intro k
    have hfirst := congrArg Prod.fst h
    have hfirst' := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x.ofLp) hfirst
    exact congrFun hfirst' k
  have hEta : weylEta Φ = weylEta Ψ := by
    apply funext
    intro k
    have hsecond := congrArg Prod.snd h
    have hsecond' := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x.ofLp) hsecond
    exact congrFun hsecond' k
  have hscale : ((1 / Real.sqrt 2 : ℝ) : ℂ) * 2 ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (one_div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))))
    · norm_num
  have hTop : ∀ k : Fin 2,
      phiToPsi Φ ⟨k.val, by omega⟩ = phiToPsi Ψ ⟨k.val, by omega⟩ := by
    intro k
    have hs :
        ((1 / Real.sqrt 2 : ℝ) : ℂ) * 2 * phiToPsi Φ ⟨k.val, by omega⟩ =
          ((1 / Real.sqrt 2 : ℝ) : ℂ) * 2 * phiToPsi Ψ ⟨k.val, by omega⟩ := by
      calc
        _ = weylXi Φ k + weylEta Φ k := by simp [weylXi, weylEta]; ring
        _ = weylXi Ψ k + weylEta Ψ k := by rw [hXi, hEta]
        _ = _ := by simp [weylXi, weylEta]; ring
    exact mul_left_cancel₀ hscale hs
  have hBottom : ∀ k : Fin 2,
      phiToPsi Φ ⟨k.val + 2, by omega⟩ = phiToPsi Ψ ⟨k.val + 2, by omega⟩ := by
    intro k
    have hs :
        ((1 / Real.sqrt 2 : ℝ) : ℂ) * 2 * phiToPsi Φ ⟨k.val + 2, by omega⟩ =
          ((1 / Real.sqrt 2 : ℝ) : ℂ) * 2 * phiToPsi Ψ ⟨k.val + 2, by omega⟩ := by
      calc
        _ = weylXi Φ k - weylEta Φ k := by simp [weylXi, weylEta]; ring
        _ = weylXi Ψ k - weylEta Ψ k := by rw [hXi, hEta]
        _ = _ := by simp [weylXi, weylEta]; ring
    exact mul_left_cancel₀ hscale hs
  apply phiToPsi_injective
  funext i
  fin_cases i
  · exact hTop 0
  · exact hTop 1
  · exact hBottom 0
  · exact hBottom 1

/-- Recover the real Dirac coordinates from the four complex coordinates in
`phiToPsi`. This is a coordinate inverse, not an intertwiner for Clifford actions. -/
def psiToPhi (z : Fin 4 → ℂ) : Vec8R := fun i =>
  match i.val with
  | 0 => (z 0).re
  | 1 => -(z 1).im
  | 2 => -(z 1).re
  | 3 => (z 0).im
  | 4 => (z 2).im
  | 5 => (z 3).re
  | 6 => (z 3).im
  | 7 => (z 2).re
  | _ => 0

theorem phiToPsi_psiToPhi (z : Fin 4 → ℂ) : phiToPsi (psiToPhi z) = z := by
  funext i
  fin_cases i <;> simp [phiToPsi, psiToPhi]

/-- Weyl-coordinate reconstruction. The sum and difference use the same
normalization as `weylXi` and `weylEta`. -/
def chiralToDiracCoords (ψ : ChiralDiracSpinor) : Fin 4 → ℂ
  | ⟨0, _⟩ => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (ψ.1.ofLp 0 + ψ.2.ofLp 0)
  | ⟨1, _⟩ => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (ψ.1.ofLp 1 + ψ.2.ofLp 1)
  | ⟨2, _⟩ => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (ψ.1.ofLp 0 - ψ.2.ofLp 0)
  | ⟨3, _⟩ => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (ψ.1.ofLp 1 - ψ.2.ofLp 1)

/-- Explicit reconstruction from a pair of complex Weyl coordinates. -/
def chiralToVec8 (ψ : ChiralDiracSpinor) : Vec8R :=
  psiToPhi (chiralToDiracCoords ψ)

private lemma invSqrtTwoComplex_sq :
    ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (1 / 2 : ℂ) := by
  have hReal : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [pow_two]
    exact inv_sqrt2_sq
  calc
    ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2 =
        (((1 / Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) := by
          simp [pow_two]
    _ = ((1 / 2 : ℝ) : ℂ) := by rw [hReal]
    _ = (1 / 2 : ℂ) := by norm_num

private lemma invSqrtTwo_sum (x y : ℂ) :
    ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (((1 / Real.sqrt 2 : ℝ) : ℂ) * (x + y) +
        ((1 / Real.sqrt 2 : ℝ) : ℂ) * (x - y)) = x := by
  calc
    _ = ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2 * ((x + y) + (x - y)) := by ring
    _ = x := by rw [invSqrtTwoComplex_sq]; ring

private lemma invSqrtTwo_sub (x y : ℂ) :
    ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (((1 / Real.sqrt 2 : ℝ) : ℂ) * (x + y) -
        ((1 / Real.sqrt 2 : ℝ) : ℂ) * (x - y)) = y := by
  calc
    _ = ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2 * ((x + y) - (x - y)) := by ring
    _ = y := by rw [invSqrtTwoComplex_sq]; ring

/-- The explicit reconstruction is a right inverse to the real-to-Weyl readout. -/
theorem vec8ToChiralDiracSpinor_right_inv (ψ : ChiralDiracSpinor) :
    vec8ToChiralDiracSpinor (chiralToVec8 ψ) = ψ := by
  apply Prod.ext
  · apply (WithLp.ext_iff 2).2
    funext k
    change ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (phiToPsi (psiToPhi (chiralToDiracCoords ψ)) ⟨k.val, by omega⟩ +
        phiToPsi (psiToPhi (chiralToDiracCoords ψ)) ⟨k.val + 2, by omega⟩) = _
    rw [phiToPsi_psiToPhi]
    fin_cases k
    · simpa [chiralToDiracCoords] using invSqrtTwo_sum (ψ.1.ofLp 0) (ψ.2.ofLp 0)
    · simpa [chiralToDiracCoords] using invSqrtTwo_sum (ψ.1.ofLp 1) (ψ.2.ofLp 1)
  · apply (WithLp.ext_iff 2).2
    funext k
    change ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (phiToPsi (psiToPhi (chiralToDiracCoords ψ)) ⟨k.val, by omega⟩ -
        phiToPsi (psiToPhi (chiralToDiracCoords ψ)) ⟨k.val + 2, by omega⟩) = _
    rw [phiToPsi_psiToPhi]
    fin_cases k
    · simpa [chiralToDiracCoords] using invSqrtTwo_sub (ψ.1.ofLp 0) (ψ.2.ofLp 0)
    · simpa [chiralToDiracCoords] using invSqrtTwo_sub (ψ.1.ofLp 1) (ψ.2.ofLp 1)

/-- Every doubled complex Weyl pair is obtained from a real eight-coordinate
spinor. -/
theorem vec8ToChiralDiracSpinor_surjective :
    Function.Surjective vec8ToChiralDiracSpinor := by
  intro ψ
  exact ⟨chiralToVec8 ψ, vec8ToChiralDiracSpinor_right_inv ψ⟩

/-- The explicit reconstruction is also a left inverse, by injectivity of the
real-to-Weyl map. -/
theorem chiralToVec8_left_inv (Φ : Vec8R) :
    chiralToVec8 (vec8ToChiralDiracSpinor Φ) = Φ := by
  apply vec8ToChiralDiracSpinor_injective
  exact vec8ToChiralDiracSpinor_right_inv (vec8ToChiralDiracSpinor Φ)

/-- The real `M₈(ℝ)` coordinates and doubled complex Weyl carrier are in
bijective correspondence as carriers, via the explicit readout above. -/
theorem vec8ToChiralDiracSpinor_bijective :
    Function.Bijective vec8ToChiralDiracSpinor :=
  ⟨vec8ToChiralDiracSpinor_injective, vec8ToChiralDiracSpinor_surjective⟩

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

/-! ### Part 4: the `Cl(2,2)` tower acts faithfully on the chiral carrier -/

/-- Reindex the two Weyl components as one complex four-vector. This is a coordinate
equivalence; it does not identify the Clifford algebra with the full real endomorphism algebra. -/
private def chiralFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4 := @finSumFinEquiv 2 2

def chiralCoordinateEquiv : ChiralDiracSpinor ≃ (Fin 4 → ℂ) where
  toFun ψ i :=
    Sum.elim ψ.1.ofLp ψ.2.ofLp (chiralFinEquiv.symm i)
  invFun z :=
    (WithLp.toLp 2 (fun i => z (chiralFinEquiv (Sum.inl i))),
      WithLp.toLp 2 (fun i => z (chiralFinEquiv (Sum.inr i))))
  left_inv ψ := by
    apply Prod.ext
    · apply (WithLp.ext_iff 2).2
      funext i
      change Sum.elim ψ.1.ofLp ψ.2.ofLp
        (chiralFinEquiv.symm (chiralFinEquiv (Sum.inl i))) = ψ.1.ofLp i
      simp [chiralFinEquiv]
    · apply (WithLp.ext_iff 2).2
      funext i
      change Sum.elim ψ.1.ofLp ψ.2.ofLp
        (chiralFinEquiv.symm (chiralFinEquiv (Sum.inr i))) = ψ.2.ofLp i
      simp [chiralFinEquiv]
  right_inv z := by
    funext i
    change Sum.elim
      (fun j => z (chiralFinEquiv (Sum.inl j)))
      (fun j => z (chiralFinEquiv (Sum.inr j)))
      (chiralFinEquiv.symm i) = z i
    rw [← chiralFinEquiv.apply_symm_apply i]
    cases chiralFinEquiv.symm i <;> simp

/-- Complexify the real `M₄(ℝ)` action of `SplitClPower 2` and transport it to the two-Weyl
carrier. The target is a faithful real action on `ℂ⁴`, not all of `End_ℝ(ℂ⁴)`. -/
def splitClPowerTwoChiralAction (a : SplitClPower 2) (ψ : ChiralDiracSpinor) :
    ChiralDiracSpinor :=
  chiralCoordinateEquiv.symm
    (((splitClPowerEquivMat 2 a).map Complex.ofRealHom) *ᵥ chiralCoordinateEquiv ψ)

theorem splitClPowerTwoChiralAction_one (ψ : ChiralDiracSpinor) :
    splitClPowerTwoChiralAction (1 : SplitClPower 2) ψ = ψ := by
  apply chiralCoordinateEquiv.injective
  simp [splitClPowerTwoChiralAction]

theorem splitClPowerTwoChiralAction_mul (a b : SplitClPower 2) (ψ : ChiralDiracSpinor) :
    splitClPowerTwoChiralAction (a * b) ψ =
      splitClPowerTwoChiralAction a (splitClPowerTwoChiralAction b ψ) := by
  apply chiralCoordinateEquiv.injective
  simp [splitClPowerTwoChiralAction, Matrix.map_mul, Matrix.mulVec_mulVec]

/-- If this represented element annihilates every chiral state, it is zero. -/
theorem splitClPowerTwoChiralAction_faithful (a : SplitClPower 2)
    (ha : ∀ ψ : ChiralDiracSpinor, splitClPowerTwoChiralAction a ψ = 0) : a = 0 := by
  apply (splitClPowerEquivMat 2).injective
  apply Matrix.map_injective Complex.ofReal_injective
  ext i j
  let e : Fin 4 → ℂ := Pi.single j 1
  have hzero :
      ((splitClPowerEquivMat 2 a).map Complex.ofRealHom) *ᵥ e = 0 := by
    have h := congrArg chiralCoordinateEquiv (ha (chiralCoordinateEquiv.symm e))
    have hmapzero : chiralCoordinateEquiv (0 : ChiralDiracSpinor) = 0 := by
      funext i
      simp [chiralCoordinateEquiv]
    change chiralCoordinateEquiv (chiralCoordinateEquiv.symm
      (((splitClPowerEquivMat 2 a).map Complex.ofRealHom) *ᵥ
        chiralCoordinateEquiv (chiralCoordinateEquiv.symm e))) =
      chiralCoordinateEquiv 0 at h
    rw [Equiv.apply_symm_apply] at h
    rw [hmapzero] at h
    exact h
  have hentry := congrFun hzero i
  simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply] using hentry

end InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge
