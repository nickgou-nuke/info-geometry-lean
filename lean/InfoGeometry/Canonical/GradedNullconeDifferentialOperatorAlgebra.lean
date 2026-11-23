/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open scoped Kronecker
open Matrix

namespace GradedNullconeAlgebra

/-! ### Axiom 1 & 2: Dual Isotropic Nullcones (N₊ ⊕ N₋) and Non-Equal Involutions (Γ ≠ J) -/

/-- The doubled nullcone substrate `V_n = N₊ ⊕ N₋`. -/
abbrev NullconeCarrier (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def nullPlus {n : ℕ} (u : Fin n → ℝ) : NullconeCarrier n := (u, 0)
def nullMinus {n : ℕ} (v : Fin n → ℝ) : NullconeCarrier n := (0, v)

/-- Indefinite cross-pairing on `N₊ ⊕ N₋`: `η(u, v) = ⟨u₊, v₋⟩ + ⟨u₋, v₊⟩`. -/
def nullKreinPairing {n : ℕ} (u v : NullconeCarrier n) : ℝ :=
  (∑ i : Fin n, u.1 i * v.2 i) + (∑ i : Fin n, u.2 i * v.1 i)

/-- **The Cut / Grading** `Γ(u₊, u₋) = (u₊, -u₋)`. -/
def cutOp {n : ℕ} (u : NullconeCarrier n) : NullconeCarrier n :=
  (u.1, -u.2)

/-- **The Mirror / Reciprocity** `J(u₊, u₋) = (u₋, u₊)`. -/
def mirrorOp {n : ℕ} (u : NullconeCarrier n) : NullconeCarrier n :=
  (u.2, u.1)

/-- **Axiom 1 (Dual Isotropic Nullcones)**:
Self-pairings on `N₊` and `N₋` vanish identically; all metric pairing resides in `⟨N₊, N₋⟩`. -/
theorem axiom1_dual_isotropic_nullcones {n : ℕ} (u₁ u₂ v₁ v₂ : Fin n → ℝ) :
    nullKreinPairing (nullPlus u₁) (nullPlus u₂) = 0 ∧
    nullKreinPairing (nullMinus v₁) (nullMinus v₂) = 0 ∧
    nullKreinPairing (nullPlus u₁) (nullMinus v₁) = ∑ i : Fin n, u₁ i * v₁ i := by
  simp [nullKreinPairing, nullPlus, nullMinus]

/-- **Axiom 2 (Cut vs. Mirror Non-Equality, Ghost Collapse, & Positive Hilbert Metric)**:
1. `Γ² = id`, `J² = id`, and `Γ ∘ J = -(J ∘ Γ)`.
2. For `n > 0`, `Γ ≠ J`.
3. **Ghost Collapse (`J_fake = Γ`)**: inserting `Γ` into `η` vanishes identically (`η(u, Γ u) = 0`).
4. **Positive Mirror Norm (`η(u, J v)`)**: inserting `J` yields `∑ (u₊² + u₋²) ≥ 0`,
   vanishing iff `u = 0`. -/
theorem axiom2_cut_vs_mirror_law {n : ℕ} (u v : NullconeCarrier n) :
    cutOp (cutOp u) = u ∧
    mirrorOp (mirrorOp u) = u ∧
    cutOp (mirrorOp u) = -mirrorOp (cutOp u) ∧
    (0 < n → (cutOp : NullconeCarrier n → NullconeCarrier n) ≠ mirrorOp) ∧
    nullKreinPairing u (cutOp u) = 0 ∧
    nullKreinPairing u (mirrorOp v) =
      (∑ i : Fin n, u.1 i * v.1 i) + (∑ i : Fin n, u.2 i * v.2 i) ∧
    0 ≤ nullKreinPairing u (mirrorOp u) ∧
    (nullKreinPairing u (mirrorOp u) = 0 ↔ u = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i <;> simp [cutOp]
  · ext i <;> simp [mirrorOp]
  · ext i <;> simp [cutOp, mirrorOp]
  · intro hn hEq
    let e : NullconeCarrier n := (fun _ => 1, 0)
    have h := congrFun hEq e
    have h1 := congrFun (congrArg Prod.fst h) ⟨0, hn⟩
    simp [cutOp, mirrorOp, e] at h1
  · simp [nullKreinPairing, cutOp]
    rw [show (∑ i : Fin n, u.2 i * u.1 i) = ∑ i : Fin n, u.1 i * u.2 i by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _]
    ring
  · simp [nullKreinPairing, mirrorOp]
  · simp only [nullKreinPairing, mirrorOp]
    exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (u.1 i))
      (Finset.sum_nonneg fun i _ => mul_self_nonneg (u.2 i))
  · simp only [nullKreinPairing, mirrorOp]
    constructor
    · intro hSum
      have hnn1 : 0 ≤ ∑ i : Fin n, u.1 i * u.1 i :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg (u.1 i)
      have hnn2 : 0 ≤ ∑ i : Fin n, u.2 i * u.2 i :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg (u.2 i)
      have h1 : ∑ i : Fin n, u.1 i * u.1 i = 0 := by linarith
      have h2 : ∑ i : Fin n, u.2 i * u.2 i = 0 := by linarith
      ext i
      · exact mul_self_eq_zero.mp
          ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (u.1 j)).mp h1 i
            (Finset.mem_univ i))
      · exact mul_self_eq_zero.mp
          ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (u.2 j)).mp h2 i
            (Finset.mem_univ i))
    · rintro rfl; simp

/-! ### Axiom 3: 2×2 Peirce–Zorn Operator Matrix, Mass/Berry Brackets,
Socratic Defect, and Unilateral Limit -/

/-- **Axiom 3 (Peirce–Zorn Decomposition in Any Associative Ring)**:
Given complementary Peirce idempotents `P² = P`, `Q = 1 - P`, cut `Γ = P - Q`, and any operator `Ω`
split into diagonal states `T = P Ω P`, `G = Q Ω Q` and off-diagonal bridges `X = Q Ω P`,
`Y = P Ω Q` (`F = X + Y`):
1. `X² = 0`, `Y² = 0`, and `{Γ, F} = 0`.
2. **Symmetric Anticommutator (Mass / Grace)**: `{X, Y} = F²`.
3. **Antisymmetric Commutator (Berry Curvature / Frame Dragging)**: `[Y, X] = Γ F²`.
4. **Socratic Defect Law**: if `Ω² = Ω`, then `(T - T²) + (G - G²) = {X, Y} = F²`.
5. **Unilateral Parabolic Limit**: if `X = 0`, then `F = Y`, `F² = 0`, and `(P + Y)² = P + Y`
   with `[P + Y, P] = -Y`. -/
theorem axiom3_peirce_zorn_operator_algebra {B : Type*} [Ring B]
    (P Ω : B) (hP : P * P = P) :
    let Q := 1 - P
    let Γ := P - Q
    let T := P * Ω * P
    let G := Q * Ω * Q
    let X := Q * Ω * P
    let Y := P * Ω * Q
    let F := X + Y
    X * X = 0 ∧
    Y * Y = 0 ∧
    Γ * F + F * Γ = 0 ∧
    X * Y + Y * X = F * F ∧
    Y * X - X * Y = Γ * (F * F) ∧
    (Ω * Ω = Ω → (T - T * T) + (G - G * G) = X * Y + Y * X) ∧
    (X = 0 → F = Y ∧ F * F = 0 ∧
      (P + Y) * (P + Y) = P + Y ∧ (P + Y) * P - P * (P + Y) = -Y) := by
  dsimp
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P) = 1 - 2 * P + P * P := by noncomm_ring
      _ = 1 - 2 * P + P := by rw [hP]
      _ = 1 - P := by noncomm_ring
  set Q := 1 - P
  set T := P * Ω * P
  set G := Q * Ω * Q
  set X := Q * Ω * P
  set Y := P * Ω * Q
  have hX2 : X * X = 0 := by
    calc (Q * Ω * P) * (Q * Ω * P) = Q * Ω * (P * Q) * Ω * P := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hY2 : Y * Y = 0 := by
    calc (P * Ω * Q) * (P * Ω * Q) = P * Ω * (Q * P) * Ω * Q := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hPX : P * X = 0 := by
    calc P * (Q * Ω * P) = (P * Q) * Ω * P := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hXP : X * P = X := by
    calc (Q * Ω * P) * P = Q * Ω * (P * P) := by noncomm_ring
      _ = X := by rw [hP]
  have hQX : Q * X = X := by
    calc Q * (Q * Ω * P) = (Q * Q) * Ω * P := by noncomm_ring
      _ = X := by rw [hQ2]
  have hXQ : X * Q = 0 := by
    calc (Q * Ω * P) * Q = Q * Ω * (P * Q) := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hPY : P * Y = Y := by
    calc P * (P * Ω * Q) = (P * P) * Ω * Q := by noncomm_ring
      _ = Y := by rw [hP]
  have hYP : Y * P = 0 := by
    calc (P * Ω * Q) * P = P * Ω * (Q * P) := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hQY : Q * Y = 0 := by
    calc Q * (P * Ω * Q) = (Q * P) * Ω * Q := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hYQ : Y * Q = Y := by
    calc (P * Ω * Q) * Q = P * Ω * (Q * Q) := by noncomm_ring
      _ = Y := by rw [hQ2]
  have hF2 : (X + Y) * (X + Y) = X * Y + Y * X := by
    calc (X + Y) * (X + Y) = X * X + (X * Y + Y * X) + Y * Y := by noncomm_ring
      _ = X * Y + Y * X := by rw [hX2, hY2]; abel
  refine ⟨hX2, hY2, ?_, hF2.symm, ?_, ?_, ?_⟩
  · calc (P - Q) * (X + Y) + (X + Y) * (P - Q)
        = (P * X - Q * X + P * Y - Q * Y) + (X * P + Y * P - X * Q - Y * Q) := by noncomm_ring
      _ = (0 - X + Y - 0) + (X + 0 - 0 - Y) := by
            rw [hPX, hQX, hPY, hQY, hXP, hYP, hXQ, hYQ]
      _ = 0 := by noncomm_ring
  · rw [hF2]
    calc Y * X - X * Y
        = ((P * Y) * X - (Q * X) * Y) - ((Q * Y) * X - (P * X) * Y) := by
            rw [hPY, hQX, hQY, hPX]; noncomm_ring
      _ = (P - Q) * (X * Y + Y * X) := by noncomm_ring
  · intro hIdem
    have hRes : P + Q = 1 := by dsimp [Q]; noncomm_ring
    have hPΩPP : (P * Ω * P) * (P * Ω * P) = P * Ω * P * Ω * P := by
      calc (P * Ω * P) * (P * Ω * P) = P * Ω * (P * P) * Ω * P := by noncomm_ring
        _ = P * Ω * P * Ω * P := by rw [hP]
    have hPΩQ : (P * Ω * Q) * (Q * Ω * P) = P * Ω * Q * Ω * P := by
      calc (P * Ω * Q) * (Q * Ω * P) = P * Ω * (Q * Q) * Ω * P := by noncomm_ring
        _ = P * Ω * Q * Ω * P := by rw [hQ2]
    have hPΩP : P * (Ω * Ω) * P = T * T + Y * X := by
      calc P * (Ω * Ω) * P = P * Ω * (P + Q) * Ω * P := by rw [hRes]; noncomm_ring
        _ = P * Ω * P * Ω * P + P * Ω * Q * Ω * P := by noncomm_ring
        _ = (P * Ω * P) * (P * Ω * P) + (P * Ω * Q) * (Q * Ω * P) := by rw [← hPΩPP, ← hPΩQ]
        _ = T * T + Y * X := rfl
    have hQΩQQ : (Q * Ω * Q) * (Q * Ω * Q) = Q * Ω * Q * Ω * Q := by
      calc (Q * Ω * Q) * (Q * Ω * Q) = Q * Ω * (Q * Q) * Ω * Q := by noncomm_ring
        _ = Q * Ω * Q * Ω * Q := by rw [hQ2]
    have hQΩP : (Q * Ω * P) * (P * Ω * Q) = Q * Ω * P * Ω * Q := by
      calc (Q * Ω * P) * (P * Ω * Q) = Q * Ω * (P * P) * Ω * Q := by noncomm_ring
        _ = Q * Ω * P * Ω * Q := by rw [hP]
    have hQΩQ : Q * (Ω * Ω) * Q = G * G + X * Y := by
      calc Q * (Ω * Ω) * Q = Q * Ω * (P + Q) * Ω * Q := by rw [hRes]; noncomm_ring
        _ = Q * Ω * Q * Ω * Q + Q * Ω * P * Ω * Q := by noncomm_ring
        _ = (Q * Ω * Q) * (Q * Ω * Q) + (Q * Ω * P) * (P * Ω * Q) := by rw [← hQΩQQ, ← hQΩP]
        _ = G * G + X * Y := rfl
    have hT : T - T * T = Y * X := by
      calc T - T * T = P * Ω * P - T * T := rfl
        _ = P * (Ω * Ω) * P - T * T := by rw [hIdem]
        _ = (T * T + Y * X) - T * T := by rw [hPΩP]
        _ = Y * X := by noncomm_ring
    have hG : G - G * G = X * Y := by
      calc G - G * G = Q * Ω * Q - G * G := rfl
        _ = Q * (Ω * Ω) * Q - G * G := by rw [hIdem]
        _ = (G * G + X * Y) - G * G := by rw [hQΩQ]
        _ = X * Y := by noncomm_ring
    rw [hT, hG]; abel
  · intro hX0
    refine ⟨by rw [hX0, zero_add], by rw [hX0, zero_add, hY2], ?_, ?_⟩
    · calc (P + Y) * (P + Y) = P * P + P * Y + Y * P + Y * Y := by noncomm_ring
        _ = P + Y := by rw [hP, hPY, hYP, hY2]; abel
    · calc (P + Y) * P - P * (P + Y) = Y * P - P * Y := by noncomm_ring
        _ = -Y := by rw [hYP, hPY]; noncomm_ring

/-! ### Axiom 4: Leibniz Derivation (D), Cartan Torsion Split, and
Logarithmic Soldering `θ_L(g) = g⁻¹ D g` -/

/-- A ring derivation `D : B → B` satisfying additivity and the Leibniz product rule. -/
structure RingDeriv (B : Type*) [Ring B] where
  toFun : B → B
  map_add' : ∀ a b : B, toFun (a + b) = toFun a + toFun b
  map_mul' : ∀ a b : B, toFun (a * b) = toFun a * b + a * toFun b

instance {B : Type*} [Ring B] : CoeFun (RingDeriv B) (fun _ => B → B) :=
  ⟨RingDeriv.toFun⟩

instance {B : Type*} [Ring B] : Inhabited (RingDeriv B) where
  default :=
    { toFun := fun _ => 0
      map_add' := by intro a b; simp
      map_mul' := by intro a b; simp }

namespace RingDeriv

variable {B : Type*} [Ring B]

theorem map_one (D : RingDeriv B) : D 1 = 0 := by
  have h := D.map_mul' 1 1
  simp only [one_mul, mul_one] at h
  have h' : D 1 + 0 = D 1 + D 1 := by simpa [add_zero] using h
  exact (add_left_cancel h').symm

theorem map_inv (D : RingDeriv B) (g : Bˣ) :
    D ((g⁻¹ : Bˣ) : B) = -((g⁻¹ : Bˣ) : B) * D g * (g⁻¹ : Bˣ) := by
  have h : (0 : B) = D ((g⁻¹ : Bˣ) : B) * g + (g⁻¹ : Bˣ) * D g := by
    calc (0 : B) = D 1 := D.map_one.symm
      _ = D (((g⁻¹ : Bˣ) : B) * g) := by simp
      _ = D ((g⁻¹ : Bˣ) : B) * g + (g⁻¹ : Bˣ) * D g := D.map_mul' _ _
  have h1 : D ((g⁻¹ : Bˣ) : B) * g = -((g⁻¹ : Bˣ) : B) * D g := by
    simpa [neg_mul] using (eq_neg_of_add_eq_zero_left h.symm)
  calc D ((g⁻¹ : Bˣ) : B) = (D ((g⁻¹ : Bˣ) : B) * (g : B)) * ((g⁻¹ : Bˣ) : B) := by
        rw [mul_assoc]; simp
    _ = (-((g⁻¹ : Bˣ) : B) * D g) * (g⁻¹ : Bˣ) := by rw [h1]

end RingDeriv

/-- Logarithmic Maurer–Cartan / Darboux soldering form `θ_L(g) = g⁻¹ D(g)`. -/
def logSoldering {B : Type*} [Ring B] (D : RingDeriv B) (g : Bˣ) : B :=
  ((g⁻¹ : Bˣ) : B) * D g

/-- **Axiom 4 (Cartan Torsion Split, Maurer–Cartan Cocycle, von Mangoldt Additivity, & Curvature)**:
1. **Cartan–Peirce Connection Split**: decomposing `Ω = ϖ + e` into `Γ`-even gauge `ϖ` and `Γ`-odd
   soldering `e` splits `Ω² = (ϖ² + e²) + (ϖe + eϖ)` into `Γ`-even curvature and `Γ`-odd torsion.
2. **Maurer–Cartan Cocycle**: `θ_L(g h) = h⁻¹ θ_L(g) h + θ_L(h)`.
3. **Von Mangoldt Additivity**: whenever `h` commutes with `θ_L(g)` (in particular in any
   commutative algebra or on commuting diagonal factors), `θ_L(g h) = θ_L(g) + θ_L(h)`.
4. **Curvature / Topological Residue**: `D(θ_L(g)) + θ_L(g)² = g⁻¹ D²(g)`.
5. **Two-Derivation 2-Form Curvature**:
   `(D₁ θ_{L,2}(g) - D₂ θ_{L,1}(g)) + [θ_{L,1}(g), θ_{L,2}(g)] = g⁻¹ [D₁, D₂](g)`. -/
theorem axiom4_derivation_and_soldering_laws {B : Type*} [Ring B]
    (D D₁ D₂ : RingDeriv B) (g h : Bˣ) (Γ ϖ e : B)
    (hΓϖ : Γ * ϖ = ϖ * Γ) (hΓe : Γ * e = -(e * Γ)) :
    (Γ * (ϖ * ϖ + e * e) = (ϖ * ϖ + e * e) * Γ ∧
     Γ * (ϖ * e + e * ϖ) = -((ϖ * e + e * ϖ) * Γ)) ∧
    (logSoldering D (g * h) =
      ((h⁻¹ : Bˣ) : B) * logSoldering D g * h + logSoldering D h) ∧
    ((h : B) * logSoldering D g = logSoldering D g * h →
      logSoldering D (g * h) = logSoldering D g + logSoldering D h) ∧
    (D (logSoldering D g) + logSoldering D g * logSoldering D g =
      ((g⁻¹ : Bˣ) : B) * D (D g)) ∧
    ((D₁ (logSoldering D₂ g) - D₂ (logSoldering D₁ g)) +
      (logSoldering D₁ g * logSoldering D₂ g - logSoldering D₂ g * logSoldering D₁ g) =
      ((g⁻¹ : Bˣ) : B) * (D₁ (D₂ g) - D₂ (D₁ g))) := by
  have hCocycle : logSoldering D (g * h) =
      ((h⁻¹ : Bˣ) : B) * logSoldering D g * h + logSoldering D h := by
    unfold logSoldering
    simp only [Units.val_mul, _root_.mul_inv_rev]
    rw [D.map_mul']
    calc ((h⁻¹ : Bˣ) : B) * ((g⁻¹ : Bˣ) : B) * (D g * h + g * D h)
        = ((h⁻¹ : Bˣ) : B) * (((g⁻¹ : Bˣ) : B) * D g) * h +
            ((h⁻¹ : Bˣ) : B) * (((g⁻¹ : Bˣ) : B) * g) * D h := by noncomm_ring
      _ = ((h⁻¹ : Bˣ) : B) * (((g⁻¹ : Bˣ) : B) * D g) * h + ((h⁻¹ : Bˣ) : B) * D h := by
            simp
  refine ⟨⟨?_, ?_⟩, hCocycle, ?_, ?_, ?_⟩
  · calc Γ * (ϖ * ϖ + e * e)
        = (Γ * ϖ) * ϖ + (Γ * e) * e := by noncomm_ring
      _ = (ϖ * Γ) * ϖ + (-(e * Γ)) * e := by rw [hΓϖ, hΓe]
      _ = ϖ * (Γ * ϖ) - e * (Γ * e) := by noncomm_ring
      _ = ϖ * (ϖ * Γ) - e * (-(e * Γ)) := by rw [hΓϖ, hΓe]
      _ = (ϖ * ϖ + e * e) * Γ := by noncomm_ring
  · calc Γ * (ϖ * e + e * ϖ)
        = (Γ * ϖ) * e + (Γ * e) * ϖ := by noncomm_ring
      _ = (ϖ * Γ) * e + (-(e * Γ)) * ϖ := by rw [hΓϖ, hΓe]
      _ = ϖ * (Γ * e) - e * (Γ * ϖ) := by noncomm_ring
      _ = ϖ * (-(e * Γ)) - e * (ϖ * Γ) := by rw [hΓe, hΓϖ]
      _ = -((ϖ * e + e * ϖ) * Γ) := by noncomm_ring
  · intro hComm
    rw [hCocycle, mul_assoc, ← hComm, ← mul_assoc]
    simp
  · unfold logSoldering
    rw [D.map_mul', D.map_inv g]
    noncomm_ring
  · unfold logSoldering
    rw [D₁.map_mul', D₂.map_mul', D₁.map_inv g, D₂.map_inv g]
    noncomm_ring

/-! ### Axiom 5: The Parity-Soldered Clifford Tower Cl(1,1)^{⊗̂ k} ≅ M_{2^k}(ℝ) -/

/-- Cut, Mirror, and Skew-Chiral generators of the `k = 1` atom `Cl(1,1) ≅ M₂(ℝ)`. -/
def gammaCut2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def gammaMir2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def gammaSkew2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

lemma cl11_atom_laws :
    gammaCut2 * gammaCut2 = 1 ∧
    gammaMir2 * gammaMir2 = 1 ∧
    gammaSkew2 * gammaSkew2 = -1 ∧
    gammaCut2 * gammaMir2 + gammaMir2 * gammaCut2 = 0 ∧
    gammaCut2 * gammaSkew2 + gammaSkew2 * gammaCut2 = 0 ∧
    gammaMir2 * gammaSkew2 + gammaSkew2 * gammaMir2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [gammaCut2, gammaMir2, gammaSkew2, Matrix.mul_apply, Fin.sum_univ_two] }

private lemma kronecker_neg_left {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kronecker, neg_mul]

private lemma kronecker_neg_right {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kronecker, mul_neg]

private lemma kronecker_add_left {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A₁ A₂ : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kronecker, add_mul]

private lemma kronecker_add_right {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B₁ B₂ : Matrix m₂ n₂ R) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kronecker, mul_add]

/-- Recursive index type of cardinality `2^k` for the parity-soldered Clifford tower `Cl(k, k)`. -/
@[reducible] def TowerIdx : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin 2 × TowerIdx k

instance instFintypeTowerIdx : ∀ k : ℕ, Fintype (TowerIdx k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeProd (Fin 2) (TowerIdx k) _ (instFintypeTowerIdx k)

instance instDecidableEqTowerIdx : ∀ k : ℕ, DecidableEq (TowerIdx k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => @instDecidableEqProd (Fin 2) (TowerIdx k) _ (instDecidableEqTowerIdx k)

theorem card_towerIdx (k : ℕ) : Fintype.card (TowerIdx k) = 2 ^ k := by
  induction k with
  | zero => simp [TowerIdx]
  | succ k ih =>
    change Fintype.card (Fin 2 × TowerIdx k) = 2 ^ (k + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ']

/-- Total matrix dimension of `M_{2^k}(ℝ) ≅ Cl(k, k)` equals `4^k`. -/
theorem finrank_clTower (k : ℕ) :
    Module.finrank ℝ (Matrix (TowerIdx k) (TowerIdx k) ℝ) = 4 ^ k := by
  rw [Module.finrank_matrix, card_towerIdx, Module.finrank_self, mul_one]
  calc 2 ^ k * 2 ^ k = (2 * 2) ^ k := (mul_pow 2 2 k).symm
    _ = 4 ^ k := by norm_num

/-- Total chirality grading `Γ^{(k)} = γ_cut^{⊗ k}` on `Cl(k, k)`. -/
def towerGamma : (k : ℕ) → Matrix (TowerIdx k) (TowerIdx k) ℝ
  | 0 => 1
  | k + 1 => gammaCut2 ⊗ₖ towerGamma k

/-- The `k` positive Jordan–Wigner Clifford generators `e_i` (`e_i² = +1`). -/
def jwPos : (k : ℕ) → Fin k → Matrix (TowerIdx k) (TowerIdx k) ℝ
  | 0, i => Fin.elim0 i
  | k + 1, i => Fin.cases (gammaMir2 ⊗ₖ (1 : Matrix (TowerIdx k) (TowerIdx k) ℝ))
      (fun j => gammaCut2 ⊗ₖ jwPos k j) i

/-- The `k` negative Jordan–Wigner Clifford generators `f_i` (`f_i² = -1`). -/
def jwNeg : (k : ℕ) → Fin k → Matrix (TowerIdx k) (TowerIdx k) ℝ
  | 0, i => Fin.elim0 i
  | k + 1, i => Fin.cases (gammaSkew2 ⊗ₖ (1 : Matrix (TowerIdx k) (TowerIdx k) ℝ))
      (fun j => gammaCut2 ⊗ₖ jwNeg k j) i

/-- **Axiom 5 (Inductive Jordan–Wigner / Koszul Parity-Soldered Tower
`Cl(1,1)^{⊗̂ k} ≅ M_{2^k}(ℝ)`)**:
For every tower level `k : ℕ`, the `2k` operators `jwPos k` and `jwNeg k`
together with `towerGamma k` satisfy the exact split-signature Clifford
algebra `Cl(k, k)` :
1. `(Γ^{(k)})² = 1`.
2. `e_i² = +1` and `f_i² = -1` for all `i : Fin k`.
3. `{Γ^{(k)}, e_i} = 0` and `{Γ^{(k)}, f_i} = 0` for all `i : Fin k`.
4. `{e_i, f_l} = 0` for all `i, l : Fin k`.
5. `{e_i, e_l} = 0` and `{f_i, f_l} = 0` for all `i ≠ l`. -/
theorem axiom5_parity_soldered_clifford_tower (k : ℕ) :
    (towerGamma k * towerGamma k = 1) ∧
    (∀ i : Fin k, jwPos k i * jwPos k i = 1) ∧
    (∀ i : Fin k, jwNeg k i * jwNeg k i = -1) ∧
    (∀ i : Fin k, towerGamma k * jwPos k i + jwPos k i * towerGamma k = 0) ∧
    (∀ i : Fin k, towerGamma k * jwNeg k i + jwNeg k i * towerGamma k = 0) ∧
    (∀ i l : Fin k, jwPos k i * jwNeg k l + jwNeg k l * jwPos k i = 0) ∧
    (∀ i l : Fin k, i ≠ l → jwPos k i * jwPos k l + jwPos k l * jwPos k i = 0) ∧
    (∀ i l : Fin k, i ≠ l → jwNeg k i * jwNeg k l + jwNeg k l * jwNeg k i = 0) := by
  obtain ⟨hCC, hMM, hSS, hCM, hCS, hMS⟩ := cl11_atom_laws
  have hMC : gammaMir2 * gammaCut2 + gammaCut2 * gammaMir2 = 0 := by
    rw [add_comm]
    exact hCM
  have hSC : gammaSkew2 * gammaCut2 + gammaCut2 * gammaSkew2 = 0 := by
    rw [add_comm]
    exact hCS
  have hSM : gammaSkew2 * gammaMir2 + gammaMir2 * gammaSkew2 = 0 := by
    rw [add_comm]
    exact hMS
  induction k with
  | zero =>
    refine ⟨?_, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    simp [towerGamma]
  | succ m ih =>
    rcases ih with ⟨ihG, ihP, ihN, ihGP, ihGN, ihPN, ihPP, ihNN⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [towerGamma]
      rw [← Matrix.mul_kronecker_mul, hCC, ihG, Matrix.one_kronecker_one]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [jwPos, Fin.cases_zero]
        rw [← Matrix.mul_kronecker_mul, hMM, Matrix.one_mul, Matrix.one_kronecker_one]
      · intro j
        simp only [jwPos, Fin.cases_succ]
        rw [← Matrix.mul_kronecker_mul, hCC, ihP j, Matrix.one_kronecker_one]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [jwNeg, Fin.cases_zero]
        rw [← Matrix.mul_kronecker_mul, hSS, Matrix.one_mul, kronecker_neg_left,
          Matrix.one_kronecker_one]
      · intro j
        simp only [jwNeg, Fin.cases_succ]
        rw [← Matrix.mul_kronecker_mul, hCC, ihN j, kronecker_neg_right,
          Matrix.one_kronecker_one]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [towerGamma, jwPos, Fin.cases_zero]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          Matrix.mul_one, Matrix.one_mul, ← kronecker_add_left, hCM, Matrix.zero_kronecker]
      · intro j
        simp only [towerGamma, jwPos, Fin.cases_succ]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hCC,
          ← kronecker_add_right, ihGP j, Matrix.kronecker_zero]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [towerGamma, jwNeg, Fin.cases_zero]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          Matrix.mul_one, Matrix.one_mul, ← kronecker_add_left, hCS, Matrix.zero_kronecker]
      · intro j
        simp only [towerGamma, jwNeg, Fin.cases_succ]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hCC,
          ← kronecker_add_right, ihGN j, Matrix.kronecker_zero]
    · intro i l
      refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ l
      · simp only [jwPos, jwNeg, Fin.cases_zero]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          ← kronecker_add_left, hMS, Matrix.zero_kronecker]
      · intro l'
        simp only [jwPos, jwNeg, Fin.cases_zero, Fin.cases_succ]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          Matrix.one_mul, Matrix.mul_one, ← kronecker_add_left, hMC, Matrix.zero_kronecker]
      · intro i'
        simp only [jwPos, jwNeg, Fin.cases_zero, Fin.cases_succ]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          Matrix.mul_one, Matrix.one_mul, ← kronecker_add_left, hCS, Matrix.zero_kronecker]
      · intro l' i'
        simp only [jwPos, jwNeg, Fin.cases_succ]
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hCC,
          ← kronecker_add_right, ihPN i' l', Matrix.kronecker_zero]
    · intro i l hne
      revert l
      refine Fin.cases ?_ ?_ i
      · intro l hne
        revert hne
        refine Fin.cases ?_ ?_ l
        · intro hne
          exact False.elim (hne rfl)
        · intro l' hne
          simp only [jwPos, Fin.cases_zero, Fin.cases_succ]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            Matrix.one_mul, Matrix.mul_one, ← kronecker_add_left, hMC, Matrix.zero_kronecker]
      · intro i' l hne
        revert hne
        refine Fin.cases ?_ ?_ l
        · intro hne
          simp only [jwPos, Fin.cases_zero, Fin.cases_succ]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            Matrix.mul_one, Matrix.one_mul, ← kronecker_add_left]
          rw [hCM, Matrix.zero_kronecker]
        · intro l' hne
          have hne' : i' ≠ l' := fun h => hne (congrArg Fin.succ h)
          simp only [jwPos, Fin.cases_succ]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hCC,
            ← kronecker_add_right, ihPP i' l' hne', Matrix.kronecker_zero]
    · intro i l hne
      revert l
      refine Fin.cases ?_ ?_ i
      · intro l hne
        revert hne
        refine Fin.cases ?_ ?_ l
        · intro hne
          exact False.elim (hne rfl)
        · intro l' hne
          simp only [jwNeg, Fin.cases_zero, Fin.cases_succ]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            Matrix.one_mul, Matrix.mul_one, ← kronecker_add_left, hSC, Matrix.zero_kronecker]
      · intro i' l hne
        revert hne
        refine Fin.cases ?_ ?_ l
        · intro hne
          simp only [jwNeg, Fin.cases_zero, Fin.cases_succ]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
            Matrix.mul_one, Matrix.one_mul, ← kronecker_add_left]
          rw [hCS, Matrix.zero_kronecker]
        · intro l' hne
          have hne' : i' ≠ l' := fun h => hne (congrArg Fin.succ h)
          simp only [jwNeg, Fin.cases_succ]
          rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hCC,
            ← kronecker_add_right, ihNN i' l' hne', Matrix.kronecker_zero]

end GradedNullconeAlgebra
