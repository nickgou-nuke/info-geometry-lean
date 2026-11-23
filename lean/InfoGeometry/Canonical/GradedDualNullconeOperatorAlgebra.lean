/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.SplitCl11GradedTensorTower
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.NonAssocDerivation

/-!
# Graded differential operators over dual isotropic nullcones

This file formalizes the irreducible algebraic core `(V = N₊ ⊕ N₋, Γ, J, D)` and
its five foundational axioms:
1. Dual Isotropic Nullcones: `N₊` and `N₋` are individually null under `η`, while metric pairing
   lives strictly in cross-pairing `⟨N₊, N₋⟩`.
2. Cut vs. Mirror Non-Equality (`Γ ≠ J`): Perspectival cut `Γ` and CPT/KMS mirror `J` are distinct
   involutions; inserting `Γ` into `η` collapses to zero (`η(u, Γ u) = 0`), while inserting `J`
   yields a positive-definite Hilbert metric.
3. Peirce–Zorn 2×2 Operator Matrix: Off-diagonal nilpotent bridges `X, Y` satisfy `{X, Y} = F²`
   (mass and Socratic defect), `[Y, X] = Γ F²` (Berry curvature), and unilateral limit `F² = 0`.
4. Leibniz Derivation `D` & Logarithmic Soldering `θ_L(g) = g⁻¹ D g`: Cartan torsion-curvature
   splitting, Maurer–Cartan cocycle, and topological curvature identities.
5. Finite `Cl(1,1)` Atom & Parity-Soldered Tower: the actual tower and its matrix equivalence are
   reused from `InfoGeometry.Clifford.SplitCl11GradedTensorTower`.
-/

set_option linter.unusedSimpArgs false

noncomputable section

open scoped BigOperators
open Matrix
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Krein

namespace InfoGeometry.Canonical.GradedDualNullconeOperatorAlgebra

/-! ### Axiom 1 & 2: Dual Isotropic Nullcones (N₊ ⊕ N₋) and Non-Equal Involutions (Γ ≠ J) -/

/-- The doubled nullcone substrate `V_n = N₊ ⊕ N₋`. -/
abbrev NullconeBase (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev NullconeCarrier (n : ℕ) := DoubledSpace (NullconeBase n)

def nullPlus {n : ℕ} (u : NullconeBase n) : NullconeCarrier n := to_doubled u 0
def nullMinus {n : ℕ} (v : NullconeBase n) : NullconeCarrier n := to_doubled 0 v

/-- Indefinite cross-pairing on `N₊ ⊕ N₋`: `η(u, v) = ⟨u₊, v₋⟩ + ⟨u₋, v₊⟩`. -/
def nullKreinPairing {n : ℕ} (u v : NullconeCarrier n) : ℝ :=
  InfoGeometry.Krein.nullPairing u v

/-- **The Cut / Grading** `Γ(u₊, u₋) = (u₊, -u₋)`. -/
def cutOp {n : ℕ} (u : NullconeCarrier n) : NullconeCarrier n :=
  InfoGeometry.Krein.spectral_epsilon u

/-- **The Mirror / Reciprocity** `J(u₊, u₋) = (u₋, u₊)`. -/
def mirrorOp {n : ℕ} (u : NullconeCarrier n) : NullconeCarrier n :=
  InfoGeometry.Krein.modular_j u

/-- **Axiom 1 (Dual Isotropic Nullcones)**:
Self-pairings on `N₊` and `N₋` vanish identically; all metric pairing resides in `⟨N₊, N₋⟩`. -/
theorem axiom1_dual_isotropic_nullcones {n : ℕ}
    (u₁ u₂ v₁ v₂ : NullconeBase n) :
    nullKreinPairing (nullPlus u₁) (nullPlus u₂) = 0 ∧
    nullKreinPairing (nullMinus v₁) (nullMinus v₂) = 0 ∧
    nullKreinPairing (nullPlus u₁) (nullMinus v₁) = inner ℝ u₁ v₁ := by
  refine ⟨?_, ?_, ?_⟩
  · exact InfoGeometry.Krein.nullPairing_plus_self_isotropic u₁ u₂
  · exact InfoGeometry.Krein.nullPairing_minus_self_isotropic v₁ v₂
  · change InfoGeometry.Krein.nullPairing (to_doubled u₁ 0)
      (to_doubled 0 v₁) = inner ℝ u₁ v₁
    exact InfoGeometry.Krein.nullPairing_cross_sheet u₁ v₁

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
    nullKreinPairing u (mirrorOp v) = inner ℝ u v ∧
    0 ≤ nullKreinPairing u (mirrorOp u) ∧
    (nullKreinPairing u (mirrorOp u) = 0 ↔ u = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun T : _ →L[ℝ] _ => T u)
      (InfoGeometry.Krein.spectral_epsilon_involution
        (NullconeBase n))
    simpa [cutOp] using h
  · have h := congrArg (fun T : _ →L[ℝ] _ => T u)
      (InfoGeometry.Krein.modular_j_involution
        (NullconeBase n))
    simpa [mirrorOp] using h
  · have h := congrArg (fun T : _ →L[ℝ] _ => T u)
      (InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute
        (NullconeBase n))
    simpa [cutOp, mirrorOp, Function.comp_apply] using
      (congrArg Neg.neg h).symm
  · intro hn hEq
    let e : NullconeBase n :=
      WithLp.toLp 2 fun i => if i = ⟨0, hn⟩ then 1 else 0
    have hstate := congrFun hEq (nullPlus e)
    have hfirst := congrArg WithLp.fst hstate
    simp [cutOp, mirrorOp, nullPlus,
      InfoGeometry.Krein.spectral_epsilon_to_doubled,
      InfoGeometry.Krein.modular_j_to_doubled,
      InfoGeometry.Krein.fst_to_doubled] at hfirst
    have hcoord := congrFun (congrArg WithLp.ofLp hfirst) ⟨0, hn⟩
    simp [e] at hcoord
  · exact InfoGeometry.Krein.nullPairing_cut_self_eq_zero u
  · exact InfoGeometry.Krein.nullPairing_mirror_eq_hilbert u v
  · change 0 ≤ InfoGeometry.Krein.nullPairing u
      (InfoGeometry.Krein.modular_j u)
    rw [InfoGeometry.Krein.nullPairing_mirror_eq_hilbert]
    exact real_inner_self_nonneg (x := u)
  · change InfoGeometry.Krein.nullPairing u
      (InfoGeometry.Krein.modular_j u) = 0 ↔ u = 0
    rw [InfoGeometry.Krein.nullPairing_mirror_eq_hilbert]
    constructor
    · intro h
      by_contra hu
      have hp := real_inner_self_pos.mpr hu
      linarith
    · rintro rfl
      simp

/-! ### Axiom 3: 2×2 Peirce–Zorn Operator Matrix, Socratic Defect, & Unilateral Limit -/

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
      _ = 0 + (X * Y + Y * X) + 0 := by rw [hX2, hY2]
      _ = X * Y + Y * X := by abel
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
    have hPΩP : P * (Ω * Ω) * P = T * T + Y * X := by
      calc P * (Ω * Ω) * P = P * Ω * 1 * Ω * P := by noncomm_ring
        _ = P * Ω * (P + Q) * Ω * P := by rw [← hRes]
        _ = P * Ω * (P * P + Q * Q) * Ω * P := by rw [hP, hQ2]
        _ = T * T + Y * X := by dsimp [T, Y, X]; noncomm_ring
    have hQΩQ : Q * (Ω * Ω) * Q = G * G + X * Y := by
      calc Q * (Ω * Ω) * Q = Q * Ω * 1 * Ω * Q := by noncomm_ring
        _ = Q * Ω * (P + Q) * Ω * Q := by rw [← hRes]
        _ = Q * Ω * (P * P + Q * Q) * Ω * Q := by rw [hP, hQ2]
        _ = G * G + X * Y := by dsimp [G, X, Y]; noncomm_ring
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
    rw [hT, hG]
    abel
  · intro hX0
    refine ⟨by rw [hX0, zero_add], by rw [hX0, zero_add, hY2], ?_, ?_⟩
    · calc (P + Y) * (P + Y) = P * P + P * Y + Y * P + Y * Y := by noncomm_ring
        _ = P + Y + 0 + 0 := by rw [hP, hPY, hYP, hY2]
        _ = P + Y := by abel
    · calc (P + Y) * P - P * (P + Y) = Y * P - P * Y := by noncomm_ring
        _ = -Y := by rw [hYP, hPY]; noncomm_ring

/-! ### Axiom 4: Leibniz Derivation (D), Cartan Split, & Log Soldering θ_L(g) = g⁻¹ D g -/

/-- A ring derivation `D : B → B` satisfying additivity and the Leibniz product rule. -/
structure RingDeriv (B : Type*) [Ring B] where
  toFun : B → B
  map_add' : ∀ a b : B, toFun (a + b) = toFun a + toFun b
  map_mul' : ∀ a b : B, toFun (a * b) = toFun a * b + a * toFun b

instance {B : Type*} [Ring B] : CoeFun (RingDeriv B) (fun _ => B → B) :=
  ⟨RingDeriv.toFun⟩

private def ringDerivIntLinearEnd {B : Type*} [Ring B] (D : RingDeriv B) :
    Module.End ℤ B where
  toFun := D
  map_add' := D.map_add'
  map_smul' := fun n x => by
    change D (n • x) = n • D x
    exact (AddMonoidHom.mk' D D.map_add').map_zsmul n x

/-- View the additive Leibniz map as an element of the repository's canonical derivation
Lie subalgebra. Integer-linearity follows from additivity; the Leibniz field is unchanged. -/
def RingDeriv.toCanonicalDerivation {B : Type*} [Ring B] (D : RingDeriv B) :
    InfoGeometry.Algebra.NonAssocDerivation.derivations ℤ B :=
  ⟨ringDerivIntLinearEnd D, D.map_mul'⟩

/-- Recover the function-based interface from a canonical integer-linear derivation. -/
def RingDeriv.ofCanonicalDerivation {B : Type*} [Ring B]
    (D : InfoGeometry.Algebra.NonAssocDerivation.derivations ℤ B) : RingDeriv B where
  toFun := D
  map_add' := (D : Module.End ℤ B).map_add
  map_mul' := D.property

/-- The project-specific `RingDeriv` interface is equivalent to the existing canonical
integer-linear Leibniz subalgebra on the same ring. -/
def RingDeriv.equivCanonicalDerivation {B : Type*} [Ring B] :
    RingDeriv B ≃ InfoGeometry.Algebra.NonAssocDerivation.derivations ℤ B where
  toFun := RingDeriv.toCanonicalDerivation
  invFun := RingDeriv.ofCanonicalDerivation
  left_inv D := by
    cases D
    rfl
  right_inv D := by
    apply Subtype.ext
    ext x
    rfl

@[simp] theorem RingDeriv.toCanonicalDerivation_apply {B : Type*} [Ring B]
    (D : RingDeriv B) (x : B) :
    (D.toCanonicalDerivation : Module.End ℤ B) x = D x := rfl

/-- Constructive trivial zero derivation witnessing model non-degeneracy. -/
def zeroRingDeriv (B : Type*) [Ring B] : RingDeriv B where
  toFun _ := 0
  map_add' _ _ := by simp
  map_mul' _ _ := by simp

instance (B : Type*) [Ring B] : Inhabited (RingDeriv B) :=
  ⟨zeroRingDeriv B⟩

namespace RingDeriv

variable {B : Type*} [Ring B]

theorem map_one (D : RingDeriv B) : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by
    calc D 1 = D (1 * 1) := by rw [mul_one]
      _ = D 1 * 1 + 1 * D 1 := D.map_mul' 1 1
      _ = D 1 + D 1 := by rw [mul_one, one_mul]
  have h0 : (0 : B) = D 1 := by
    calc (0 : B) = D 1 - D 1 := (sub_self (D 1)).symm
      _ = (D 1 + D 1) - D 1 := by rw [← h]
      _ = D 1 := by rw [add_sub_cancel_right]
  exact h0.symm

theorem map_inv (D : RingDeriv B) (g : Bˣ) :
    D ((g⁻¹ : Bˣ) : B) = -((g⁻¹ : Bˣ) : B) * D g * (g⁻¹ : Bˣ) := by
  have h : (0 : B) = D ((g⁻¹ : Bˣ) : B) * g + (g⁻¹ : Bˣ) * D g := by
    calc (0 : B) = D 1 := D.map_one.symm
      _ = D (((g⁻¹ : Bˣ) : B) * g) := by simp
      _ = D ((g⁻¹ : Bˣ) : B) * g + (g⁻¹ : Bˣ) * D g := D.map_mul' _ _
  have h1 : D ((g⁻¹ : Bˣ) : B) * g = -(((g⁻¹ : Bˣ) : B) * D g) :=
    eq_neg_of_add_eq_zero_left h.symm
  calc D ((g⁻¹ : Bˣ) : B) = (D ((g⁻¹ : Bˣ) : B) * (g : B)) * ((g⁻¹ : Bˣ) : B) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = -(((g⁻¹ : Bˣ) : B) * D g) * (g⁻¹ : Bˣ) := by rw [h1]
    _ = -((g⁻¹ : Bˣ) : B) * D g * (g⁻¹ : Bˣ) := by rw [← neg_mul]

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

/-! ### Axiom 5: Reuse the actual parity-soldered Clifford tower -/

/-- The fundamental 2×2 split matrix algebra atom `Cl(1,1) ≅ M₂(ℝ)`. -/
def cl11_atom_matrix_equiv : CliffordAlgebra q11 ≃ₐ[ℝ] Mat2 := cl11EquivMat

theorem cl11_atom_generator_laws :
    (Eplus * Eplus = 1) ∧
    (Eminus * Eminus = -1 • (1 : Mat2)) ∧
    (Eplus * Eminus + Eminus * Eplus = 0) := by
  refine ⟨Eplus_sq, Eminus_sq, ?_⟩
  simpa only [cl11ToMat_iota_pos, cl11ToMat_iota_neg] using
    cl11ToMat_iota_pos_neg_anticomm

/- The all-level construction is owned by `SplitCl11GradedTensorTower`. Its
   `SplitClPower n` is the Clifford algebra of the actual `n`-fold split form,
   and `splitClPowerEquivMat n` identifies it with the real matrix algebra of
   dimension `2^n × 2^n`. Re-export those declarations instead of introducing
   an arbitrary stage structure that could be inhabited by `Unit`. -/
export InfoGeometry.Clifford.SplitCl11GradedTensorTower
  (SplitClPower splitClPowerEquivMat splitClPowerEquivWordMat)

end InfoGeometry.Canonical.GradedDualNullconeOperatorAlgebra
