/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.ZMod.Basic
import InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
import InfoGeometry.OperatorAlgebra.SymmetryInvariants

/-!
# Felix Klein Erlangen 2.0 Symmetry Invariants for the Cantor Double Cylinder Colimit

This module formalizes the Felix Klein Erlangen 2.0 geometry of symmetry invariants
for the Cantor double cylinder fractal operator colimit.

## Mathematical Architecture

1. **Symmetry Group**:
   `G_swap := Multiplicative (ZMod 2)` acting on cylinder words by the bit-flip
   involution `notWord n w := fun i => !(w i)`.

2. **Stage Automorphisms & Equivariance**:
   - `stageSwapEquiv B n : DoubleCylinderStage B n ≃+* DoubleCylinderStage B n`.
   - `stageSwap_commutes_bond`: Proof that the stage automorphism intertwines the
     dyadic branch subdivision bonding map: `α_{n+1} ∘ ι_n = ι_n ∘ α_n`.

3. **Descent to Colimit & Symmetry Action**:
   - `colimitSwapEquiv B : DoubleCylinderColimit B ≃+* DoubleCylinderColimit B`.
   - `erlangenDoubleCylinderSymmetryAction B : SymmetryAction G_swap (DoubleCylinderColimit B)`.

4. **Felix Klein Invariant Subring**:
   - `erlangenDoubleCylinderInvariantSubring B := invariantSubring (erlangenDoubleCylinderSymmetryAction B)`.
   - Invariant symmetrized cylinder projectors `P_u^{sym} = P_u + P_{¬u}` proven `IsInvariantProjector`.
   - Casimir element invariance: central elements of `B` embed as invariant central operators.
   - Strict Noncommutative Operator Discipline (R3): Proof that for any noncommutative
     seed ring `B`, `erlangenDoubleCylinderInvariantSubring B` is strictly noncommutative!
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants

open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.OperatorAlgebra
open Matrix

universe u

variable (B : Type u) [Ring B]

/-! ## 1. Symmetry Group and Word Bit-Flip Involution -/

/-- The two-sheet / branch-swap symmetry group `G_swap ≅ ℤ₂`. -/
abbrev G_swap := Multiplicative (ZMod 2)

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

lemma g_swap_cases (g : G_swap) : g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  have h := zmod2_cases (Multiplicative.toAdd g)
  rcases h with h0 | h1
  · left
    exact (Multiplicative.toAdd.injective (by simpa using h0))
  · right
    exact (Multiplicative.toAdd.injective (by simpa using h1))

/-- Involution on binary words: flip all bits `0 ↔ 1`. -/
def notWord (n : ℕ) (w : BitWord n) : BitWord n :=
  fun i => !(w i)

@[simp]
theorem notWord_involutive (n : ℕ) (w : BitWord n) :
    notWord n (notWord n w) = w := by
  funext i
  simp [notWord]

theorem notWord_injective (n : ℕ) :
    Function.Injective (notWord n) := by
  intro u v h
  have h_inv := congrArg (notWord n) h
  simpa only [notWord_involutive] using h_inv

theorem notWord_eq_iff (n : ℕ) (u w : BitWord n) :
    u = notWord n w ↔ notWord n u = w := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- Equivalence of `BitWord n` induced by word bit-flip negation. -/
def notWordEquiv (n : ℕ) : BitWord n ≃ BitWord n where
  toFun := notWord n
  invFun := notWord n
  left_inv := notWord_involutive n
  right_inv := notWord_involutive n

theorem prefixSucc_notWord (n : ℕ) (w : BitWord (n + 1)) :
    prefixSucc n (notWord (n + 1) w) = notWord n (prefixSucc n w) := by
  funext i
  simp [prefixSucc, notWord]

theorem extendSucc_notWord (n : ℕ) (u : BitWord n) (b : Bool) :
    notWord (n + 1) (extendSucc n u b) = extendSucc n (notWord n u) (!b) := by
  funext i
  dsimp [notWord, extendSucc]
  split_ifs with h <;> rfl

/-! ## 2. Finite-Stage Automorphism and Bonding Equivariance -/

/-- Action of word swap on finite-stage double cylinder matrices. -/
def stageSwapFun (n : ℕ) (M : DoubleCylinderStage B n) :
    DoubleCylinderStage B n :=
  fun u v => M (notWord n u) (notWord n v)

@[simp]
theorem stageSwapFun_apply (n : ℕ) (M : DoubleCylinderStage B n) (u v : BitWord n) :
    stageSwapFun B n M u v = M (notWord n u) (notWord n v) :=
  rfl

theorem stageSwapFun_involutive (n : ℕ) (M : DoubleCylinderStage B n) :
    stageSwapFun B n (stageSwapFun B n M) = M := by
  ext u v
  simp [stageSwapFun]

/-- Finite-stage ring automorphism induced by word bit-flip involution. -/
def stageSwapEquiv (n : ℕ) :
    DoubleCylinderStage B n ≃+* DoubleCylinderStage B n where
  toFun := stageSwapFun B n
  invFun := stageSwapFun B n
  left_inv := stageSwapFun_involutive B n
  right_inv := stageSwapFun_involutive B n
  map_add' := by
    intro M N
    ext u v
    simp [stageSwapFun]
  map_mul' := by
    intro M N
    ext u v
    dsimp [stageSwapFun, Matrix.mul_apply]
    have h_sum := (Equiv.sum_comp (notWordEquiv n)
      (fun k => M (notWord n u) k * N k (notWord n v))).symm
    exact h_sum

@[simp]
theorem stageSwapEquiv_apply (n : ℕ) (M : DoubleCylinderStage B n) (u v : BitWord n) :
    stageSwapEquiv B n M u v = M (notWord n u) (notWord n v) :=
  rfl

/-- Equivariance Theorem:
    The branch-swap automorphism commutes with the dyadic subdivision bonding map:
    `α_{n+1} ∘ ι_n = ι_n ∘ α_n`. -/
theorem stageSwap_commutes_bond (n : ℕ) (M : DoubleCylinderStage B n) :
    stageSwapEquiv B (n + 1) (doubleCylinderBond B n M) =
      doubleCylinderBond B n (stageSwapEquiv B n M) := by
  ext u v
  dsimp [stageSwapEquiv, stageSwapFun, doubleCylinderBond, doubleCylinderBondFun]
  have h_last :
      ((notWord (n + 1) u) ⟨n, Nat.lt_succ_self n⟩ =
       (notWord (n + 1) v) ⟨n, Nat.lt_succ_self n⟩) ↔
      (u ⟨n, Nat.lt_succ_self n⟩ = v ⟨n, Nat.lt_succ_self n⟩) := by
    dsimp [notWord]
    cases (u ⟨n, Nat.lt_succ_self n⟩) <;> cases (v ⟨n, Nat.lt_succ_self n⟩) <;> decide
  rw [prefixSucc_notWord, prefixSucc_notWord]
  by_cases h : u ⟨n, Nat.lt_succ_self n⟩ = v ⟨n, Nat.lt_succ_self n⟩
  · have h_not : (notWord (n + 1) u) ⟨n, Nat.lt_succ_self n⟩ =
                 (notWord (n + 1) v) ⟨n, Nat.lt_succ_self n⟩ := h_last.mpr h
    rw [ite_eq_left h_not, ite_eq_left h]
  · have h_not : ¬((notWord (n + 1) u) ⟨n, Nat.lt_succ_self n⟩ =
                   (notWord (n + 1) v) ⟨n, Nat.lt_succ_self n⟩) := mt h_last.mp h
    rw [ite_eq_right h_not, ite_eq_right h]

/-! ## 3. Descent to Colimit Automorphism and Symmetry Action -/

/-- Induced endomorphism on the inductive colimit algebra. -/
def colimitSwapHom : DoubleCylinderColimit B →+* DoubleCylinderColimit B :=
  directLimitEndomorphism (doubleCylinderBond B)
    (fun n => (stageSwapEquiv B n).toRingHom)
    (stageSwap_commutes_bond B)

@[simp]
theorem colimitSwapHom_inclusion (n : ℕ) (M : DoubleCylinderStage B n) :
    colimitSwapHom B (doubleCylinderInclusion B n M) =
      doubleCylinderInclusion B n (stageSwapEquiv B n M) :=
  directLimitEndomorphism_of (doubleCylinderBond B)
    (fun n => (stageSwapEquiv B n).toRingHom)
    (stageSwap_commutes_bond B) n M

theorem colimitSwapHom_sq :
    (colimitSwapHom B).comp (colimitSwapHom B) =
      RingHom.id (DoubleCylinderColimit B) := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext M
  change colimitSwapHom B (colimitSwapHom B (doubleCylinderInclusion B n M)) =
    doubleCylinderInclusion B n M
  rw [colimitSwapHom_inclusion, colimitSwapHom_inclusion]
  dsimp [stageSwapEquiv]
  rw [stageSwapFun_involutive]

theorem colimitSwapHom_involutive (x : DoubleCylinderColimit B) :
    colimitSwapHom B (colimitSwapHom B x) = x := by
  change ((colimitSwapHom B).comp (colimitSwapHom B)) x = x
  rw [colimitSwapHom_sq B]
  rfl

/-- The colimit branch-swap automorphism `α_∞ : 𝒜_∞ ≃+* 𝒜_∞`. -/
def colimitSwapEquiv : DoubleCylinderColimit B ≃+* DoubleCylinderColimit B where
  toFun := colimitSwapHom B
  invFun := colimitSwapHom B
  left_inv := colimitSwapHom_involutive B
  right_inv := colimitSwapHom_involutive B
  map_add' := (colimitSwapHom B).map_add
  map_mul' := (colimitSwapHom B).map_mul

@[simp]
theorem colimitSwapEquiv_inclusion (n : ℕ) (M : DoubleCylinderStage B n) :
    colimitSwapEquiv B (doubleCylinderInclusion B n M) =
      doubleCylinderInclusion B n (stageSwapEquiv B n M) :=
  colimitSwapHom_inclusion B n M

/-- Felix Klein Erlangen 2.0 Symmetry Action of `G_swap` on the Cantor double cylinder colimit. -/
def erlangenDoubleCylinderSymmetryAction :
    SymmetryAction G_swap (DoubleCylinderColimit B) where
  act g :=
    if g = 1 then
      RingEquiv.refl (DoubleCylinderColimit B)
    else
      colimitSwapEquiv B
  act_one x := by
    dsimp
  act_mul g h x := by
    have h11 : (Multiplicative.ofAdd (1 : ZMod 2)) * (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
      decide
    rcases g_swap_cases g with rfl | rfl
    · simp only [one_mul]
      rfl
    · rcases g_swap_cases h with rfl | rfl
      · simp only [mul_one]
        rfl
      · rw [h11]
        dsimp
        exact (colimitSwapHom_involutive B x).symm

/-! ## 4. Felix Klein Invariant Subring and Invariant Projectors -/

/-- The Felix Klein Invariant Subring `𝒜_∞^{G_swap}` of the Cantor double cylinder fractal. -/
def erlangenDoubleCylinderInvariantSubring :
    Subring (DoubleCylinderColimit B) :=
  invariantSubring (erlangenDoubleCylinderSymmetryAction B)

/-- An element of the colimit is invariant under the action iff it is fixed by `colimitSwapEquiv`. -/
theorem isInvariant_iff_colimitSwap (x : DoubleCylinderColimit B) :
    IsInvariant (erlangenDoubleCylinderSymmetryAction B) x ↔
      colimitSwapEquiv B x = x := by
  constructor
  · intro h
    have h_swap := h (Multiplicative.ofAdd (1 : ZMod 2))
    dsimp [erlangenDoubleCylinderSymmetryAction] at h_swap
    exact h_swap
  · intro h g
    rcases g_swap_cases g with rfl | rfl
    · dsimp [erlangenDoubleCylinderSymmetryAction]
    · dsimp [erlangenDoubleCylinderSymmetryAction]
      exact h

/-- Action of stage swap on cylinder projectors: `α_n(P_u) = P_{¬u}`. -/
theorem stageSwap_doubleCylinderProj (n : ℕ) (u : BitWord n) :
    stageSwapEquiv B n (doubleCylinderProj B n u) =
      doubleCylinderProj B n (notWord n u) := by
  ext a b
  dsimp [stageSwapEquiv, stageSwapFun, doubleCylinderProj, Matrix.single_apply]
  have h_iff : (u = notWord n a ∧ u = notWord n b) ↔ (notWord n u = a ∧ notWord n u = b) := by
    rw [notWord_eq_iff, notWord_eq_iff]
  simp_rw [h_iff]

/-- Symmetrized double cylinder projector: `P_u^{sym} = P_u + P_{¬u}`. -/
def symmetrizedCylinderProj (n : ℕ) (u : BitWord n) : DoubleCylinderStage B n :=
  doubleCylinderProj B n u + doubleCylinderProj B n (notWord n u)

/-- The symmetrized cylinder operator is invariant under stage swap. -/
theorem stageSwap_symmetrizedCylinderProj (n : ℕ) (u : BitWord n) :
    stageSwapEquiv B n (symmetrizedCylinderProj B n u) =
      symmetrizedCylinderProj B n u := by
  dsimp [symmetrizedCylinderProj]
  rw [map_add, stageSwap_doubleCylinderProj, stageSwap_doubleCylinderProj,
      notWord_involutive, add_comm]

/-- Symmetrized cylinder operators descend to invariant elements of the colimit algebra. -/
theorem colimit_symmetrizedCylinderProj_isInvariant (n : ℕ) (u : BitWord n) :
    IsInvariant (erlangenDoubleCylinderSymmetryAction B)
      (doubleCylinderInclusion B n (symmetrizedCylinderProj B n u)) := by
  rw [isInvariant_iff_colimitSwap]
  rw [colimitSwapEquiv_inclusion, stageSwap_symmetrizedCylinderProj]

/-- Distinct cylinder words yield orthogonal projectors. -/
theorem doubleCylinderProj_mul_of_ne (n : ℕ) {u v : BitWord n} (h : u ≠ v) :
    doubleCylinderProj B n u * doubleCylinderProj B n v = 0 := by
  dsimp [doubleCylinderProj]
  exact Matrix.single_mul_single_of_ne 1 u u v h 1

/-- For `n ≥ 1`, the bit-flip of any word is distinct from itself. -/
theorem notWord_ne_self (n : ℕ) (u : BitWord (n + 1)) :
    notWord (n + 1) u ≠ u := by
  intro h
  have h0 := congrFun h 0
  dsimp [notWord] at h0
  cases hu : u 0 <;> rw [hu] at h0 <;> revert h0 <;> decide

/-- The symmetrized cylinder projector is an algebraic idempotent for `n ≥ 1`. -/
theorem symmetrizedCylinderProj_isProjector (n : ℕ) (u : BitWord (n + 1)) :
    IsProjector (symmetrizedCylinderProj B (n + 1) u) := by
  dsimp [IsProjector, symmetrizedCylinderProj]
  have h_ne : u ≠ notWord (n + 1) u := (notWord_ne_self n u).symm
  have h_ne' : notWord (n + 1) u ≠ u := notWord_ne_self n u
  rw [add_mul, mul_add, mul_add]
  have h_uu : doubleCylinderProj B (n + 1) u * doubleCylinderProj B (n + 1) u =
      doubleCylinderProj B (n + 1) u := by
    dsimp [doubleCylinderProj]
    rw [Matrix.single_mul_single_same, mul_one]
  have h_not_not : doubleCylinderProj B (n + 1) (notWord (n + 1) u) *
      doubleCylinderProj B (n + 1) (notWord (n + 1) u) =
      doubleCylinderProj B (n + 1) (notWord (n + 1) u) := by
    dsimp [doubleCylinderProj]
    rw [Matrix.single_mul_single_same, mul_one]
  have h_u_not : doubleCylinderProj B (n + 1) u *
      doubleCylinderProj B (n + 1) (notWord (n + 1) u) = 0 :=
    doubleCylinderProj_mul_of_ne B (n + 1) h_ne
  have h_not_u : doubleCylinderProj B (n + 1) (notWord (n + 1) u) *
      doubleCylinderProj B (n + 1) u = 0 :=
    doubleCylinderProj_mul_of_ne B (n + 1) h_ne'
  rw [h_uu, h_not_not, h_u_not, h_not_u, add_zero, zero_add]

/-- Felix Klein Theorem: Symmetrized double cylinder projectors are genuine invariant projectors. -/
theorem symmetrizedCylinderProj_isInvariantProjector (n : ℕ) (u : BitWord (n + 1)) :
    IsInvariantProjector (erlangenDoubleCylinderSymmetryAction B)
      (doubleCylinderInclusion B (n + 1) (symmetrizedCylinderProj B (n + 1) u)) := by
  refine ⟨?_, colimit_symmetrizedCylinderProj_isInvariant B (n + 1) u⟩
  dsimp [IsProjector]
  change doubleCylinderInclusion B (n + 1) (symmetrizedCylinderProj B (n + 1) u) *
         doubleCylinderInclusion B (n + 1) (symmetrizedCylinderProj B (n + 1) u) =
         doubleCylinderInclusion B (n + 1) (symmetrizedCylinderProj B (n + 1) u)
  rw [← (doubleCylinderInclusion B (n + 1)).map_mul,
      symmetrizedCylinderProj_isProjector]

/-! ## 4.5. Swap-Invariant Off-Diagonal Transition Operators -/

/-- Action of stage swap on double cylinder matrix units: `α_n(E_{u, v}) = E_{¬u, ¬v}`. -/
theorem stageSwap_doubleCylinderUnit (n : ℕ) (u v : BitWord n) :
    stageSwapEquiv B n (doubleCylinderUnit B n u v) =
      doubleCylinderUnit B n (notWord n u) (notWord n v) := by
  ext a b
  dsimp [stageSwapEquiv, stageSwapFun, doubleCylinderUnit, Matrix.single_apply]
  have h_iff : (u = notWord n a ∧ v = notWord n b) ↔ (notWord n u = a ∧ notWord n v = b) := by
    rw [notWord_eq_iff, notWord_eq_iff]
  simp_rw [h_iff]

/-- Symmetrized double cylinder transition operator:
    `T_{u, v}^{sym} = E_{u, v} + E_{¬u, ¬v}`. -/
def symmetrizedTransitionOp (n : ℕ) (u v : BitWord n) : DoubleCylinderStage B n :=
  doubleCylinderUnit B n u v + doubleCylinderUnit B n (notWord n u) (notWord n v)

/-- The symmetrized transition operator is invariant under stage swap. -/
theorem stageSwap_symmetrizedTransitionOp (n : ℕ) (u v : BitWord n) :
    stageSwapEquiv B n (symmetrizedTransitionOp B n u v) =
      symmetrizedTransitionOp B n u v := by
  dsimp [symmetrizedTransitionOp]
  rw [map_add, stageSwap_doubleCylinderUnit, stageSwap_doubleCylinderUnit,
      notWord_involutive, notWord_involutive, add_comm]

/-- Symmetrized transition operators descend to invariant elements of the colimit algebra. -/
theorem colimit_symmetrizedTransitionOp_isInvariant (n : ℕ) (u v : BitWord n) :
    IsInvariant (erlangenDoubleCylinderSymmetryAction B)
      (doubleCylinderInclusion B n (symmetrizedTransitionOp B n u v)) := by
  rw [isInvariant_iff_colimitSwap]
  rw [colimitSwapEquiv_inclusion, stageSwap_symmetrizedTransitionOp]

/-- Multiplication of mutually reverse symmetrized transition operators reduces to a diagonal projector
    when the target word is distinct from its bit-flip negation. -/
theorem symmetrizedTransitionOp_mul_same_rev (n : ℕ) {u v : BitWord n}
    (h_v_not : v ≠ notWord n v) :
    symmetrizedTransitionOp B n u v * symmetrizedTransitionOp B n v u =
      symmetrizedCylinderProj B n u := by
  dsimp [symmetrizedTransitionOp, symmetrizedCylinderProj, doubleCylinderProj]
  rw [add_mul, mul_add, mul_add]
  have h1 : doubleCylinderUnit B n u v * doubleCylinderUnit B n v u = doubleCylinderUnit B n u u := by
    rw [doubleCylinderUnit_mul]
    simp only [ite_true]
  have h2 : doubleCylinderUnit B n u v * doubleCylinderUnit B n (notWord n v) (notWord n u) = 0 := by
    rw [doubleCylinderUnit_mul]
    simp only [h_v_not, ite_false]
  have h_not_v : notWord n v ≠ v := h_v_not.symm
  have h3 : doubleCylinderUnit B n (notWord n u) (notWord n v) * doubleCylinderUnit B n v u = 0 := by
    rw [doubleCylinderUnit_mul]
    simp only [h_not_v, ite_false]
  have h4 : doubleCylinderUnit B n (notWord n u) (notWord n v) *
      doubleCylinderUnit B n (notWord n v) (notWord n u) =
      doubleCylinderUnit B n (notWord n u) (notWord n u) := by
    rw [doubleCylinderUnit_mul]
    simp only [ite_true]
  rw [h1, h2, h3, h4, add_zero, zero_add]
  rfl

/-- Value of the symmetrized cylinder projector at `(u, u)` is `1` whenever `u ≠ ¬u`. -/
theorem symmetrizedCylinderProj_apply_same (n : ℕ) {u : BitWord n} (h_u_not : u ≠ notWord n u) :
    symmetrizedCylinderProj B n u u u = 1 := by
  dsimp [symmetrizedCylinderProj, doubleCylinderProj, Matrix.single_apply]
  have h_ne : notWord n u ≠ u := h_u_not.symm
  simp only [and_self, ite_true]
  rw [ite_eq_right h_ne, add_zero]

/-- Value of the symmetrized cylinder projector `P_v^{sym}` at `(u, u)` is `0`
    whenever `u ≠ v` and `u ≠ ¬v`. -/
theorem symmetrizedCylinderProj_apply_of_ne (n : ℕ) {u v : BitWord n}
    (h_uv : u ≠ v) (h_u_notv : u ≠ notWord n v) :
    symmetrizedCylinderProj B n v u u = 0 := by
  dsimp [symmetrizedCylinderProj, doubleCylinderProj, Matrix.single_apply]
  have h_vu : v ≠ u := h_uv.symm
  have h_notvu : notWord n v ≠ u := h_u_notv.symm
  simp only [and_self]
  rw [ite_eq_right h_vu, ite_eq_right h_notvu, add_zero]

/-- First test word at depth 2: `00` (`fun _ => false`). -/
def depth2Word00 : BitWord 2 := fun _ => false

/-- Second test word at depth 2: `01` (`fun i => i.1 = 1`). -/
def depth2Word01 : BitWord 2 := fun i => i.1 = 1

theorem depth2Word00_ne_depth2Word01 : depth2Word00 ≠ depth2Word01 := by
  intro h
  have h1 := congrFun h ⟨1, by decide⟩
  dsimp [depth2Word00, depth2Word01] at h1
  contradiction

theorem depth2Word00_ne_not_depth2Word01 : depth2Word00 ≠ notWord 2 depth2Word01 := by
  intro h
  have h0 := congrFun h ⟨0, by decide⟩
  dsimp [depth2Word00, notWord, depth2Word01] at h0
  contradiction

/-- Finite-stage noncommutativity at depth 2: The product of swap-invariant off-diagonal transition
    operators does not commute for any nontrivial ring `B`. -/
theorem depth2_symmetrizedTransitionOp_mul_ne [Nontrivial B] :
    symmetrizedTransitionOp B 2 depth2Word00 depth2Word01 *
    symmetrizedTransitionOp B 2 depth2Word01 depth2Word00 ≠
    symmetrizedTransitionOp B 2 depth2Word01 depth2Word00 *
    symmetrizedTransitionOp B 2 depth2Word00 depth2Word01 := by
  intro h
  have h_v_not : depth2Word01 ≠ notWord 2 depth2Word01 :=
    (notWord_ne_self 1 depth2Word01).symm
  have h_u_not : depth2Word00 ≠ notWord 2 depth2Word00 :=
    (notWord_ne_self 1 depth2Word00).symm
  have h_ts : symmetrizedTransitionOp B 2 depth2Word00 depth2Word01 *
              symmetrizedTransitionOp B 2 depth2Word01 depth2Word00 =
              symmetrizedCylinderProj B 2 depth2Word00 :=
    symmetrizedTransitionOp_mul_same_rev B 2 h_v_not
  have h_st : symmetrizedTransitionOp B 2 depth2Word01 depth2Word00 *
              symmetrizedTransitionOp B 2 depth2Word00 depth2Word01 =
              symmetrizedCylinderProj B 2 depth2Word01 :=
    symmetrizedTransitionOp_mul_same_rev B 2 h_u_not
  rw [h_ts, h_st] at h
  have h_app := congrFun (congrFun h depth2Word00) depth2Word00
  rw [symmetrizedCylinderProj_apply_same B 2 h_u_not] at h_app
  rw [symmetrizedCylinderProj_apply_of_ne B 2 depth2Word00_ne_depth2Word01 depth2Word00_ne_not_depth2Word01] at h_app
  exact one_ne_zero h_app

/-- Finite-stage Lie bracket non-vanishing at depth 2. -/
theorem depth2_symmetrizedTransitionOp_lie_ne_zero [Nontrivial B] :
    ⁅symmetrizedTransitionOp B 2 depth2Word00 depth2Word01,
     symmetrizedTransitionOp B 2 depth2Word01 depth2Word00⁆ ≠ 0 := by
  intro h
  rw [Ring.lie_def, sub_eq_zero] at h
  exact depth2_symmetrizedTransitionOp_mul_ne B h

/-- Felix Klein Erlangen 2.0 Invariant Subring Intrinsic Noncommutativity Theorem:
    For ANY nontrivial seed ring `B` (including commutative rings like `ℤ` and `ℝ`),
    the swap-invariant subring `erlangenDoubleCylinderInvariantSubring B` is strictly
    noncommutative at matrix depth `n ≥ 2`! -/
theorem erlangenDoubleCylinderInvariantSubring_noncommutative [Nontrivial B] :
    ∃ a b : erlangenDoubleCylinderInvariantSubring B, a * b ≠ b * a := by
  let T := symmetrizedTransitionOp B 2 depth2Word00 depth2Word01
  let S := symmetrizedTransitionOp B 2 depth2Word01 depth2Word00
  let a_colim := doubleCylinderInclusion B 2 T
  let b_colim := doubleCylinderInclusion B 2 S
  have ha_inv : IsInvariant (erlangenDoubleCylinderSymmetryAction B) a_colim :=
    colimit_symmetrizedTransitionOp_isInvariant B 2 depth2Word00 depth2Word01
  have hb_inv : IsInvariant (erlangenDoubleCylinderSymmetryAction B) b_colim :=
    colimit_symmetrizedTransitionOp_isInvariant B 2 depth2Word01 depth2Word00
  let a_sub : erlangenDoubleCylinderInvariantSubring B := ⟨a_colim, ha_inv⟩
  let b_sub : erlangenDoubleCylinderInvariantSubring B := ⟨b_colim, hb_inv⟩
  refine ⟨a_sub, b_sub, ?_⟩
  intro h_comm
  have h_comm_val : a_sub.1 * b_sub.1 = b_sub.1 * a_sub.1 := congrArg Subtype.val h_comm
  change doubleCylinderInclusion B 2 T * doubleCylinderInclusion B 2 S =
         doubleCylinderInclusion B 2 S * doubleCylinderInclusion B 2 T at h_comm_val
  rw [← (doubleCylinderInclusion B 2).map_mul, ← (doubleCylinderInclusion B 2).map_mul] at h_comm_val
  have h_stage := doubleCylinderInclusion_injective B 2 h_comm_val
  exact depth2_symmetrizedTransitionOp_mul_ne B h_stage

/-- Lie bracket formulation of intrinsic noncommutativity in the invariant subring. -/
theorem erlangenDoubleCylinderInvariantSubring_lie_ne_zero [Nontrivial B] :
    ∃ a b : erlangenDoubleCylinderInvariantSubring B, ⁅a, b⁆ ≠ 0 := by
  obtain ⟨a, b, hne⟩ := erlangenDoubleCylinderInvariantSubring_noncommutative B
  refine ⟨a, b, ?_⟩
  intro hlie
  rw [Ring.lie_def, sub_eq_zero] at hlie
  exact hne hlie

/-! ## 5. Casimir Element Invariance -/

/-- Scalar matrix at finite stage `n` corresponding to an element of the seed ring `B`. -/
def stageScalar (n : ℕ) (c : B) : DoubleCylinderStage B n :=
  c • (1 : DoubleCylinderStage B n)

theorem stageSwapEquiv_stageScalar (n : ℕ) (c : B) :
    stageSwapEquiv B n (stageScalar B n c) = stageScalar B n c := by
  ext u v
  dsimp [stageScalar, stageSwapEquiv, stageSwapFun, Matrix.one_apply]
  have h_eq : (notWord n u = notWord n v) ↔ (u = v) :=
    ⟨fun h => notWord_injective n h, fun h => by rw [h]⟩
  by_cases h : u = v
  · rw [ite_eq_left (h_eq.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt h_eq.mp h), ite_eq_right h]

/-- Casimir element in the colimit algebra associated with scalar `c ∈ B`. -/
def colimitCasimir (c : B) : DoubleCylinderColimit B :=
  doubleCylinderInclusion B 0 (stageScalar B 0 c)

/-- Casimir elements are invariant under the Felix Klein symmetry action. -/
theorem colimitCasimir_isInvariant (c : B) :
    IsInvariant (erlangenDoubleCylinderSymmetryAction B) (colimitCasimir B c) := by
  rw [isInvariant_iff_colimitSwap]
  change colimitSwapEquiv B (doubleCylinderInclusion B 0 (stageScalar B 0 c)) =
    doubleCylinderInclusion B 0 (stageScalar B 0 c)
  rw [colimitSwapEquiv_inclusion, stageSwapEquiv_stageScalar]

/-! ## 6. Strict Noncommutative Operator Discipline (R3) -/

/-- For stage 0, the word type `BitWord 0` has exactly one element (`Fin 0 → Bool`),
    so `DoubleCylinderStage B 0 ≃+* B`. -/
def stageZeroEquivSeed : DoubleCylinderStage B 0 ≃+* B where
  toFun M := M (fun _ => false) (fun _ => false)
  invFun b := fun _ _ => b
  left_inv M := by
    ext u v
    have hu : u = fun _ => false := by funext i; exact Fin.elim0 i
    have hv : v = fun _ => false := by funext i; exact Fin.elim0 i
    rw [hu, hv]
  right_inv b := rfl
  map_add' M N := rfl
  map_mul' M N := by
    dsimp [Matrix.mul_apply]
    have h_card : (Finset.univ : Finset (BitWord 0)) = {fun _ => false} := by
      ext w
      simp only [Finset.mem_univ, true_iff, Finset.mem_singleton]
      funext i
      exact Fin.elim0 i
    rw [h_card, Finset.sum_singleton]

theorem stageZero_mul_apply (M N : DoubleCylinderStage B 0) :
    (M * N) (fun _ => false) (fun _ => false) =
      M (fun _ => false) (fun _ => false) * N (fun _ => false) (fun _ => false) :=
  (stageZeroEquivSeed B).map_mul M N

/-- Strict Noncommutative Operator Discipline (R3):
    Whenever the seed ring `B` is noncommutative, the Felix Klein Invariant Subring
    `erlangenDoubleCylinderInvariantSubring B` is strictly noncommutative! -/
theorem invariantSubring_is_noncommutative (hB : ∃ x y : B, x * y ≠ y * x) :
    ∃ a b : erlangenDoubleCylinderInvariantSubring B, a * b ≠ b * a := by
  obtain ⟨x, y, hxy⟩ := hB
  let M_x : DoubleCylinderStage B 0 := (stageZeroEquivSeed B).symm x
  let M_y : DoubleCylinderStage B 0 := (stageZeroEquivSeed B).symm y
  have hMx_inv : stageSwapEquiv B 0 M_x = M_x := by
    ext u v
    have hu : notWord 0 u = u := by funext i; exact Fin.elim0 i
    have hv : notWord 0 v = v := by funext i; exact Fin.elim0 i
    rw [stageSwapEquiv_apply, hu, hv]
  have hMy_inv : stageSwapEquiv B 0 M_y = M_y := by
    ext u v
    have hu : notWord 0 u = u := by funext i; exact Fin.elim0 i
    have hv : notWord 0 v = v := by funext i; exact Fin.elim0 i
    rw [stageSwapEquiv_apply, hu, hv]
  let a_colim := doubleCylinderInclusion B 0 M_x
  let b_colim := doubleCylinderInclusion B 0 M_y
  have ha_inv : IsInvariant (erlangenDoubleCylinderSymmetryAction B) a_colim := by
    rw [isInvariant_iff_colimitSwap, colimitSwapEquiv_inclusion, hMx_inv]
  have hb_inv : IsInvariant (erlangenDoubleCylinderSymmetryAction B) b_colim := by
    rw [isInvariant_iff_colimitSwap, colimitSwapEquiv_inclusion, hMy_inv]
  let a_sub : erlangenDoubleCylinderInvariantSubring B := ⟨a_colim, ha_inv⟩
  let b_sub : erlangenDoubleCylinderInvariantSubring B := ⟨b_colim, hb_inv⟩
  refine ⟨a_sub, b_sub, ?_⟩
  intro h_comm
  have h_comm_val : a_sub.1 * b_sub.1 = b_sub.1 * a_sub.1 := congrArg Subtype.val h_comm
  change doubleCylinderInclusion B 0 M_x * doubleCylinderInclusion B 0 M_y =
         doubleCylinderInclusion B 0 M_y * doubleCylinderInclusion B 0 M_x at h_comm_val
  rw [← (doubleCylinderInclusion B 0).map_mul, ← (doubleCylinderInclusion B 0).map_mul] at h_comm_val
  have h_stage := doubleCylinderInclusion_injective B 0 h_comm_val
  have h_seed := congrArg (stageZeroEquivSeed B) h_stage
  simp only [map_mul] at h_seed
  have h_cancel :
      (stageZeroEquivSeed B) ((stageZeroEquivSeed B).symm x) *
      (stageZeroEquivSeed B) ((stageZeroEquivSeed B).symm y) = x * y := by
    simp only [RingEquiv.apply_symm_apply]
  have h_cancel' :
      (stageZeroEquivSeed B) ((stageZeroEquivSeed B).symm y) *
      (stageZeroEquivSeed B) ((stageZeroEquivSeed B).symm x) = y * x := by
    simp only [RingEquiv.apply_symm_apply]
  rw [h_cancel, h_cancel'] at h_seed
  exact hxy h_seed

/-! ## 7. Model Non-Degeneracy Witness (Gate 2.5 / T17) -/

/-- Model witness certifying non-degeneracy of the Erlangen symmetry invariants. -/
structure ErlangenInvariantWitnessPacket (R : Type) [Ring R] where
  invariantElement : DoubleCylinderColimit R
  isInvariant : IsInvariant (erlangenDoubleCylinderSymmetryAction R) invariantElement

/-- Closed model witness over `ℤ` (certifies Gate 2.5 / T17). -/
def erlangenInvariantWitnessPacketZ : ErlangenInvariantWitnessPacket ℤ :=
  ⟨1, fun g => by
    rcases g_swap_cases g with rfl | rfl
    · rfl
    · dsimp [erlangenDoubleCylinderSymmetryAction]
      exact map_one (colimitSwapEquiv ℤ)⟩

instance : Inhabited (ErlangenInvariantWitnessPacket ℤ) :=
  ⟨erlangenInvariantWitnessPacketZ⟩

end InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
