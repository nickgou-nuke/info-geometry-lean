import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Finite matrix mixtures for routing.

This owner formalizes only the linear-algebraic part of a finite orbit-polytope
construction.  It does not identify a mixture with an automorphism or a
Clifford action.
-/

namespace InfoGeometry.Routing.FiniteMatrixMixture

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

structure FiniteMatrixRepresentation (G : Type*) (n : ℕ) [Fintype G] where
  value : G → Mat n

/-! A genuine multiplicative representation, separated from the weaker
finite family above.  This is the prerequisite for Reynolds averaging. -/
structure FiniteMatrixGroupRepresentation (G : Type*) (n : ℕ)
    [Fintype G] [Group G] extends FiniteMatrixRepresentation G n where
  map_one : value 1 = 1
  map_mul : ∀ g h : G, value (g * h) = value g * value h

def rightTranslate {G : Type*} [Group G] (h : G) : G ≃ G where
  toFun g := g * h
  invFun g := g * h⁻¹
  left_inv g := by simp [mul_assoc]
  right_inv g := by simp [mul_assoc]

def leftTranslate {G : Type*} [Group G] (h : G) : G ≃ G where
  toFun g := h * g
  invFun g := h⁻¹ * g
  left_inv g := by simp
  right_inv g := by simp

theorem sum_rep_mul_right {G : Type*} {n : ℕ} [Fintype G] [Group G]
    (rep : FiniteMatrixGroupRepresentation G n) (h : G) :
    (∑ g, rep.value g) * rep.value h = ∑ g, rep.value g := by
  rw [Finset.sum_mul]
  have hsum := Equiv.sum_comp (rightTranslate h) (fun g => rep.value g)
  change (∑ g, rep.value (g * h)) = ∑ g, rep.value g at hsum
  calc
    (∑ g, rep.value g * rep.value h) = ∑ g, rep.value (g * h) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← rep.map_mul]
    _ = ∑ g, rep.value g := hsum

theorem sum_mul_rep_left {G : Type*} {n : ℕ} [Fintype G] [Group G]
    (rep : FiniteMatrixGroupRepresentation G n) (h : G) :
    rep.value h * (∑ g, rep.value g) = ∑ g, rep.value g := by
  rw [Finset.mul_sum]
  have hsum := Equiv.sum_comp (leftTranslate h) (fun g => rep.value g)
  change (∑ g, rep.value (h * g)) = ∑ g, rep.value g at hsum
  calc
    (∑ g, rep.value h * rep.value g) = ∑ g, rep.value (h * g) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← rep.map_mul]
    _ = ∑ g, rep.value g := hsum

noncomputable def reynoldsOperator {G : Type*} {n : ℕ} [Fintype G] [Group G]
    (rep : FiniteMatrixGroupRepresentation G n) : Mat n :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g, rep.value g

theorem reynolds_mul_right {G : Type*} {n : ℕ} [Fintype G] [Group G]
    (rep : FiniteMatrixGroupRepresentation G n) (h : G) :
    reynoldsOperator rep * rep.value h = reynoldsOperator rep := by
  unfold reynoldsOperator
  rw [smul_mul_assoc, sum_rep_mul_right]

theorem reynolds_mul_left {G : Type*} {n : ℕ} [Fintype G] [Group G]
    (rep : FiniteMatrixGroupRepresentation G n) (h : G) :
    rep.value h * reynoldsOperator rep = reynoldsOperator rep := by
  unfold reynoldsOperator
  rw [mul_smul_comm, sum_mul_rep_left]

theorem reynolds_idempotent {G : Type*} {n : ℕ} [Fintype G] [Group G]
    (rep : FiniteMatrixGroupRepresentation G n) :
    reynoldsOperator rep * reynoldsOperator rep = reynoldsOperator rep := by
  rw [show reynoldsOperator rep * reynoldsOperator rep =
      reynoldsOperator rep * ((Fintype.card G : ℝ)⁻¹ • ∑ g, rep.value g) from rfl]
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [reynolds_mul_right]
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  simp only [Matrix.smul_apply]
  rw [nsmul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

structure Weights (G : Type*) [Fintype G] where
  value : G → ℝ
  nonneg : ∀ g, 0 ≤ value g
  sum_one : ∑ g, value g = 1

def softLift {G : Type*} {n : ℕ} [Fintype G]
    (rep : FiniteMatrixRepresentation G n) (w : Weights G) : Mat n :=
  ∑ g, (w.value g) • rep.value g

theorem softLift_trace {G : Type*} {n : ℕ} [Fintype G]
    (rep : FiniteMatrixRepresentation G n) (w : Weights G) :
    Matrix.trace (softLift rep w) =
      ∑ g, w.value g * Matrix.trace (rep.value g) := by
  simp [softLift, Matrix.trace_sum]

def deltaWeights {G : Type*} [Fintype G] [DecidableEq G]
    (g₀ : G) : Weights G where
  value g := if g = g₀ then 1 else 0
  nonneg g := by
    split <;> norm_num
  sum_one := by
    simp

theorem softLift_delta {G : Type*} {n : ℕ} [Fintype G] [DecidableEq G]
    (rep : FiniteMatrixRepresentation G n) (g₀ : G) :
    softLift rep (deltaWeights g₀) = rep.value g₀ := by
  simp [softLift, deltaWeights]

end InfoGeometry.Routing.FiniteMatrixMixture
