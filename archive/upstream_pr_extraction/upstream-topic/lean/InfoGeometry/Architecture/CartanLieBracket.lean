import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Lattice

namespace InfoGeometry.Architecture

/-!
# Common Lie-bracket law for Cartan geometry

This is the single owner for the algebraic Lie-bracket laws used by the
Cartan/nomizu architecture.  The surrounding geometry modules supply their
own grading, involution, and curvature data.
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A bilinear, skew bracket satisfying the Jacobi identity. -/
structure IsLieBracket (bracket : V → V → V) : Prop where
  skew : ∀ x y, bracket x y = - bracket y x
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  smul_left : ∀ (c : ℝ) x y, bracket (c • x) y = c • bracket x y
  smul_right : ∀ (c : ℝ) x y, bracket x (c • y) = c • bracket x y
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0

/-- The three bracket-closure laws of a Cartan symmetric grading. -/
structure CartanGrading (bracket : V → V → V)
    (k_space p_space : Submodule ℝ V) : Prop where
  k_k : ∀ x y, x ∈ k_space → y ∈ k_space → bracket x y ∈ k_space
  k_p : ∀ x y, x ∈ k_space → y ∈ p_space → bracket x y ∈ p_space
  p_p : ∀ x y, x ∈ p_space → y ∈ p_space → bracket x y ∈ k_space

lemma bracket_zero_left (bracket : V → V → V)
    (h_lie : IsLieBracket bracket) (x : V) :
    bracket (0 : V) x = 0 := by
  have hz := h_lie.smul_left (0 : ℝ) (0 : V) x
  rw [zero_smul, zero_smul] at hz
  exact hz

lemma bracket_zero_right (bracket : V → V → V)
    (h_lie : IsLieBracket bracket) (x : V) :
    bracket x (0 : V) = 0 := by
  have hz := h_lie.smul_right (0 : ℝ) x (0 : V)
  rw [zero_smul, zero_smul] at hz
  exact hz

lemma bracket_neg_left (bracket : V → V → V)
    (h_lie : IsLieBracket bracket) (x y : V) :
    bracket (-x) y = - bracket x y := by
  have h := h_lie.smul_left (-1 : ℝ) x y
  rw [neg_one_smul, neg_one_smul] at h
  exact h

lemma bracket_neg_right (bracket : V → V → V)
    (h_lie : IsLieBracket bracket) (x y : V) :
    bracket x (-y) = - bracket x y := by
  have h := h_lie.smul_right (-1 : ℝ) x y
  rw [neg_one_smul, neg_one_smul] at h
  exact h

lemma bracket_neg_neg (bracket : V → V → V)
    (h_lie : IsLieBracket bracket) (x y : V) :
    bracket (-x) (-y) = bracket x y := by
  rw [bracket_neg_left bracket h_lie, bracket_neg_right bracket h_lie, neg_neg]

end InfoGeometry.Architecture
