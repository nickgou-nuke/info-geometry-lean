import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.Data.Real.Basic

/-!
# Isometric Tower Structure

This file defines the `IsometricTower` structure for a directed sequence 
of isometric embeddings over the natural numbers.
-/

variable {V : ℕ → Type} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
variable (Q : ∀ n, QuadraticForm ℝ (V n))

/-- 
  A strict isometric tower structure over the natural numbers.
-/
structure IsometricTower where
  iso : ∀ (n m : ℕ) (h : n ≤ m), Q n →qᵢ Q m
  iso_id : ∀ (n : ℕ) (h : n ≤ n), iso n n h = QuadraticMap.Isometry.id (Q n)
  iso_comp : ∀ (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n), 
    (iso m n hmn).comp (iso l m hlm) = iso l n (le_trans hlm hmn)
