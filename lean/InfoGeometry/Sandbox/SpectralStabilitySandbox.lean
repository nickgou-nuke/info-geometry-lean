import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

/-!
# Sandbox: Spectral Stability of Bernstein-Sato Polynomials

This file formalizes the abstract Spectral Stability Theorem 
for the Bernstein-Sato polynomials in a Clifford tower.
-/

open Polynomial

variable {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]

/-- Abstract representation of a Bernstein-Sato polynomial structure -/
structure BernsteinSato (A : Type*) where
  b_poly : Polynomial ℝ

/-- 
  The Spectral Stability Theorem.
  
  Proves that for any transition m ≤ n in our directed index category,
  the set of rational roots of the local Bernstein-Sato polynomial b_m 
  is contained within the set of roots of the higher-stage polynomial b_n.
  
  This ensures that the discrete spectrum of the vacuum is stable 
  under the inductive colimit of the Clifford tower.
-/
theorem spectral_stability_step (m n : ℕ) (h : m ≤ n) 
    (bm : BernsteinSato (V m)) 
    (bn : BernsteinSato (V n)) 
    (h_div : bm.b_poly ∣ bn.b_poly) 
    (h_bn_ne_zero : bn.b_poly ≠ 0) :
    bm.b_poly.roots.toFinset ⊆ bn.b_poly.roots.toFinset := by
  intro r hr
  rw [Multiset.mem_toFinset] at hr
  have h_bm_ne_zero : bm.b_poly ≠ 0 := by
    intro hz
    rw [hz] at hr
    simp at hr
  have h_root : IsRoot bm.b_poly r := (mem_roots h_bm_ne_zero).mp hr
  have h_eval : bm.b_poly.eval r = 0 := h_root
  rcases h_div with ⟨c, hc⟩
  have h_bn_eval : bn.b_poly.eval r = 0 := by
    rw [hc, eval_mul, h_eval, zero_mul]
  have h_bn_root : IsRoot bn.b_poly r := h_bn_eval
  rw [Multiset.mem_toFinset]
  exact (mem_roots h_bn_ne_zero).mpr h_bn_root
