import Mathlib.Tactic

/-!
# Fenchel Duality and Spacetime Optimization

Concrete finite-dimensional theorem layer for the quadratic potential
`Phi(x) = x^2 / 2`.  This avoids global convex-analysis axioms while keeping
the primal/dual mirror used by the Tomita/Fenchel dictionary.
-/

noncomputable section

set_option linter.unnecessarySimpa false

open Set

def Phi (x : ℝ) : ℝ := x ^ 2 / 2

noncomputable def fenchelConjugateQuadratic (p : ℝ) : ℝ :=
  sSup (Set.range fun x : ℝ => p * x - Phi x)

noncomputable def bregmanQuadratic (x y : ℝ) : ℝ :=
  Phi x - Phi y - y * (x - y)

theorem fenchelConjugateQuadratic_eq (p : ℝ) :
    fenchelConjugateQuadratic p = p ^ 2 / 2 := by
  have h_bound : ∀ x : ℝ, p * x - Phi x ≤ p ^ 2 / 2 := by
    intro x
    unfold Phi
    nlinarith [sq_nonneg (x - p)]
  have h_nonempty : (Set.range fun x : ℝ => p * x - Phi x).Nonempty := by
    refine ⟨p ^ 2 / 2, p, ?_⟩
    unfold Phi
    ring
  apply le_antisymm
  · exact csSup_le h_nonempty (by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact h_bound x)
  · have h_mem : p ^ 2 / 2 ∈ Set.range (fun x : ℝ => p * x - Phi x) := by
      refine ⟨p, ?_⟩
      unfold Phi
      ring
    have h_bdd : BddAbove (Set.range fun x : ℝ => p * x - Phi x) := by
      refine ⟨p ^ 2 / 2, ?_⟩
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact h_bound x
    exact le_csSup h_bdd h_mem

theorem fenchelYoung_quadratic (x p : ℝ) :
    x * p ≤ Phi x + fenchelConjugateQuadratic p := by
  rw [fenchelConjugateQuadratic_eq]
  unfold Phi
  nlinarith [sq_nonneg (x - p)]

theorem fenchelYoung_eq_on_gradient (x : ℝ) :
    Phi x + fenchelConjugateQuadratic x = x * x := by
  rw [fenchelConjugateQuadratic_eq]
  unfold Phi
  ring

theorem fenchel_biconjugate_quadratic (x : ℝ) :
    sSup (Set.range fun p : ℝ => x * p - fenchelConjugateQuadratic p) = Phi x := by
  have hfun :
      (fun p : ℝ => x * p - fenchelConjugateQuadratic p) =
        (fun p : ℝ => x * p - p ^ 2 / 2) := by
    funext p
    rw [fenchelConjugateQuadratic_eq]
  rw [hfun]
  simpa [fenchelConjugateQuadratic, Phi] using fenchelConjugateQuadratic_eq x

theorem quadratic_gradient (x : ℝ) :
    deriv Phi x = x := by
  unfold Phi
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hhalf : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * x ^ 2)
      ((1 / 2 : ℝ) * (2 * x)) x :=
    hsq.const_mul (1 / 2 : ℝ)
  simpa [mul_comm, mul_left_comm] using hhalf.deriv

theorem quadratic_gradient_inverse (x : ℝ) :
    deriv Phi (deriv Phi x) = x := by
  rw [quadratic_gradient x]
  exact quadratic_gradient x

theorem bregmanQuadratic_eq_square (x y : ℝ) :
    bregmanQuadratic x y = (x - y) ^ 2 / 2 := by
  unfold bregmanQuadratic Phi
  ring

theorem bregmanQuadratic_nonnegative (x y : ℝ) :
    0 ≤ bregmanQuadratic x y := by
  rw [bregmanQuadratic_eq_square]
  nlinarith [sq_nonneg (x - y)]

theorem universe_is_convex_optimization (x p : ℝ) :
    x * p ≤ Phi x + fenchelConjugateQuadratic p ∧
    sSup (Set.range fun q : ℝ => x * q - fenchelConjugateQuadratic q) = Phi x ∧
    deriv Phi (deriv Phi x) = x ∧
    ∀ y, 0 ≤ bregmanQuadratic x y := by
  exact ⟨fenchelYoung_quadratic x p, fenchel_biconjugate_quadratic x,
    quadratic_gradient_inverse x, bregmanQuadratic_nonnegative x⟩
