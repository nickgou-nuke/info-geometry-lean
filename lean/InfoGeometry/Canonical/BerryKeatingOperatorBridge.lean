import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Real dilation differential identities

These are identities for real differentiable functions. No Hilbert-space domain,
self-adjoint realization, or spectral identification is asserted here.

This module formalizes genuine, non-vacuous differential identities for the Berry-Keating operator in Mathlib 4:
1. **Canonical Heisenberg-Weyl Commutator $[D, X] f = f$**:
   $$(D \circ X - X \circ D) f = f$$
2. **Exact Berry-Keating Symmetric Form $H f = x f' + \frac{1}{2} f$**:
   $$H f = \frac{1}{2} (X (D f) + D (X f)) = x \frac{df}{dx} + \frac{1}{2} f$$
3. **Exact Monomial Scaling Eigenvalues $(X \circ D)(x^n) = n x^n$**:
   $$x \frac{d}{dx}(x^n) = n x^n \quad (\forall n \in \mathbb{N})$$
4. **Monomial differential identity**:
   $$H(x^n) = \left(n + \frac{1}{2}\right) x^n$$
5. **Exact Integration by Parts and Boundary Pairing on $[0, 1]$**:
   $$\int_0^1 (x f'(x) g(x) + x f(x) g'(x) + f(x) g(x)) \, dx = f(1) g(1)$$
-/

noncomputable section

namespace InfoGeometry.Canonical.BerryKeating

open Real intervalIntegral MeasureTheory

/-- Multiplication operator by coordinate x -/
def posOp (f : ℝ → ℝ) : ℝ → ℝ := fun x => x * f x

/-- Derivative operator D -/
def derivOp (f : ℝ → ℝ) : ℝ → ℝ := fun x => deriv f x

/-- 🏆 THEOREM 1: Exact Heisenberg-Weyl Commutator [D, X] f = f for Differentiable Functions -/
theorem heisenberg_weyl_commutator (f : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) :
    derivOp (posOp f) x - posOp (derivOp f) x = f x := by
  have h_mul := deriv_mul (differentiableAt_id : DifferentiableAt ℝ id x) hf
  have h_deriv_id : deriv id x = 1 := deriv_id x
  have h_pos_deriv : deriv (fun y => y * f y) x = 1 * f x + x * deriv f x := by
    calc deriv (fun y => y * f y) x = deriv (id * f) x := rfl
    _ = deriv id x * f x + id x * deriv f x := h_mul
    _ = 1 * f x + x * deriv f x := by rw [h_deriv_id]; rfl
  dsimp [posOp, derivOp]
  change deriv (fun y => y * f y) x - x * deriv f x = f x
  rw [h_pos_deriv]
  ring

/-- 🏆 THEOREM 2: Exact Berry-Keating Symmetric Form H f = x f' + (1/2) f -/
theorem berry_keating_symmetric_form (f : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) :
    (1 / 2 : ℝ) * (x * deriv f x + deriv (fun y => y * f y) x) =
      x * deriv f x + (1 / 2 : ℝ) * f x := by
  have h_mul := deriv_mul (differentiableAt_id : DifferentiableAt ℝ id x) hf
  have h_deriv_id : deriv id x = 1 := deriv_id x
  have h_pos_deriv : deriv (fun y => y * f y) x = 1 * f x + x * deriv f x := by
    calc deriv (fun y => y * f y) x = deriv (id * f) x := rfl
    _ = deriv id x * f x + id x * deriv f x := h_mul
    _ = 1 * f x + x * deriv f x := by rw [h_deriv_id]; rfl
  rw [h_pos_deriv]
  ring

/-- 🏆 THEOREM 3: Exact Monomial Eigenvalue Equation for x (d/dx) (x^n) = n x^n -/
theorem monomial_scaling_eigenvalue (n : ℕ) (x : ℝ) :
    x * deriv (fun y => y ^ n) x = (n : ℝ) * x ^ n := by
  have h_deriv : deriv (fun y => y ^ n) x = (n : ℝ) * x ^ (n - 1) := by
    exact (hasDerivAt_pow n x).deriv
  rw [h_deriv]
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn_sub : n = (n - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn))).symm
    have h_pow_x : x * x ^ (n - 1) = x ^ n := by
      conv_rhs => rw [hn_sub]
      rw [pow_succ]
      ring
    calc x * ((n : ℝ) * x ^ (n - 1)) = (n : ℝ) * (x * x ^ (n - 1)) := by ring
    _ = (n : ℝ) * x ^ n := by rw [h_pow_x]

/-- 🏆 THEOREM 4: Exact Berry-Keating Eigenvalue on Monomials H (x^n) = (n + 1/2) x^n -/
theorem berry_keating_monomial_eigenvalue (n : ℕ) (x : ℝ) :
    x * deriv (fun y => y ^ n) x + (1 / 2 : ℝ) * x ^ n =
      ((n : ℝ) + 1 / 2) * x ^ n := by
  rw [monomial_scaling_eigenvalue n x]
  ring

/-- Boundary pairing for the real dilation expression on an oriented interval.
Only integrability of the differentiated product is required. -/
theorem scaling_generator_boundary_pairing (f g : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (deriv f x) x)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (deriv g x) x)
    (hi : IntervalIntegrable
      (fun x => x * deriv f x * g x + x * f x * deriv g x + f x * g x) volume a b) :
    ∫ x in a..b, (x * deriv f x * g x + x * f x * deriv g x + f x * g x) =
      b * f b * g b - a * f a * g a := by
  have h_prod_deriv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y => y * f y * g y) (x * deriv f x * g x + x * f x * deriv g x + f x * g x) x := by
    intro x hx
    have hx_id : HasDerivAt id 1 x := hasDerivAt_id x
    have hx_f : HasDerivAt f (deriv f x) x := hf x hx
    have hx_g : HasDerivAt g (deriv g x) x := hg x hx
    have h_xf : HasDerivAt (fun y => y * f y) (1 * f x + x * deriv f x) x := by
      have := HasDerivAt.mul hx_id hx_f
      exact this
    have h_total := HasDerivAt.mul h_xf hx_g
    have h_alg : (1 * f x + x * deriv f x) * g x + (x * f x) * deriv g x =
        x * deriv f x * g x + x * f x * deriv g x + f x * g x := by ring
    rw [h_alg] at h_total
    exact h_total
  have h_ftc := integral_eq_sub_of_hasDerivAt (f := fun y => y * f y * g y)
    (f' := fun x => x * deriv f x * g x + x * f x * deriv g x + f x * g x)
    h_prod_deriv hi
  exact h_ftc

/-- The coordinate factor makes the lower boundary term vanish at zero. -/
theorem scaling_generator_integration_by_parts (f g : ℝ → ℝ)
    (hf : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (deriv f x) x)
    (hg : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt g (deriv g x) x)
    (h_cont : Continuous (fun x => x * deriv f x * g x + x * f x * deriv g x + f x * g x)) :
    ∫ x in (0:ℝ)..1, (x * deriv f x * g x + x * f x * deriv g x + f x * g x) =
      f 1 * g 1 := by
  simpa using scaling_generator_boundary_pairing f g 0 1 hf hg
    (h_cont.intervalIntegrable 0 1)

end InfoGeometry.Canonical.BerryKeating
