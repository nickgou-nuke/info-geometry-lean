/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.MajoranaPolyaHilbert.BerryKeating
import InfoGeometry.Algebra.NoncommutativeTetraktysFlows
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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

/-! ### Logarithmic Radial-Time Pullback & Fractional Power Eigenvalues -/

/-- Berry-Keating symmetric differential expression `(H f)(x) = x f'(x) + ½ f(x)`. -/
def bkOp (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * deriv f x + (1 / 2 : ℝ) * f x

/-- Half-density logarithmic pullback `x^(-1/2) g(log x)` turning `x d/dx + 1/2` into `d/du`. -/
def halfDensityPullback (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * Real.log x) * g (Real.log x)

/-- Pulling back the scaling vector field `x d/dx` by `u = log x` gives `d/du`. -/
theorem scaling_log_pullback (g : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hg : DifferentiableAt ℝ g (Real.log x)) :
    x * deriv (fun y => g (Real.log y)) x = deriv g (Real.log x) := by
  have hcomp : HasDerivAt (fun y => g (Real.log y)) (deriv g (Real.log x) * x⁻¹) x :=
    hg.hasDerivAt.comp x (Real.hasDerivAt_log (ne_of_gt hx))
  rw [hcomp.deriv]
  field_simp [ne_of_gt hx]

/-- Logarithmic-time pullback of the Berry-Keating symmetric operator `x d/dx + 1/2`. -/
theorem berry_keating_log_pullback (g : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hg : DifferentiableAt ℝ g (Real.log x)) :
    bkOp (fun y => g (Real.log y)) x = deriv g (Real.log x) + (1 / 2 : ℝ) * g (Real.log x) := by
  dsimp [bkOp]
  rw [scaling_log_pullback g hx hg]

/-- The half-density pullback `x^(-1/2) g(log x)` intertwines `bkOp` directly with `d/du`. -/
theorem berry_keating_halfDensity_intertwines_deriv (g : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hg : DifferentiableAt ℝ g (Real.log x)) :
    bkOp (halfDensityPullback g) x = Real.exp (-(1 / 2 : ℝ) * Real.log x) * deriv g (Real.log x) := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have hexp : HasDerivAt (fun y => Real.exp (-(1 / 2 : ℝ) * Real.log y))
      (Real.exp (-(1 / 2 : ℝ) * Real.log x) * (-(1 / 2 : ℝ) * x⁻¹)) x :=
    (hlog.const_mul (-(1 / 2 : ℝ))).exp
  have hgcomp : HasDerivAt (fun y => g (Real.log y)) (deriv g (Real.log x) * x⁻¹) x :=
    hg.hasDerivAt.comp x hlog
  have hprod := hexp.mul hgcomp
  have hderiv : deriv (halfDensityPullback g) x =
      Real.exp (-(1 / 2 : ℝ) * Real.log x) * (-(1 / 2 : ℝ) * x⁻¹) * g (Real.log x) +
        Real.exp (-(1 / 2 : ℝ) * Real.log x) * (deriv g (Real.log x) * x⁻¹) :=
    hprod.deriv
  dsimp [bkOp, halfDensityPullback]
  rw [hderiv]
  field_simp [ne_of_gt hx]
  ring

/-- Möbius inversion `x ↦ x⁻¹` negates the scaling generator `x d/dx`. -/
theorem scaling_op_inversion_antiparity (f : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hf : DifferentiableAt ℝ f x⁻¹) :
    x * deriv (fun y => f y⁻¹) x = -(x⁻¹ * deriv f x⁻¹) := by
  have hcomp : HasDerivAt (fun y => f y⁻¹) (deriv f x⁻¹ * (-(x ^ 2)⁻¹)) x :=
    hf.hasDerivAt.comp x (hasDerivAt_inv (ne_of_gt hx))
  rw [hcomp.deriv]
  field_simp [ne_of_gt hx]

/-- Arbitrary real power eigenvalue `H(x^s) = (s + 1/2) x^s` on `x > 0`. -/
theorem berry_keating_rpow_eigenvalue (s : ℝ) {x : ℝ} (hx : 0 < x) :
    bkOp (fun y => y ^ s) x = (s + 1 / 2) * x ^ s := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ s) (s * x ^ (s - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have hmul : x * x ^ (s - 1) = x ^ s := by
    calc
      x * x ^ (s - 1) = x ^ (1 : ℝ) * x ^ (s - 1) := by rw [Real.rpow_one]
      _ = x ^ (1 + (s - 1)) := (Real.rpow_add hx 1 (s - 1)).symm
      _ = x ^ s := by ring_nf
  dsimp [bkOp]
  rw [hpow.deriv]
  calc
    x * (s * x ^ (s - 1)) + (1 / 2 : ℝ) * x ^ s
        = s * (x * x ^ (s - 1)) + (1 / 2 : ℝ) * x ^ s := by ring
    _ = s * x ^ s + (1 / 2 : ℝ) * x ^ s := by rw [hmul]
    _ = (s + 1 / 2) * x ^ s := by ring

/-- The critical half-density mode `x^(-1/2)` is in the kernel of the Berry-Keating operator. -/
theorem berry_keating_critical_halfDensity_zero {x : ℝ} (hx : 0 < x) :
    bkOp (fun y => y ^ (-(1 / 2 : ℝ))) x = 0 := by
  rw [berry_keating_rpow_eigenvalue (-(1 / 2 : ℝ)) hx]
  norm_num

/-! ### Differential Split & Noncommutative Matrix Tetraktys Embedding -/

section DifferentialAndMatrixTetraktysSplit

open InfoGeometry.Arithmetic.MajoranaPolyaHilbert
open InfoGeometry.Algebra.NoncommutativeTetraktysFlows

/-- Symmetrized differential split unifying `berry_keating_symmetric_form` and `bkOp`:
`x f'(x) + (x f(x))' = 2 * bkOp f x`. -/
theorem posOp_derivOp_add_derivOp_posOp (f : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) :
    posOp (derivOp f) x + derivOp (posOp f) x = 2 * bkOp f x := by
  have hsym := berry_keating_symmetric_form f x hf
  have h2 : 2 * ((1 / 2 : ℝ) * (x * deriv f x + deriv (posOp f) x)) =
      2 * (x * deriv f x + (1 / 2 : ℝ) * f x) := by
    change 2 * ((1 / 2 : ℝ) * (x * deriv f x + deriv (fun y => y * f y) x)) =
      2 * (x * deriv f x + (1 / 2 : ℝ) * f x)
    rw [hsym]
  dsimp [posOp, derivOp, bkOp]
  linarith

/-- Unification of `bkOp` and `heisenberg_weyl_commutator`:
`2 * derivOp (posOp f) x = 2 * bkOp f x + f x`. -/
theorem two_mul_derivOp_posOp_eq_two_bkOp_add (f : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    2 * derivOp (posOp f) x = 2 * bkOp f x + f x := by
  have hsum := posOp_derivOp_add_derivOp_posOp f x hf
  have hcomm := heisenberg_weyl_commutator f x hf
  linarith

/-- Unification of `bkOp` and `heisenberg_weyl_commutator` on `posOp (derivOp f)`:
`2 * posOp (derivOp f) x = 2 * bkOp f x - f x`. -/
theorem two_mul_posOp_derivOp_eq_two_bkOp_sub (f : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    2 * posOp (derivOp f) x = 2 * bkOp f x - f x := by
  have hsum := posOp_derivOp_add_derivOp_posOp f x hf
  have hcomm := heisenberg_weyl_commutator f x hf
  linarith

section MatrixBridge

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- On arbitrary real `n × n` matrices, `2 • finiteSymmetrizedDilation x p` equals `symDilaton2 x p`. -/
theorem two_smul_finiteSymmetrizedDilation_eq_symDilaton2 (x p : Matrix n n ℝ) :
    (2 : ℝ) • finiteSymmetrizedDilation x p = symDilaton2 x p := by
  dsimp [finiteSymmetrizedDilation, symDilaton2]
  rw [smul_smul]
  norm_num

/-- Matrix product `x * p` splits into the symmetric Berry-Keating dilation and half the commutator. -/
theorem xp_eq_finiteSymmetrizedDilation_add_half_antisymComm (x p : Matrix n n ℝ) :
    x * p = finiteSymmetrizedDilation x p + (1 / 2 : ℝ) • antisymComm x p := by
  dsimp [finiteSymmetrizedDilation, antisymComm]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Reversed matrix product `p * x` splits into `finiteSymmetrizedDilation` minus half the commutator. -/
theorem px_eq_finiteSymmetrizedDilation_sub_half_antisymComm (x p : Matrix n n ℝ) :
    p * x = finiteSymmetrizedDilation x p - (1 / 2 : ℝ) • antisymComm x p := by
  dsimp [finiteSymmetrizedDilation, antisymComm]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- Commutator between `finiteSymmetrizedDilation x p` and `(1 / 2) • antisymComm x p`. -/
theorem lie_finiteSymmetrizedDilation_half_antisymComm (x p : Matrix n n ℝ) :
    ⁅finiteSymmetrizedDilation x p, (1 / 2 : ℝ) • antisymComm x p⁆ =
      (1 / 2 : ℝ) • ⁅p * x, x * p⁆ := by
  have h1 : finiteSymmetrizedDilation x p = (1 / 2 : ℝ) • symDilaton2 x p := rfl
  rw [h1, Ring.lie_def]
  have hlin : ((1 / 2 : ℝ) • symDilaton2 x p) * ((1 / 2 : ℝ) • antisymComm x p) -
      ((1 / 2 : ℝ) • antisymComm x p) * ((1 / 2 : ℝ) • symDilaton2 x p) =
      ((1 / 2 : ℝ) * (1 / 2 : ℝ)) • ⁅symDilaton2 x p, antisymComm x p⁆ := by
    rw [Ring.lie_def]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, smul_sub]
  rw [hlin, lie_symDilaton2_antisymComm]
  have h2 : (2 : Matrix n n ℝ) * ⁅p * x, x * p⁆ = (2 : ℝ) • ⁅p * x, x * p⁆ := by
    rw [two_mul, ← two_smul ℝ]
  rw [h2, smul_smul]
  norm_num

/-- Embedding `(finiteSymmetrizedDilation x p, (1 / 2) • antisymComm x p, cOmega)` into
`NoncommutativeTetraktysFlows.flowGen` and computing its exact Casimir + Lie obstruction square. -/
theorem finiteSymmetrizedDilation_flowGen_square (x p cOmega : Matrix n n ℝ) :
    flowGen (finiteSymmetrizedDilation x p) ((1 / 2 : ℝ) • antisymComm x p) cOmega *
      flowGen (finiteSymmetrizedDilation x p) ((1 / 2 : ℝ) • antisymComm x p) cOmega =
      fiberEmbed (finiteSymmetrizedDilation x p * finiteSymmetrizedDilation x p +
        ((1 / 2 : ℝ) • antisymComm x p) * ((1 / 2 : ℝ) • antisymComm x p) -
        cOmega * cOmega) * 1 +
      fiberEmbed ⁅(1 / 2 : ℝ) • antisymComm x p, cOmega⁆ * gamma1Op +
      fiberEmbed ⁅cOmega, finiteSymmetrizedDilation x p⁆ * sigmaOp -
      fiberEmbed ((1 / 2 : ℝ) • ⁅p * x, x * p⁆) * omegaOp := by
  rw [noncommutative_charpoly_casimir_and_lie_obstruction,
    lie_finiteSymmetrizedDilation_half_antisymComm]

/-- Hyperbolic Mellin focusing on `finiteSymmetrizedDilation` and `(1 / 2) • antisymComm`. -/
theorem finiteSymmetrizedDilation_mellinFocus (u : (Matrix n n ℝ)ˣ) (x p : Matrix n n ℝ) :
    mellinFocus u * (fiberEmbed (finiteSymmetrizedDilation x p) * F_plus) * mellinFocus u⁻¹ =
      fiberEmbed ((u : Matrix n n ℝ) * finiteSymmetrizedDilation x p * (u : Matrix n n ℝ)) *
        F_plus ∧
    mellinFocus u * (fiberEmbed ((1 / 2 : ℝ) • antisymComm x p) * F_minus) * mellinFocus u⁻¹ =
      fiberEmbed ((↑u⁻¹ : Matrix n n ℝ) * ((1 / 2 : ℝ) • antisymComm x p) *
        (↑u⁻¹ : Matrix n n ℝ)) * F_minus ∧
    (fiberEmbed ((u : Matrix n n ℝ) * finiteSymmetrizedDilation x p * (u : Matrix n n ℝ)) *
        F_plus) *
      (fiberEmbed ((↑u⁻¹ : Matrix n n ℝ) * ((1 / 2 : ℝ) • antisymComm x p) *
        (↑u⁻¹ : Matrix n n ℝ)) * F_minus) =
      fiberEmbed ((u : Matrix n n ℝ) * finiteSymmetrizedDilation x p *
        ((1 / 2 : ℝ) • antisymComm x p) * (↑u⁻¹ : Matrix n n ℝ)) * P_plus := by
  have h1 : (u : Matrix n n ℝ) * (↑u⁻¹ : Matrix n n ℝ) = 1 := Units.mul_inv u
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_plus]
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_minus]
  · apply ext_fin2 <;> simp [fiberEmbed, F_plus, F_minus, P_plus]
    have h1' : (u : Matrix n n ℝ) * (u : Matrix n n ℝ)⁻¹ = 1 := by
      rw [← Matrix.coe_units_inv u]
      exact h1
    calc (u : Matrix n n ℝ) * finiteSymmetrizedDilation x p * (u : Matrix n n ℝ) *
          ((u : Matrix n n ℝ)⁻¹ * antisymComm x p * (u : Matrix n n ℝ)⁻¹)
      _ = (u : Matrix n n ℝ) * finiteSymmetrizedDilation x p *
          ((u : Matrix n n ℝ) * (u : Matrix n n ℝ)⁻¹) *
          antisymComm x p * (u : Matrix n n ℝ)⁻¹ := by noncomm_ring
      _ = (u : Matrix n n ℝ) * finiteSymmetrizedDilation x p *
          antisymComm x p * (u : Matrix n n ℝ)⁻¹ := by
          rw [h1']; noncomm_ring

end MatrixBridge

end DifferentialAndMatrixTetraktysSplit

end InfoGeometry.Canonical.BerryKeating
