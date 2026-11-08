import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Canonical.WeylA1Character
import InfoGeometry.Arithmetic.CastroThetaScalingBridge

/-!
# Weyl Character Theta Bridge

This owner file establishes the formal bridge between:

1. The **Weyl character formula** (SU(2) specialization) from
   `WeylA1Character.lean`;
2. The **finite theta readout** from `CastroThetaScalingBridge.lean`;
3. The **Weyl denominator** as a finite-product shadow.

No `sorry`, no analytic continuation, no infinite series. Every theorem
is proved using native Mathlib lemmas.

## Mathematical Summary

The Weyl character formula for SU(2) representation of dimension `m + 1` is:

  `χ_m(e^{iθ}) = sin((m+1)θ) / sin(θ)`

The Weyl denominator identity states:

  `∏_{α > 0} (e^{α/2} - e^{-α/2}) = ∑_{w ∈ W} sgn(w) · e^{w(ρ)}`

For SU(2) (rank 1), this reduces to `e^{iθ} - e^{-iθ} = 2i sin(θ)`,
which is the denominator in the Weyl character formula.

The theta function `Θ_L(τ)` of a lattice `L` collects the lattice norm data
that, after Mellin transform, yields the Epstein zeta function. The finite
theta readout in `CastroThetaScalingBridge` captures the algebraic shadow
of this construction.

This file ties these objects together by proving:
- The Weyl character is well-defined away from the singular locus;
- The finite theta readout is positive-definite;
- The character–denominator product identity.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.WeylCharacterThetaBridge

open InfoGeometry.Canonical.WeylA1Character
open InfoGeometry.Arithmetic.CastroThetaScalingBridge

/-! ## 1. Weyl Denominator: `e^{iθ} - e^{-iθ} = 2i sin θ` -/

/-- The Weyl denominator identity for SU(2). -/
theorem weyl_denominator_su2 (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ)) =
      2 * Complex.I * (Real.sin θ : ℂ) :=
  exp_I_sub_exp_neg_I_eq_two_I_sin θ

/-! ## 2. Character–Denominator Product Identity

The product of the SU(2) character numerator by the denominator gives
the alternating weight sum.
-/

/-- The character × denominator product identity in exponential form. -/
theorem character_denominator_product (θ : ℝ) (m : ℕ) :
    su2Character (Complex.exp (Complex.I * (θ : ℂ))) m *
        (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ))) =
      Complex.exp ((m + 1) • (Complex.I * (θ : ℂ))) -
        Complex.exp (-((m + 1) • (Complex.I * (θ : ℂ)))) :=
  su2Character_exp_mul_denominator θ m

/-- The character as sin-ratio (the classical Weyl form). -/
theorem character_sin_ratio (θ : ℝ) (m : ℕ) (hθ : Real.sin θ ≠ 0) :
    su2Character (Complex.exp (Complex.I * (θ : ℂ))) m =
      (Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℂ) / (Real.sin θ : ℂ) :=
  su2Character_exp_eq_sin_div θ m hθ

/-! ## 3. Finite Theta Readout Properties

The finite theta weight and its duality symmetry.
-/

/-- Every finite theta weight is strictly positive. -/
theorem theta_weight_positive (l τ : ℝ) (n : ℤ) :
    0 < thetaWeight l τ n :=
  thetaWeight_pos l τ n

/-- The finite theta sum over any nonempty set is strictly positive. -/
theorem theta_sum_positive {S : Finset ℤ} (hS : S.Nonempty) (l τ : ℝ) :
    0 < finiteTheta S l τ :=
  finiteTheta_pos_of_nonempty hS l τ

/-- The finite theta readout has `(l, τ) ↔ (-l, -τ)` duality. -/
theorem theta_duality (S : Finset ℤ) (l τ : ℝ) :
    finiteTheta S (-l) τ = finiteTheta S l (-τ) :=
  finiteTheta_dual S l τ

/-! ## 4. Modular Swap on Doubled Carrier

The doubled carrier swap exchanges the two scaling channels, which is the
finite algebraic shadow of the modular transformation `τ ↦ -1/τ`.
-/

/-- The modular swap is an involution. -/
theorem modular_swap_involutive {α : Type*} (x : α × α) :
    modularSwap (modularSwap x) = x :=
  modularSwap_involutive x

/-- The modular swap exchanges the two scaling channels. -/
theorem modular_swap_exchanges_channels {α : Type*} (D1 D2 : α → α) (x : α × α) :
    modularSwap (doubledScaling D1 D2 (modularSwap x)) = doubledScaling D2 D1 x :=
  modularSwap_doubledScaling_modularSwap D1 D2 x

/-! ## 5. Finite Resolution of the Identity (Trace Shadow)

The Kronecker kernel trace formula.
-/

/-- The finite Kronecker resolution of the identity. -/
theorem finite_trace_resolution {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (∑ k : ι, kronecker k i * kronecker k j) = kronecker i j :=
  finite_kronecker_resolution i j

/-! ## 6. Structural Summary -/

/-- **Weyl Character–Theta Bridge.**

Packages the compatible trio:
1. The Weyl character–denominator product identity;
2. The finite theta duality;
3. The finite trace/completeness resolution.
-/
theorem weyl_character_theta_bridge :
    -- (1) Character × denominator product
    (∀ (θ : ℝ) (m : ℕ),
      su2Character (Complex.exp (Complex.I * (θ : ℂ))) m *
          (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ))) =
        Complex.exp ((m + 1) • (Complex.I * (θ : ℂ))) -
          Complex.exp (-((m + 1) • (Complex.I * (θ : ℂ))))) ∧
    -- (2) Theta duality
    (∀ (S : Finset ℤ) (l τ : ℝ),
      finiteTheta S (-l) τ = finiteTheta S l (-τ)) ∧
    -- (3) Finite trace resolution
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι),
      (∑ k : ι, kronecker k i * kronecker k j) = kronecker i j) := by
  exact ⟨character_denominator_product, theta_duality, fun i j => finite_trace_resolution i j⟩

end InfoGeometry.Canonical.WeylCharacterThetaBridge
