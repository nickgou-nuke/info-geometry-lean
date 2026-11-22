/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge

/-!
# Noncommutative / R1 Maurer–Cartan Von Mangoldt Bridge

Proves that the classical von Mangoldt arithmetic function `Λ` and the logarithmic
derivative `-ζ'(s)/ζ(s)` are literally an instance of the repository's R1
`LieActionLane` / `MaurerCartanTower` left-logarithmic Maurer–Cartan 1-form:

1. **Logarithmic Dirichlet Derivation (`dirichletLogDerivEnd`)**:
   `(dirichletLogDerivEnd f) n = Real.log n * f n` is an exact `ℝ`-linear Leibniz
   derivation on the Dirichlet convolution algebra `ArithmeticFunction ℝ`:
   `dirichletLogDerivEnd (f * g) = dirichletLogDerivEnd f * g + f * dirichletLogDerivEnd g`.
2. **R1 `LieActionLane` & Flatness (`dirichletLogActionLane`)**:
   The one-generator abelian Lie action `c ↦ c • dirichletLogDerivEnd` satisfies
   `IsLeibnizAction dirichletLogActionLane`, so `actionThetaL` on any unit `g` has
   identically vanishing Chevalley–Eilenberg curvature (`actionCurvature = 0`).
3. **Von Mangoldt = Left Maurer–Cartan 1-Form of the Zeta Unit**:
   With `zetaUnit : (ArithmeticFunction ℝ)ˣ` (`val = ζ`, `inv = μ`),
   `actionThetaL dirichletLogActionLane zetaUnit (fun _ => 1) = Λ`
   (`ArithmeticFunction.vonMangoldt`), and on `1 < s.re` its `LSeries` equals
   `-deriv riemannZeta s / riemannZeta s`.
-/

noncomputable section

namespace InfoGeometry.Canonical.MaurerCartanVonMangoldtBridge

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius LSeries.notation
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge

/-! ## 1. Logarithmic derivation on the Dirichlet convolution algebra -/

/-- Pointwise multiplication by `Real.log n` on `ArithmeticFunction ℝ`. -/
def dirichletLogDeriv (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := Real.log (n : ℝ) * f n
  map_zero' := by simp

@[simp] theorem dirichletLogDeriv_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    dirichletLogDeriv f n = Real.log (n : ℝ) * f n := rfl

/-- `dirichletLogDeriv` as an `ℝ`-linear endomorphism of `ArithmeticFunction ℝ`. -/
def dirichletLogDerivEnd : Module.End ℝ (ArithmeticFunction ℝ) where
  toFun := dirichletLogDeriv
  map_add' f g := by
    ext n
    simp only [dirichletLogDeriv_apply, ArithmeticFunction.add_apply, mul_add]
  map_smul' c f := by
    ext n
    change Real.log (n : ℝ) * (c * f n) = c * (Real.log (n : ℝ) * f n)
    ring

@[simp] theorem dirichletLogDerivEnd_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    dirichletLogDerivEnd f n = Real.log (n : ℝ) * f n := rfl

/-- Exact Leibniz rule for `dirichletLogDerivEnd` under Dirichlet convolution:
`D_ln (f * g) = D_ln f * g + f * D_ln g`. -/
theorem dirichletLogDerivEnd_mul (f g : ArithmeticFunction ℝ) :
    dirichletLogDerivEnd (f * g) =
      dirichletLogDerivEnd f * g + f * dirichletLogDerivEnd g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [dirichletLogDerivEnd_apply, ArithmeticFunction.add_apply,
      ArithmeticFunction.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hmul : d.1 * d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
    have hd1 : (d.1 : ℝ) ≠ 0 := by
      exact_mod_cast (left_ne_zero_of_mul (hmul.symm ▸ hn))
    have hd2 : (d.2 : ℝ) ≠ 0 := by
      exact_mod_cast (right_ne_zero_of_mul (hmul.symm ▸ hn))
    have hlog : Real.log (n : ℝ) = Real.log (d.1 : ℝ) + Real.log (d.2 : ℝ) := by
      rw [← hmul, Nat.cast_mul, Real.log_mul hd1 hd2]
    rw [hlog]
    ring

/-- Acting with `dirichletLogDerivEnd` on `ζ` produces `ArithmeticFunction.log`. -/
theorem dirichletLogDerivEnd_zeta :
    dirichletLogDerivEnd (ζ : ArithmeticFunction ℝ) = ArithmeticFunction.log := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [dirichletLogDerivEnd_apply, ArithmeticFunction.log_apply,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]

/-! ## 2. R1 `LieActionLane` and the Zeta Unit -/

local instance : IsScalarTower ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) where
  smul_assoc c f g := by
    ext n
    change (∑ x ∈ n.divisorsAntidiagonal, (c * f x.1) * g x.2) =
      c * ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

local instance : SMulCommClass ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) where
  smul_comm c f g := by
    ext n
    change c * (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) =
      ∑ x ∈ n.divisorsAntidiagonal, f x.1 * (c * g x.2)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

local instance : LieRing ℝ := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ ℝ := LieAlgebra.ofAssociativeAlgebra
local instance : LieRing (Module.End ℝ (ArithmeticFunction ℝ)) := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ (Module.End ℝ (ArithmeticFunction ℝ)) := LieAlgebra.ofAssociativeAlgebra

/-- One-generator abelian Lie action `c ↦ c • dirichletLogDerivEnd` on
`ArithmeticFunction ℝ`. -/
def dirichletLogActionHom : ℝ →ₗ⁅ℝ⁆ Module.End ℝ (ArithmeticFunction ℝ) where
  toFun c := c • dirichletLogDerivEnd
  map_add' c₁ c₂ := add_smul c₁ c₂ dirichletLogDerivEnd
  map_smul' c₁ c₂ := smul_eq_mul c₁ c₂ ▸ mul_smul c₁ c₂ dirichletLogDerivEnd
  map_lie' {c₁ c₂} := by
    ext f n
    change (c₁ * c₂ - c₂ * c₁) * (Real.log (n : ℝ) * f n) =
      c₁ * (Real.log (n : ℝ) * (c₂ * (Real.log (n : ℝ) * f n))) -
        c₂ * (Real.log (n : ℝ) * (c₁ * (Real.log (n : ℝ) * f n)))
    ring

/-- R1 `LieActionLane ℝ (ArithmeticFunction ℝ)` generated by `D_ln`. -/
abbrev dirichletLogActionLane : LieActionLane ℝ (ArithmeticFunction ℝ) :=
  ⟨ℝ, inferInstance, inferInstance, dirichletLogActionHom⟩

/-- `dirichletLogActionLane` is an exact R1 Leibniz action lane. -/
theorem dirichletLogActionLane_isLeibniz :
    IsLeibnizAction dirichletLogActionLane := by
  intro c f g
  change c • dirichletLogDerivEnd (f * g) =
    (c • dirichletLogDerivEnd f) * g + f * (c • dirichletLogDerivEnd g)
  rw [dirichletLogDerivEnd_mul, smul_add, smul_mul_assoc, mul_smul_comm]

/-- The Dirichlet zeta function `ζ` as a unit in `(ArithmeticFunction ℝ)ˣ`,
with convolution inverse `μ`. -/
def zetaUnit : (ArithmeticFunction ℝ)ˣ where
  val := (ζ : ArithmeticFunction ℝ)
  inv := (μ : ArithmeticFunction ℝ)
  val_inv := ArithmeticFunction.coe_zeta_mul_coe_moebius
  inv_val := ArithmeticFunction.coe_moebius_mul_coe_zeta

/-! ## 3. Von Mangoldt = Left Maurer–Cartan 1-Form of `zetaUnit` -/

/-- **Main Algebraic Identification**: Evaluating R1's left-logarithmic Maurer–Cartan
1-form `actionThetaL dirichletLogActionLane zetaUnit` at the generator `1 : ℝ`
produces `ArithmeticFunction.vonMangoldt` (`Λ`) identically. -/
theorem actionThetaL_zetaUnit_one_eq_vonMangoldt :
    actionThetaL dirichletLogActionLane zetaUnit (fun _ => (1 : ℝ)) =
      ArithmeticFunction.vonMangoldt := by
  rw [actionThetaL_apply]
  change (μ : ArithmeticFunction ℝ) * ((1 : ℝ) • dirichletLogDerivEnd (ζ : ArithmeticFunction ℝ)) =
    ArithmeticFunction.vonMangoldt
  rw [one_smul, dirichletLogDerivEnd_zeta, ← ArithmeticFunction.vonMangoldt_mul_zeta,
    mul_comm (μ : ArithmeticFunction ℝ), mul_assoc,
    ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]

/-- **Maurer–Cartan Flatness**: The left-logarithmic Maurer–Cartan 1-form of `zetaUnit`
has identically vanishing R1 Chevalley–Eilenberg curvature `d θ_L + θ_L ∧ θ_L = 0`. -/
theorem actionThetaL_zetaUnit_flat :
    actionCurvature dirichletLogActionLane
      (actionThetaL dirichletLogActionLane zetaUnit) = 0 :=
  actionThetaL_flat dirichletLogActionLane dirichletLogActionLane_isLeibniz zetaUnit

/-- **Analytic L-Series Readout**: On the convergent half-plane `1 < s.re`, the
`LSeries` of R1's Maurer–Cartan 1-form `actionThetaL dirichletLogActionLane zetaUnit (fun _ => 1)`
equals `-deriv riemannZeta s / riemannZeta s`. -/
theorem LSeries_actionThetaL_zetaUnit_eq_neg_logDeriv_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    L ↗(actionThetaL dirichletLogActionLane zetaUnit (fun _ => (1 : ℝ))) s =
      -deriv riemannZeta s / riemannZeta s := by
  rw [actionThetaL_zetaUnit_one_eq_vonMangoldt]
  exact vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative hs

end InfoGeometry.Canonical.MaurerCartanVonMangoldtBridge
