/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
import InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

/-!
# InfoGeometry.Arithmetic.MaurerCartanVonMangoldtBridge

Establishes the exact gauge-geometric identification inside `InfoGeometry`:

1. Pointwise multiplication by `Real.log n` (`logDerivationEnd`) is an exact
   Leibniz derivation on the Dirichlet convolution ring `ArithmeticFunction ℝ`
   (`logDerivationEnd_leibniz`, `isLeibniz_logDerivationEnd`).
2. `dirichletLogLane : LieActionLane ℝ (ArithmeticFunction ℝ)` packages `c ↦ c • logDerivationEnd`
   into the repository's R1 Chevalley–Eilenberg / Maurer–Cartan framework
   (`MaurerCartanTower`) satisfying `IsLeibnizAction dirichletLogLane`.
3. `zetaUnit : (ArithmeticFunction ℝ)ˣ` wraps `(ζ, μ)` (`coe_zeta_mul_coe_moebius`),
   and its canonical R1 left-logarithmic Maurer–Cartan 1-form
   `actionThetaL dirichletLogLane zetaUnit` evaluated at `![(1 : ℝ)]` is identically
   the von Mangoldt function `Λ = μ * log`, is flat under the Chevalley–Eilenberg
   curvature (`actionCurvature = 0`), has `LSeries` equal to
   `actualRiemannZetaLogDerivative s = -deriv riemannZeta s / riemannZeta s` on
   `1 < s.re`, and satisfies divisor summation back to `logCoefficients n`.
-/

noncomputable section

open ArithmeticFunction
open scoped LSeries.notation BigOperators

namespace InfoGeometry.Arithmetic.MaurerCartanVonMangoldtBridge

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
open InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
open InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Multiplication by `Real.log n` as an `ℝ`-linear endomorphism of `ArithmeticFunction ℝ`. -/
def logDerivationEnd : Module.End ℝ (ArithmeticFunction ℝ) where
  toFun f := f.pmul ArithmeticFunction.log
  map_add' f g := by
    ext n
    simp [ArithmeticFunction.pmul_apply, add_mul]
  map_smul' c f := by
    ext n
    simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.smul_map,
      RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem logDerivationEnd_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    logDerivationEnd f n = f n * Real.log n :=
  rfl

/-- Applying `logDerivationEnd` to `ζ` produces `ArithmeticFunction.log`. -/
@[simp] theorem logDerivationEnd_zeta :
    logDerivationEnd (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = ArithmeticFunction.log :=
  ArithmeticFunction.zeta_pmul ArithmeticFunction.log

/-- `logDerivationEnd` satisfies the exact Leibniz product rule on the Dirichlet
convolution ring `ArithmeticFunction ℝ`. -/
theorem logDerivationEnd_leibniz (f g : ArithmeticFunction ℝ) :
    logDerivationEnd (f * g) = logDerivationEnd f * g + f * logDerivationEnd g := by
  ext n
  simp only [logDerivationEnd_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hmul : (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) * Real.log (n : ℝ) =
        ∑ x ∈ n.divisorsAntidiagonal, (f x.1 * g x.2) * Real.log (n : ℝ) :=
      Finset.sum_mul _ _ _
    rw [hmul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rcases Nat.mem_divisorsAntidiagonal.mp hx with ⟨hprod, _⟩
    have hx1 : x.1 ≠ 0 := left_ne_zero_of_mul (hprod ▸ hn)
    have hx2 : x.2 ≠ 0 := right_ne_zero_of_mul (hprod ▸ hn)
    have hlog : Real.log (n : ℝ) = Real.log (x.1 : ℝ) + Real.log (x.2 : ℝ) := by
      rw [← hprod, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hx1) (Nat.cast_ne_zero.mpr hx2)]
    rw [hlog]
    ring

/-- Bundled `NonAssocDerivation.IsLeibniz` witness for `logDerivationEnd`. -/
theorem isLeibniz_logDerivationEnd :
    NonAssocDerivation.IsLeibniz ℝ (ArithmeticFunction ℝ) logDerivationEnd :=
  logDerivationEnd_leibniz

/-- 1D abelian Lie homomorphism `ℝ →ₗ⁅ℝ⁆ Module.End ℝ (ArithmeticFunction ℝ)` sending
`c ↦ c • logDerivationEnd`. -/
def dirichletLogLieHom : ℝ →ₗ⁅ℝ⁆ Module.End ℝ (ArithmeticFunction ℝ) where
  toFun c := c • logDerivationEnd
  map_add' c₁ c₂ := add_smul c₁ c₂ logDerivationEnd
  map_smul' r c := by
    simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
  map_lie' {c₁ c₂} := by
    simp only [LieRing.of_associative_ring_bracket, mul_comm c₁ c₂, sub_self, zero_smul]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c₁ c₂, sub_self]

local instance : IsScalarTower ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) :=
  ⟨fun r f g => by
    ext n
    simp [ArithmeticFunction.mul_apply, Finset.mul_sum]⟩

local instance : SMulCommClass ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) :=
  ⟨fun r f g => by
    ext n
    simp [ArithmeticFunction.mul_apply, Finset.mul_sum]⟩

/-- The `LieActionLane ℝ (ArithmeticFunction ℝ)` generated by the scale derivation `logDerivationEnd`. -/
abbrev dirichletLogLane : LieActionLane ℝ (ArithmeticFunction ℝ) :=
  ⟨ℝ, inferInstance, inferInstance, dirichletLogLieHom⟩

/-- Every generator in `dirichletLogLane` acts by a Leibniz derivation. -/
theorem isLeibnizAction_dirichletLogLane : IsLeibnizAction dirichletLogLane := by
  intro c f g
  change (c • logDerivationEnd) (f * g) = (c • logDerivationEnd) f * g + f * (c • logDerivationEnd) g
  simp only [LinearMap.smul_apply, logDerivationEnd_leibniz, smul_add, smul_mul_assoc, mul_smul_comm]

/-- The arithmetic Zeta element `(ζ : ArithmeticFunction ℝ)` bundled as a unit in the
Dirichlet convolution ring with inverse `μ`. -/
def zetaUnit : (ArithmeticFunction ℝ)ˣ where
  val := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  inv := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  val_inv := ArithmeticFunction.coe_zeta_mul_coe_moebius
  inv_val := ArithmeticFunction.coe_moebius_mul_coe_zeta

@[simp] theorem zetaUnit_val :
    (zetaUnit : ArithmeticFunction ℝ) = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) :=
  rfl

@[simp] theorem zetaUnit_inv_val :
    ((zetaUnit⁻¹ : (ArithmeticFunction ℝ)ˣ) : ArithmeticFunction ℝ) =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) :=
  rfl

/-- Evaluating the R1 left-logarithmic Maurer–Cartan 1-form `actionThetaL` of `zetaUnit`
at any direction `c : ℝ` gives `c • Λ`. -/
theorem actionThetaL_zetaUnit_apply (c : ℝ) :
    actionThetaL dirichletLogLane zetaUnit ![c] = c • ArithmeticFunction.vonMangoldt := by
  rw [actionThetaL_apply]
  change (↑zetaUnit⁻¹ : ArithmeticFunction ℝ) * (c • logDerivationEnd) (zetaUnit : ArithmeticFunction ℝ) = _
  simp only [LinearMap.smul_apply, zetaUnit_val, zetaUnit_inv_val,
    logDerivationEnd_zeta, mul_smul_comm, ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]

/-- At unit scale `c = 1`, the R1 Maurer–Cartan 1-form of `zetaUnit` is identically the
von Mangoldt arithmetic function `Λ`. -/
theorem actionThetaL_zetaUnit_one_eq_vonMangoldt :
    actionThetaL dirichletLogLane zetaUnit ![(1 : ℝ)] = ArithmeticFunction.vonMangoldt := by
  simpa using actionThetaL_zetaUnit_apply 1

/-- Unconditional Chevalley–Eilenberg 2-form flatness `d θ_L + θ_L ∧ θ_L = 0` of the
zeta Maurer–Cartan 1-form in `dirichletLogLane`. -/
theorem actionThetaL_zetaUnit_flat :
    actionCurvature dirichletLogLane (actionThetaL dirichletLogLane zetaUnit) = 0 :=
  actionThetaL_flat dirichletLogLane isLeibnizAction_dirichletLogLane zetaUnit

/-- Unified R1 Maurer–Cartan ↔ Analytic Zeta ↔ Möbius inversion theorem:
on the convergent half-plane `1 < s.re`, the Dirichlet series of the unit Maurer–Cartan
1-form `actionThetaL dirichletLogLane zetaUnit ![(1 : ℝ)]` equals `-deriv riemannZeta s / riemannZeta s`,
its ambient CE curvature vanishes, `ζ(s) * L(μ, s) = 1`, and divisor summation recovers
`logCoefficients n`. -/
theorem maurerCartan_zetaLogDerivative_mobius_synthesis
    {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    L ↗(actionThetaL dirichletLogLane zetaUnit ![(1 : ℝ)]) s = actualRiemannZetaLogDerivative s ∧
    L ↗(actionThetaL dirichletLogLane zetaUnit ![(1 : ℝ)]) s = -deriv riemannZeta s / riemannZeta s ∧
    actionCurvature dirichletLogLane (actionThetaL dirichletLogLane zetaUnit) = 0 ∧
    riemannZeta s * L ↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) s = 1 ∧
    (∑ d ∈ n.divisors, actionThetaL dirichletLogLane zetaUnit ![(1 : ℝ)] d) = logCoefficients n := by
  rw [actionThetaL_zetaUnit_one_eq_vonMangoldt]
  exact ⟨vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative hs,
    vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative hs,
    actionThetaL_zetaUnit_flat,
    actualRiemannZeta_mul_mobius_LSeries_eq_one hs,
    (one_convolution_vonMangoldt_eq_log n).symm⟩

end InfoGeometry.Arithmetic.MaurerCartanVonMangoldtBridge
