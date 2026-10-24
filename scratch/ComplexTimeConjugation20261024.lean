/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteExponentialMotion
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition

/-! Complex-time extension on an existing C⋆ algebra.
Uncompiled sandbox. The positive real-time convention is exp(i t G).
This module constructs no state and asserts no scalar KMS boundary or strip bound.
-/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.ComplexTimeConjugation

open InfoGeometry.Canonical.ModularFlowExponentialGenerator

variable {A : Type*} [CStarAlgebra A]

/-- Complex-time conjugation on the same algebra, with positive real-time sign. -/
def alpha (G : A) (z : ℂ) (x : A) : A :=
  NormedSpace.exp ((z * Complex.I) • G) * x *
    NormedSpace.exp (-((z * Complex.I) • G))

/-- Every observable has an entire orbit for this bounded algebra element. -/
theorem alpha_analyticAt (G x : A) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => alpha G w x) z := by
  have harg : AnalyticAt ℂ (fun w : ℂ => (w * Complex.I) • G) z :=
    (analyticAt_id.mul analyticAt_const).smul analyticAt_const
  have hp : AnalyticAt ℂ
      (fun w : ℂ => NormedSpace.exp ((w * Complex.I) • G)) z := by
    simpa only [Function.comp_def] using
      (NormedSpace.exp_analytic (𝕂 := ℂ) ((z * Complex.I) • G)).comp harg
  have hn : AnalyticAt ℂ
      (fun w : ℂ => NormedSpace.exp (-((w * Complex.I) • G))) z := by
    simpa only [Function.comp_def] using
      (NormedSpace.exp_analytic (𝕂 := ℂ) (-((z * Complex.I) • G))).comp harg.neg
  exact (hp.mul analyticAt_const).mul hn

/-- Real-axis readback is the existing real-domain exponential path. -/
theorem alpha_ofReal (G x : A) (t : ℝ) :
    alpha G (t : ℂ) x = complexExponentialConjugationPath G x t := by
  have ht : (((t : ℂ) * Complex.I) • G) = t • (Complex.I • G) := by
    rw [mul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  unfold alpha complexExponentialConjugationPath
  rw [ht]

/-- For a self-adjoint generator the real restriction is native unitary conjugation. -/
theorem alpha_ofReal_eq_unitary (G : selfAdjoint A) (x : A) (t : ℝ) :
    alpha (G : A) (t : ℂ) x =
      Unitary.conjStarAlgAut (S := ℂ) (R := A)
        (selfAdjoint.expUnitary (t • G)) x := by
  exact (alpha_ofReal (G : A) x t).trans
    (InfoGeometry.OperatorAlgebra.expUnitary_conjugation_eq_complexPath G x t).symm

/-- Exponentials of time-scaled copies of one generator compose. -/
theorem exp_time_add (G : A) (z w : ℂ) :
    NormedSpace.exp (((z + w) * Complex.I) • G) =
      NormedSpace.exp ((z * Complex.I) • G) *
        NormedSpace.exp ((w * Complex.I) • G) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  rw [add_mul, add_smul]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl G).smul_left (z * Complex.I)).smul_right (w * Complex.I))

/-- Complex-time addition acts by composition on every observable. -/
theorem alpha_add (G x : A) (z w : ℂ) :
    alpha G (z + w) x = alpha G z (alpha G w x) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  have hn : NormedSpace.exp (-(((z + w) * Complex.I) • G)) =
      NormedSpace.exp (-((w * Complex.I) • G)) *
        NormedSpace.exp (-((z * Complex.I) • G)) := by
    have he : -(((z + w) * Complex.I) • G) =
        -((w * Complex.I) • G) + -((z * Complex.I) • G) := by
      simp only [add_mul, add_smul, neg_add]
      exact add_comm _ _
    rw [he]
    exact NormedSpace.exp_add_of_commute
      ((((Commute.refl G).smul_left (w * Complex.I)).smul_right
        (z * Complex.I)).neg_left.neg_right)
  simp only [alpha, exp_time_add, hn, mul_assoc]

/-- The positive imaginary shift yields the negative-temperature exponential first. -/
theorem alpha_imaginary (G x : A) (β : ℝ) :
    alpha G (Complex.I * (β : ℂ)) x =
      NormedSpace.exp ((-β) • G) * x * NormedSpace.exp (β • G) := by
  have hs : ((Complex.I * (β : ℂ)) * Complex.I) = -(β : ℂ) := by
    calc
      _ = (β : ℂ) * (Complex.I * Complex.I) := by ring
      _ = -(β : ℂ) := by rw [Complex.I_mul_I, mul_neg_one]
  have hg : (((Complex.I * (β : ℂ)) * Complex.I) • G) = (-β) • G := by
    rw [hs, neg_smul, neg_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [alpha, hg, neg_smul, neg_neg]

/-- The whole shifted orbit is the same imaginary conjugation of the unshifted one. -/
theorem alpha_add_imaginary (G x : A) (z : ℂ) (β : ℝ) :
    alpha G (z + Complex.I * (β : ℂ)) x =
      NormedSpace.exp ((-β) • G) * alpha G z x * NormedSpace.exp (β • G) := by
  rw [add_comm z (Complex.I * (β : ℂ)), alpha_add, alpha_imaginary]

end InfoGeometry.OperatorAlgebra.ComplexTimeConjugation
