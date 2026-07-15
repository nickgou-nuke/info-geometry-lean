import InfoGeometry.Canonical.AlgebraicStateFunctionalBridge
import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.SpecialFunctions.Exponential

open scoped InnerProductSpace

namespace AlgebraicStateLorentzAction

open AlgebraicStateFunctionalBridge
open Cl11LorentzAction
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Quantum
open InfoGeometry.Krein

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "IdH" => ContinuousLinearMap.id ℝ (DoubledSpace H)
local notation "EndH" => DoubledSpace H →L[ℝ] DoubledSpace H

/--
Dual action of the modular Lorentz boost on the algebraic state space.

The state transforms by the pullback of the inverse modular adjoint flow:
`ω_t(A) = ω(Ad_{-t} A)`.
-/
@[rep_depth transport]
noncomputable def modularAdjointStateFlow
    (X : RealSplitCl11Action (DoubledSpace H)) (t : ℝ)
    (ω : PositiveNormalizedFunctional H) : PositiveNormalizedFunctional H where
  probe := {
    toFun := fun (A : EndH) => ω.probe (modularAdjointFlow X (-t) A)
    map_add' := by
      intro A B
      change ω.probe (modularAdjointFlow X (-t) (A + B)) =
        ω.probe (modularAdjointFlow X (-t) A) + ω.probe (modularAdjointFlow X (-t) B)
      unfold modularAdjointFlow
      have h : modularFlow X (-t) * (A + B) * modularFlow X (- -t) =
          modularFlow X (-t) * A * modularFlow X (- -t) + modularFlow X (-t) * B * modularFlow X (- -t) := by
        simp [mul_add, add_mul]
      rw [h]
      exact LinearMap.map_add ω.probe _ _
    map_smul' := by
      intro c A
      change ω.probe (modularAdjointFlow X (-t) (c • A)) = c • ω.probe (modularAdjointFlow X (-t) A)
      unfold modularAdjointFlow
      have h : modularFlow X (-t) * (c • A) * modularFlow X (- -t) =
          c • (modularFlow X (-t) * A * modularFlow X (- -t)) := by
        simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      rw [h]
      exact LinearMap.map_smul ω.probe c _
  }
  normalized := by
    change ω.probe (modularAdjointFlow X (-t) 1) = 1
    unfold modularAdjointFlow
    have h : modularFlow X (-t) * 1 * modularFlow X (- -t) = 1 := by
      calc
        modularFlow X (-t) * 1 * modularFlow X (- -t)
          = modularFlow X (-t) * modularFlow X (- -t) := by simp
        _ = 1 := by
          simp only [neg_neg]
          rw [modularFlow_neg_mul_modularFlow]
    rw [h]
    exact ω.normalized

end Core

section TransportLaws

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "IdH" => ContinuousLinearMap.id ℝ (DoubledSpace H)
local notation "EndH" => DoubledSpace H →L[ℝ] DoubledSpace H

theorem PositiveNormalizedFunctional.ext
    (ω₁ ω₂ : PositiveNormalizedFunctional H) (h : ω₁.probe = ω₂.probe) : ω₁ = ω₂ := by
  cases ω₁
  cases ω₂
  congr

/-- Additive/group law for state transport: `ω_{s+t} = (ω_t)_s`. -/
@[rep_depth transport]
theorem modularAdjointStateFlow_add
    (X : RealSplitCl11Action (DoubledSpace H)) (s t : ℝ)
    (ω : PositiveNormalizedFunctional H) :
    modularAdjointStateFlow X (s + t) ω =
      modularAdjointStateFlow X s (modularAdjointStateFlow X t ω) := by
  apply PositiveNormalizedFunctional.ext
  apply LinearMap.ext
  intro A
  change ω.probe (modularAdjointFlow X (-(s + t)) A) =
    ω.probe (modularAdjointFlow X (-t) (modularAdjointFlow X (-s) A))
  have h_neg : -(s + t) = (-t) + (-s) := by ring
  rw [h_neg]
  rw [modularAdjointFlow_add X (-t) (-s) A]

/-- Adjoint state transport scales the `uPlus` channel by `exp(-2t)`. -/
@[rep_depth transport]
theorem modularAdjointStateFlow_uPlus
    (X : RealSplitCl11Action (DoubledSpace H)) (t : ℝ)
    (ω : PositiveNormalizedFunctional H) (A : EndH) :
    (modularAdjointStateFlow X t ω).probe (uPlus X A) =
      Real.exp (-2 * t) * ω.probe (uPlus X A) := by
  change ω.probe (modularAdjointFlow X (-t) (uPlus X A)) =
    Real.exp (-2 * t) * ω.probe (uPlus X A)
  rw [modularAdjointFlow_scales_uPlus X (-t) A]
  have h_eq : 2 * -t = -2 * t := by ring
  rw [h_eq]
  have h_smul : ω.probe (Real.exp (-2 * t) • uPlus X A) =
      Real.exp (-2 * t) * ω.probe (uPlus X A) := by
    exact LinearMap.map_smul ω.probe (Real.exp (-2 * t)) (uPlus X A)
  rw [h_smul]

/-- Adjoint state transport scales the `uMinus` channel by `exp(2t)`. -/
@[rep_depth transport]
theorem modularAdjointStateFlow_uMinus
    (X : RealSplitCl11Action (DoubledSpace H)) (t : ℝ)
    (ω : PositiveNormalizedFunctional H) (A : EndH) :
    (modularAdjointStateFlow X t ω).probe (uMinus X A) =
      Real.exp (2 * t) * ω.probe (uMinus X A) := by
  change ω.probe (modularAdjointFlow X (-t) (uMinus X A)) =
    Real.exp (2 * t) * ω.probe (uMinus X A)
  rw [modularAdjointFlow_scales_uMinus X (-t) A]
  have h_eq : -2 * -t = 2 * t := by ring
  rw [h_eq]
  have h_smul : ω.probe (Real.exp (2 * t) • uMinus X A) =
      Real.exp (2 * t) * ω.probe (uMinus X A) := by
    exact LinearMap.map_smul ω.probe (Real.exp (2 * t)) (uMinus X A)
  rw [h_smul]

/-- Adjoint state transport fixes the grade-zero channel. -/
@[rep_depth transport]
theorem modularAdjointStateFlow_gZeroPart
    (X : RealSplitCl11Action (DoubledSpace H)) (t : ℝ)
    (ω : PositiveNormalizedFunctional H) (A : EndH) :
    (modularAdjointStateFlow X t ω).probe (gZeroPart X A) =
      ω.probe (gZeroPart X A) := by
  change ω.probe (modularAdjointFlow X (-t) (gZeroPart X A)) =
    ω.probe (gZeroPart X A)
  rw [modularAdjointFlow_fixes_gZeroPart X (-t) A]

end TransportLaws

end AlgebraicStateLorentzAction
