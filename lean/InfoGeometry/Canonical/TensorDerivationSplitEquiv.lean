/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorTangentLieSplitting

/-! # Linear splitting of the colimit derivation algebra

The cut stabilizer and the canonical inner tangent lift form a direct sum as
real vector spaces. The result makes no claim of a product Lie algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorDerivationSplitEquiv

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Canonical.TensorTangentLieSplitting

/-- Add a stabilizing derivation and a canonically lifted tangent direction. -/
def splitSum (P : Limit) :
    (limitCutStabilizer P).toSubmodule × idempotentTangent P →ₗ[ℝ] LimitDeriv :=
  (limitCutStabilizer P).toSubmodule.subtype.coprod (tangentLift P)

/-- The two summands have unique coordinates. -/
theorem splitSum_injective (P : Limit) (hP : P * P = P) :
    Function.Injective (splitSum P) := by
  rintro ⟨S, T⟩ ⟨S', T'⟩ h
  change S.1 + tangentLift P T = S'.1 + tangentLift P T' at h
  have he := congrArg (cutEvaluation P) h
  rw [map_add, map_add, cutEvaluation_tangentLift P hP T,
    cutEvaluation_tangentLift P hP T'] at he
  have hS : cutEvaluation P S.1 = 0 := S.2
  have hS' : cutEvaluation P S'.1 = 0 := S'.2
  rw [hS, hS', zero_add, zero_add] at he
  have hT : T = T' := Subtype.ext he
  subst T'
  have hSS : S.1 = S'.1 := add_right_cancel h
  exact Prod.ext (Subtype.ext hSS) rfl

/-- The canonical tangent lift and the stabilizer span all derivations. -/
theorem splitSum_surjective (P : Limit) (hP : P * P = P) :
    Function.Surjective (splitSum P) := by
  intro D
  obtain ⟨S, T, hS, hD⟩ := derivation_eq_stabilizer_add_tangentLift P hP D
  refine ⟨(⟨S, hS⟩, T), ?_⟩
  exact hD.symm

/-- Every derivation has unique stabilizer and tangent coordinates. -/
def derivationSplitEquiv (P : Limit) (hP : P * P = P) :
    ((limitCutStabilizer P).toSubmodule × idempotentTangent P) ≃ₗ[ℝ] LimitDeriv :=
  LinearEquiv.ofBijective (splitSum P) ⟨splitSum_injective P hP, splitSum_surjective P hP⟩

end InfoGeometry.Canonical.TensorDerivationSplitEquiv

end
