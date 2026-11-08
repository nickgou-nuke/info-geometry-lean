/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorTangentLieSplitting

/-! # Stabilizer action on the idempotent tangent module

Cut-stabilizing derivations preserve the tangent equation. Their action is
compatible with the canonical inner-derivation lift, giving the mixed bracket
part of the reductive decomposition without a quotient Lie algebra claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorTangentStabilizerAction

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Canonical.TensorTangentLieSplitting

attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000

/-- A stabilizing derivation maps every idempotent tangent vector to another
idempotent tangent vector. -/
theorem stabilizer_preserves_tangent (P : Limit) (S : LimitDeriv)
    (hS : S ∈ limitCutStabilizer P) (T : idempotentTangent P) :
    S.1 T.1 ∈ idempotentTangent P := by
  change S.1 P = 0 at hS
  have h := congrArg S.1 T.2
  rw [map_add, S.property P T.1, S.property T.1 P, hS] at h
  simp only [zero_mul, mul_zero, zero_add, add_zero] at h
  exact h

/-- Each stabilizing derivation acts as a real-linear endomorphism on the
actual tangent submodule. -/
def stabilizerTangentAction (P : Limit) (S : limitCutStabilizer P) :
    idempotentTangent P →ₗ[ℝ] idempotentTangent P where
  toFun T := ⟨S.1.1 T.1, stabilizer_preserves_tangent P S.1 S.2 T⟩
  map_add' T U := by
    apply Subtype.ext
    exact map_add S.1.1 T.1 U.1
  map_smul' r T := by
    apply Subtype.ext
    exact map_smul S.1.1 r T.1

/-- The stabilizer acts on the tangent module by a native Lie algebra
homomorphism into its linear endomorphisms. -/
def stabilizerTangentLieHom (P : Limit) :
    limitCutStabilizer P →ₗ⁅ℝ⁆ Module.End ℝ (idempotentTangent P) where
  toFun := stabilizerTangentAction P
  map_add' S R := by
    ext T
    rfl
  map_smul' r S := by
    ext T
    rfl
  map_lie' := by
    intro S R
    ext T
    rfl

/-- The canonical lift intertwines the stabilizer action with the Lie
bracket of Leibniz derivations. -/
theorem tangentLift_stabilizer_equivariant (P : Limit) (S : limitCutStabilizer P)
    (T : idempotentTangent P) :
    ⁅S.1, tangentLift P T⁆ = tangentLift P (stabilizerTangentAction P S T) := by
  have hS : S.1.1 P = 0 := S.2
  apply Subtype.ext
  ext Z
  change S.1.1 ((T.1 * P - P * T.1) * Z - Z * (T.1 * P - P * T.1)) -
      ((T.1 * P - P * T.1) * S.1.1 Z - S.1.1 Z * (T.1 * P - P * T.1)) =
    (S.1.1 T.1 * P - P * S.1.1 T.1) * Z -
      Z * (S.1.1 T.1 * P - P * S.1.1 T.1)
  rw [map_sub, S.1.property, S.1.property, map_sub]
  simp only [S.1.property T.1 P, S.1.property P T.1, hS,
    zero_mul, mul_zero, add_zero, zero_add]
  noncomm_ring

end InfoGeometry.Canonical.TensorTangentStabilizerAction

end
