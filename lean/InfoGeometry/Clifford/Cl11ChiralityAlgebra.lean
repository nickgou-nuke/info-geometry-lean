/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11ChiralityTransport
import Mathlib.Algebra.Algebra.Equiv

/-!
# Real algebra equivalence for global colimit chirality

The existing descended chirality action fixes the scalar embedding. Together
with its existing involutivity, this supplies a native real algebra equivalence
on `Cl11TensorTowerLimit.Limit`. Both directions are the original global
action; no chirality element in the limit is chosen.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11ChiralityAlgebra

open Cl11TensorTowerLimit

/-- Global chirality fixes the real scalars embedded through stage zero. -/
theorem limitChiralityConj_algebraMap (r : ℝ) :
    limitChiralityConj (algebraMap ℝ Limit r) = algebraMap ℝ Limit r := by
  change limitChiralityConj (realAlgebraMap r) = realAlgebraMap r
  rw [realAlgebraMap_stage 0 r, limitChiralityConj_ofStage]
  change ofStage 0 ((1 : Stage 0) * algebraMap ℝ (Stage 0) r * 1) =
    ofStage 0 (algebraMap ℝ (Stage 0) r)
  rw [one_mul, mul_one]

/-- The existing involutive ring action, now with its scalar compatibility. -/
def limitChiralityAlgEquiv : Limit ≃ₐ[ℝ] Limit where
  toFun := limitChiralityConj
  invFun := limitChiralityConj
  left_inv := limitChiralityConj_involutive
  right_inv := limitChiralityConj_involutive
  map_mul' := limitChiralityConj.map_mul
  map_add' := limitChiralityConj.map_add
  commutes' := limitChiralityConj_algebraMap

@[simp] theorem limitChiralityAlgEquiv_apply (X : Limit) :
    limitChiralityAlgEquiv X = limitChiralityConj X := rfl

end InfoGeometry.Clifford.Cl11ChiralityAlgebra
