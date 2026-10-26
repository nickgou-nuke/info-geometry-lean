/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CyclicQuotient
import InfoGeometry.Core.CornerCentrality
import InfoGeometry.Physics.NuclearConfigurationOperatorLift

/-!
# The actual nuclear corner map on additive cyclic quotients

The lift preserves commutators without preserving the full unit. Its induced
quotient map is not asserted injective. A scalar lifts to a multiple of P;
centrality within the corner does not imply ambient centrality.
-/

noncomputable section
namespace InfoGeometry.Physics.NuclearCornerCyclicBridge

open InfoGeometry.Algebra.CyclicQuotient
open InfoGeometry.Core.CornerCentrality
open InfoGeometry.Physics.NuclearConfigurationOperatorLift
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

local notation "M2" => InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- The existing lift packaged as the native nonunital ring homomorphism. -/
def cornerNonUnitalHom : M2 →ₙ+* Operator where
  toFun := cornerLift
  map_zero' := map_zero cornerLift
  map_add' := map_add cornerLift
  map_mul' := cornerLift_mul

def cornerCyclicMap : CyclicModule ℤ M2 →ₗ[ℤ] CyclicModule ℤ Operator :=
  InfoGeometry.Algebra.CyclicQuotient.map cornerNonUnitalHom

@[simp] theorem cornerCyclicMap_class (O : M2) :
    cornerCyclicMap (cyclicClass ℤ M2 O) = cyclicClass ℤ Operator (cornerLift O) := rfl

theorem cornerCyclicMap_unique
    (f : CyclicModule ℤ M2 →ₗ[ℤ] CyclicModule ℤ Operator)
    (hf : ∀ O, f (cyclicClass ℤ M2 O) = cyclicClass ℤ Operator (cornerLift O)) :
    f = cornerCyclicMap := map_unique cornerNonUnitalHom f hf

@[simp] theorem cornerLift_scalar (r : ℝ) :
    cornerLift (r • (1 : M2)) = r • modelProjection := by
  rw [map_smul, cornerLift_one]

theorem lifted_scalar_central_in_corner (r : ℝ) (X : Operator) :
    cornerLift (r • (1 : M2)) * (modelProjection * X * modelProjection) =
      (modelProjection * X * modelProjection) * cornerLift (r • (1 : M2)) := by
  rw [cornerLift_scalar]
  exact scalar_central_in_corner r _ X modelProjection_idempotent

theorem lifted_scalar_commutator (r : ℝ) (X : Operator) :
    cornerLift (r • (1 : M2)) * X - X * cornerLift (r • (1 : M2)) =
      r • (modelProjection * X - X * modelProjection) := by
  rw [cornerLift_scalar]
  exact scalar_commutator r _ X

/-- The nonzero-scalar assumption is essential. -/
theorem lifted_scalar_commutes_iff (r : ℝ) (hr : r ≠ 0) (X : Operator) :
    cornerLift (r • (1 : M2)) * X = X * cornerLift (r • (1 : M2)) ↔
      modelProjection * X * (1 - modelProjection) = 0 ∧
        (1 - modelProjection) * X * modelProjection = 0 := by
  rw [← sub_eq_zero, lifted_scalar_commutator, smul_eq_zero]
  simp only [hr, false_or, sub_eq_zero]
  exact commutes_iff_block_diagonal _ X modelProjection_idempotent

/-- The existing phonon creation operator actually mixes the selected corner
with its complement, rather than merely providing a hypothetical condition. -/
theorem projection_not_commute_phononCreation :
    modelProjection * phononCreation ≠ phononCreation * modelProjection := by
  intro h
  have hc := congrArg (fun T : Operator => (T (modelEmbed ![0, 1]) 2 2).a) h
  change (0 : ℝ) = 1 at hc
  exact zero_ne_one hc

end InfoGeometry.Physics.NuclearCornerCyclicBridge
