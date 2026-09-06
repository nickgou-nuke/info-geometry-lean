import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Instances.Matrix
import InfoGeometry.Canonical.NonAbelianFusionFRBridge

/-!
# Topological realization of the non-Abelian fusion braid generators

The algebraic `F`/`R` owner supplies the Fibonacci fusion matrices and their
Artin relation.  This owner records their continuous left actions as
`TopCat` endomorphisms of the finite fusion space.  It does not identify a
topology or a completion beyond the stated scalar hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianFusionFRTopologicalBridge

open CategoryTheory
open Matrix
open InfoGeometry.Canonical.NonAbelianFusionFRBridge

variable {K : Type*} [CommRing K]
variable [TopologicalSpace K] [ContinuousAdd K] [ContinuousMul K]

abbrev FusionCarrier (K : Type*) := Matrix (Fin 2) (Fin 2) K

/-- Continuous left multiplication on the finite fusion matrix carrier. -/
def matrixLeftTopCatHom (M : FusionCarrier K) :
    TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K) :=
  TopCat.ofHom
    { toFun := fun X => M * X
      continuous_toFun := continuous_const.mul continuous_id }

@[simp]
theorem matrixLeftTopCatHom_apply (M X : FusionCarrier K) :
    matrixLeftTopCatHom M X = M * X := rfl

theorem matrixLeftTopCatHom_comp (M N : FusionCarrier K) :
    matrixLeftTopCatHom M ≫ matrixLeftTopCatHom N =
      matrixLeftTopCatHom (N * M) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change N * (M * X) = (N * M) * X
  simp only [Matrix.mul_assoc]

def fusionFLeftTopCatHom (a b : K) :
    TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K) :=
  matrixLeftTopCatHom (fMatrix K a b)

def fusionBraid1LeftTopCatHom (q1 q2 : K) :
    TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K) :=
  matrixLeftTopCatHom (braidGen1 K q1 q2)

def fusionBraid2LeftTopCatHom (a b q1 q2 : K) :
    TopCat.of (FusionCarrier K) ⟶ TopCat.of (FusionCarrier K) :=
  matrixLeftTopCatHom (braidGen2 K a b q1 q2)

theorem fusionFLeftTopCatHom_involutive (a b : K)
    (h_norm : a ^ 2 + b ^ 2 = 1) :
    fusionFLeftTopCatHom a b ≫ fusionFLeftTopCatHom a b =
      𝟙 (TopCat.of (FusionCarrier K)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change fMatrix K a b * (fMatrix K a b * X) = X
  rw [← Matrix.mul_assoc, fMatrix_sq K a b h_norm, Matrix.one_mul]

theorem fusionBraidLeftTopCatHom_artin (a b q1 q2 : K)
    (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 +
      a ^ 2 * q2 ^ 2 = 0) :
    fusionBraid1LeftTopCatHom q1 q2 ≫
        fusionBraid2LeftTopCatHom a b q1 q2 ≫
        fusionBraid1LeftTopCatHom q1 q2 =
      fusionBraid2LeftTopCatHom a b q1 q2 ≫
        fusionBraid1LeftTopCatHom q1 q2 ≫
        fusionBraid2LeftTopCatHom a b q1 q2 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change braidGen1 K q1 q2 *
      (braidGen2 K a b q1 q2 * (braidGen1 K q1 q2 * X)) =
    braidGen2 K a b q1 q2 *
      (braidGen1 K q1 q2 * (braidGen2 K a b q1 q2 * X))
  simpa only [Matrix.mul_assoc] using
    congrArg (fun M : FusionCarrier K => M * X)
      (nonAbelian_artin_braid_relation K a b q1 q2 h_norm h_braid)

end InfoGeometry.Canonical.NonAbelianFusionFRTopologicalBridge
