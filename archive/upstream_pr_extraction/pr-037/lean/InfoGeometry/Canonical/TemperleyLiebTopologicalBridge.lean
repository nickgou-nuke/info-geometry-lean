import InfoGeometry.Canonical.HeckeBraidTopologicalBridge
import InfoGeometry.Canonical.TemperleyLiebJonesBridge

/-!
# Topological transport of the Temperley--Lieb relations

The algebraic Temperley--Lieb owner supplies the loop and contraction
identities.  This file records their action on the topological carrier by
continuous left multiplication.  The carrier remains a noncommutative ring;
no matrix or commutative specialization is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.TemperleyLiebTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.HeckeBraidTopologicalBridge
open TemperleyLiebJonesBridge

variable {δ : ℂ} {R : Type*} [Ring R] [Algebra ℂ R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (sys : TemperleyLiebSystem δ R)

/-- The first Temperley--Lieb loop relation as a `TopCat` equality. -/
theorem tl_self_loop_1_leftTopCat_relation :
    leftMulTopCatHom sys.e1 ≫ leftMulTopCatHom sys.e1 =
      leftMulTopCatHom (δ • sys.e1) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change sys.e1 * (sys.e1 * x) = (δ • sys.e1) * x
  simpa only [mul_assoc] using congrArg (fun z : R => z * x) sys.self_loop_1

/-- The second Temperley--Lieb loop relation as a `TopCat` equality. -/
theorem tl_self_loop_2_leftTopCat_relation :
    leftMulTopCatHom sys.e2 ≫ leftMulTopCatHom sys.e2 =
      leftMulTopCatHom (δ • sys.e2) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change sys.e2 * (sys.e2 * x) = (δ • sys.e2) * x
  simpa only [mul_assoc] using congrArg (fun z : R => z * x) sys.self_loop_2

/-- The `e₁e₂e₁` contraction transported to continuous maps. -/
theorem tl_contraction_121_leftTopCat_relation :
    leftMulTopCatHom sys.e1 ≫ leftMulTopCatHom sys.e2 ≫
        leftMulTopCatHom sys.e1 = leftMulTopCatHom sys.e1 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change sys.e1 * (sys.e2 * (sys.e1 * x)) = sys.e1 * x
  simpa only [mul_assoc] using
    congrArg (fun z : R => z * x) sys.contraction_121

/-- The `e₂e₁e₂` contraction transported to continuous maps. -/
theorem tl_contraction_212_leftTopCat_relation :
    leftMulTopCatHom sys.e2 ≫ leftMulTopCatHom sys.e1 ≫
        leftMulTopCatHom sys.e2 = leftMulTopCatHom sys.e2 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change sys.e2 * (sys.e1 * (sys.e2 * x)) = sys.e2 * x
  simpa only [mul_assoc] using
    congrArg (fun z : R => z * x) sys.contraction_212

/-- Inserting the second loop between the first generators remains valid in
`TopCat`; this is the topological form of the four-fold loop reduction. -/
theorem tl_loop_insertion_1221_leftTopCat_relation :
    leftMulTopCatHom sys.e1 ≫ leftMulTopCatHom sys.e2 ≫
        leftMulTopCatHom sys.e2 ≫ leftMulTopCatHom sys.e1 =
      leftMulTopCatHom (δ • sys.e1) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change sys.e1 * (sys.e2 * (sys.e2 * (sys.e1 * x))) =
    (δ • sys.e1) * x
  simpa only [mul_assoc] using
    congrArg (fun z : R => z * x) (tl_loop_insertion_1221_eq sys)

end InfoGeometry.Canonical.TemperleyLiebTopologicalBridge
