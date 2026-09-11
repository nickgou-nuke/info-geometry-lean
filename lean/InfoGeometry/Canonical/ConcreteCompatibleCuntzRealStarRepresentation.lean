import InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Real-scalar analogue of the faithful norming representation contract. -/

noncomputable section
namespace CStarStateColimit.Native

universe u v

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℝ A]
variable {B : Type v} [CStarAlgebra B]

structure FaithfulRealStarRepresentation where
  rep : A →⋆ₐ[ℝ] B
  faithful : Function.Injective rep

namespace FaithfulRealStarRepresentation

variable (R : FaithfulRealStarRepresentation (A := A) (B := B))

def pulledNorm (a : A) : ℝ := ‖R.rep a‖

@[simp] theorem pulledNorm_zero : R.pulledNorm 0 = 0 := by
  simp [pulledNorm]

theorem pulledNorm_add_le (a b : A) :
    R.pulledNorm (a + b) ≤ R.pulledNorm a + R.pulledNorm b := by
  simpa [pulledNorm] using norm_add_le (R.rep a) (R.rep b)

theorem pulledNorm_mul_le (a b : A) :
    R.pulledNorm (a * b) ≤ R.pulledNorm a * R.pulledNorm b := by
  simpa [pulledNorm] using norm_mul_le (R.rep a) (R.rep b)

@[simp] theorem pulledNorm_neg (a : A) :
    R.pulledNorm (-a) = R.pulledNorm a := by
  simp [pulledNorm]

@[simp] theorem pulledNorm_star (a : A) :
    R.pulledNorm (star a) = R.pulledNorm a := by
  simp only [pulledNorm, map_star, norm_star]

theorem pulledNorm_eq_zero_iff (a : A) :
    R.pulledNorm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply R.faithful
    simpa using (norm_eq_zero.mp h)
  · intro h
    subst h
    exact R.pulledNorm_zero

def pulledRingNorm : RingNorm A where
  toFun := R.pulledNorm
  map_zero' := R.pulledNorm_zero
  add_le' := R.pulledNorm_add_le
  neg' := R.pulledNorm_neg
  eq_zero_of_map_eq_zero' := by
    intro a h
    exact (R.pulledNorm_eq_zero_iff a).mp h
  mul_le' := R.pulledNorm_mul_le

noncomputable def pulledNormedRing : NormedRing A :=
  RingNorm.toNormedRing R.pulledRingNorm

theorem rep_isometry :
    letI := R.pulledNormedRing
    Isometry R.rep := by
  letI := R.pulledNormedRing
  intro a b
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
  rw [← map_sub R.rep]
  rfl

end FaithfulRealStarRepresentation
end CStarStateColimit.Native

namespace InfoGeometry.Canonical.ConcreteCompatibleCuntzRealStarRepresentation

open InfoGeometry.Canonical.ConcreteCompatibleCuntzRepresentation
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness

theorem stageMap_algebraMap_real (n : ℕ) (r : ℝ) :
    stageMap n (algebraMap ℝ
      (InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n) r) =
        algebraMap ℝ BoundedL2Operator r := by
  change boundaryRep n (complexify n (clStageEquiv n (algebraMap ℝ
    (InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n) r))) = _
  rw [show clStageEquiv n (algebraMap ℝ
      (InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n) r) = r • 1 by
        simp [Algebra.algebraMap_eq_smul_one]]
  have hc : complexify n (r • (1 : UHFStage n)) =
      algebraMap ℝ ℂ r •
        (1 : InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.Stage n) := by
    by_cases hr : r = 0
    · subst r
      ext i j
      simp [complexify]
    · ext i j
      by_cases h : i = j <;> simp [complexify, h]
  rw [hc, map_smul]
  rw [show algebraMap ℝ BoundedL2Operator r =
      algebraMap ℂ BoundedL2Operator (algebraMap ℝ ℂ r) by
        rfl]
  simp [Algebra.smul_def]

def colimitStarAlgHom :
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier →⋆ₐ[ℝ]
      BoundedL2Operator where
  toFun := colimitRepresentation
  map_one' := colimitRepresentation.map_one
  map_mul' := colimitRepresentation.map_mul
  map_zero' := colimitRepresentation.map_zero
  map_add' := colimitRepresentation.map_add
  commutes' := by
    intro r
    change colimitRepresentation (realAlgebraMap r) = algebraMap ℝ BoundedL2Operator r
    rw [realAlgebraMap_stage 0 r]
    rw [colimitRepresentation_stage]
    exact stageMap_algebraMap_real 0 r
  map_star' := by
    intro x
    induction x using DirectLimit.induction with
    | _ n A =>
        change colimitRepresentation (star (ofStage n A)) =
          (colimitRepresentation (ofStage n A))†
        rw [← ofStage_star]
        rw [colimitRepresentation_stage, colimitRepresentation_stage]
        exact stageMap_star n A

theorem colimitStarAlgHom_injective :
    Function.Injective colimitStarAlgHom := by
  exact colimitRepresentation_injective

noncomputable def concreteFaithfulRealStarRepresentation :
    CStarStateColimit.Native.FaithfulRealStarRepresentation
      (A := InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier)
      (B := BoundedL2Operator) where
  rep := colimitStarAlgHom
  faithful := colimitStarAlgHom_injective

abbrev colimitPulledRingNorm :
    RingNorm InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier :=
  CStarStateColimit.Native.FaithfulRealStarRepresentation.pulledRingNorm
    concreteFaithfulRealStarRepresentation

theorem colimitPulledRingNorm_eq_zero_iff
    (x : InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier) :
    colimitPulledRingNorm x = 0 ↔ x = 0 :=
  CStarStateColimit.Native.FaithfulRealStarRepresentation.pulledNorm_eq_zero_iff
    concreteFaithfulRealStarRepresentation x

/-! The genuine metric completion is now a standard Mathlib completion of the
faithful transported norm; no ad hoc infinite object is introduced. -/

noncomputable def colimitCompletion : Type :=
  letI := CStarStateColimit.Native.FaithfulRealStarRepresentation.pulledNormedRing
    concreteFaithfulRealStarRepresentation
  UniformSpace.Completion
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier

theorem colimitCompletion_dense :
    letI := CStarStateColimit.Native.FaithfulRealStarRepresentation.pulledNormedRing
      concreteFaithfulRealStarRepresentation
    DenseRange ((↑) :
      InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier →
        UniformSpace.Completion
          InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier) := by
  letI := CStarStateColimit.Native.FaithfulRealStarRepresentation.pulledNormedRing
    concreteFaithfulRealStarRepresentation
  exact UniformSpace.Completion.denseRange_coe

end InfoGeometry.Canonical.ConcreteCompatibleCuntzRealStarRepresentation
end noncomputable section
