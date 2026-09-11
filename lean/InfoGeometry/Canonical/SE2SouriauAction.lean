import InfoGeometry.Canonical.SE2SouriauCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The native topological `SE(2)` action on homogeneous points

The matrix representation and its multiplication law already live in the
cocycle owner.  This file exposes that representation as a Mathlib
`MulAction`, retaining the joint continuity theorem and the associated orbit
maps without asserting compactness for the full non-compact group.
-/

namespace InfoGeometry.Canonical.SE2SouriauCocycle

open InfoGeometry.Canonical.Barbaresco2020Souriau

abbrev SL3Carrier := Matrix.SpecialLinearGroup (Fin 3) ℝ

def specialLinearPointAction (A : SL3Carrier) (v : HomogeneousPoint) :
    HomogeneousPoint := Matrix.mulVec A.1 v

theorem specialLinearPointAction_mul
    (A B : SL3Carrier) (v : HomogeneousPoint) :
    specialLinearPointAction (A * B) v =
      specialLinearPointAction A (specialLinearPointAction B v) := by
  dsimp [specialLinearPointAction]
  rw [Matrix.mulVec_mulVec]

theorem specialLinearPointAction_one (v : HomogeneousPoint) :
    specialLinearPointAction (1 : SL3Carrier) v = v := by
  dsimp [specialLinearPointAction]
  rw [Matrix.one_mulVec]

instance : MulAction SL3Carrier HomogeneousPoint where
  smul := specialLinearPointAction
  one_smul := specialLinearPointAction_one
  mul_smul := specialLinearPointAction_mul

theorem continuous_specialLinearPointAction :
    Continuous (fun p : SL3Carrier × HomogeneousPoint =>
      p.1 • p.2) := by
  change Continuous (fun p : SL3Carrier × HomogeneousPoint =>
    Matrix.mulVec p.1.1 p.2)
  exact Continuous.matrix_mulVec
    (continuous_subtype_val.comp continuous_fst) continuous_snd

instance : ContinuousSMul SL3Carrier HomogeneousPoint where
  continuous_smul := continuous_specialLinearPointAction

theorem se2_action_factors_through_SL3
    (g : SE2RotationCarrier) (v : HomogeneousPoint) :
    se2MatrixAction g v =
      specialLinearPointAction (se2SpecialLinearRepresentation g) v := rfl

def se2SpecialLinearRepresentationContinuousMap :
    C(SE2RotationCarrier, SL3Carrier) :=
  { toFun := se2SpecialLinearRepresentation
    continuous_toFun := continuous_se2SpecialLinearRepresentation }

theorem se2SpecialLinearRepresentation_injective :
    Function.Injective se2SpecialLinearRepresentation := by
  intro g h hEq
  have hMatrix : se2MatrixRepresentation g = se2MatrixRepresentation h := by
    exact congrArg (fun A : SL3Carrier => A.1) hEq
  apply Subtype.ext
  apply Prod.ext
  · have h00 := congrFun (congrFun hMatrix 0) 0
    simpa [se2MatrixRepresentation, se2GroupMatrix] using h00
  · apply Prod.ext
    · have h10 := congrFun (congrFun hMatrix 1) 0
      simpa [se2MatrixRepresentation, se2GroupMatrix] using h10
    · apply Prod.ext
      · have h02 := congrFun (congrFun hMatrix 0) 2
        simpa [se2MatrixRepresentation, se2GroupMatrix] using h02
      · have h12 := congrFun (congrFun hMatrix 1) 2
        simpa [se2MatrixRepresentation, se2GroupMatrix] using h12

abbrev SE2RepresentationRange :=
  Set.range (se2SpecialLinearRepresentation : SE2RotationCarrier → SL3Carrier)

def se2RepresentationReadout (A : SE2RepresentationRange) :
    SE2RotationCarrier :=
  ⟨(A.1.1 0 0, A.1.1 1 0, A.1.1 0 2, A.1.1 1 2), by
    rcases A.2 with ⟨g, hg⟩
    rw [← hg]
    exact g.2⟩

theorem continuous_se2RepresentationReadout :
    Continuous se2RepresentationReadout := by
  unfold se2RepresentationReadout
  apply Continuous.subtype_mk
  have hmatrix : Continuous (fun A : SE2RepresentationRange => A.1.1) := by
    exact continuous_subtype_val.comp continuous_subtype_val
  have h00 := (continuous_apply 0).comp ((continuous_apply 0).comp hmatrix)
  have h10 := (continuous_apply 0).comp ((continuous_apply 1).comp hmatrix)
  have h02 := (continuous_apply 2).comp ((continuous_apply 0).comp hmatrix)
  have h12 := (continuous_apply 2).comp ((continuous_apply 1).comp hmatrix)
  exact h00.prodMk (h10.prodMk (h02.prodMk h12))

def se2RepresentationRangeHomeomorph :
    SE2RotationCarrier ≃ₜ SE2RepresentationRange where
  toFun := fun g => ⟨se2SpecialLinearRepresentation g, ⟨g, rfl⟩⟩
  invFun := se2RepresentationReadout
  left_inv := by
    intro g
    apply Subtype.ext
    rfl
  right_inv := by
    intro A
    rcases A with ⟨A, ⟨g, hg⟩⟩
    cases hg
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_se2SpecialLinearRepresentation
  continuous_invFun := continuous_se2RepresentationReadout

theorem se2SpecialLinearRepresentationContinuousMap_apply
    (g : SE2RotationCarrier) :
    se2SpecialLinearRepresentationContinuousMap g =
      se2SpecialLinearRepresentation g := rfl

def specialLinearOrbitMap (v : HomogeneousPoint) :
    SL3Carrier → HomogeneousPoint := fun A => A • v

theorem continuous_specialLinearOrbitMap (v : HomogeneousPoint) :
    Continuous (specialLinearOrbitMap v) := by
  unfold specialLinearOrbitMap
  simpa only [Function.comp_apply] using
    continuous_specialLinearPointAction.comp
      (continuous_id.prodMk continuous_const)

def specialLinearOrbitContinuousMap (v : HomogeneousPoint) :
    C(SL3Carrier, HomogeneousPoint) :=
  { toFun := specialLinearOrbitMap v
    continuous_toFun := continuous_specialLinearOrbitMap v }

def specialLinearOrbit (v : HomogeneousPoint) :
    Set HomogeneousPoint := Set.range (specialLinearOrbitMap v)

theorem specialLinearOrbitMap_mul (v : HomogeneousPoint)
    (A B : SL3Carrier) :
    specialLinearOrbitMap v (A * B) =
      specialLinearOrbitMap (specialLinearOrbitMap v B) A := by
  simp [specialLinearOrbitMap, mul_smul]

instance : MulAction SE2RotationCarrier HomogeneousPoint where
  smul := se2MatrixAction
  one_smul := se2MatrixAction_one
  mul_smul := se2MatrixAction_mul

theorem continuous_homogeneousPoint_action :
    Continuous (fun p : SE2RotationCarrier × HomogeneousPoint =>
      p.1 • p.2) := by
  simpa only [SMul.smul] using continuous_se2MatrixAction

instance : ContinuousSMul SE2RotationCarrier HomogeneousPoint where
  continuous_smul := continuous_homogeneousPoint_action

def homogeneousOrbitMap (v : HomogeneousPoint) :
    SE2RotationCarrier → HomogeneousPoint := fun g => g • v

theorem homogeneousOrbitMap_factorization (v : HomogeneousPoint) :
    homogeneousOrbitMap v =
      specialLinearOrbitMap v ∘ se2SpecialLinearRepresentation := by
  funext g
  exact se2_action_factors_through_SL3 g v

theorem continuous_homogeneousOrbitMap (v : HomogeneousPoint) :
    Continuous (homogeneousOrbitMap v) := by
  unfold homogeneousOrbitMap
  simpa only [Function.comp_apply] using
      continuous_homogeneousPoint_action.comp
      (continuous_id.prodMk continuous_const)

def homogeneousOrbitContinuousMap (v : HomogeneousPoint) :
    C(SE2RotationCarrier, HomogeneousPoint) :=
  { toFun := homogeneousOrbitMap v
    continuous_toFun := continuous_homogeneousOrbitMap v }

theorem homogeneousOrbitContinuousMap_factorization
  (v : HomogeneousPoint) :
    homogeneousOrbitContinuousMap v =
      (specialLinearOrbitContinuousMap v).comp
        se2SpecialLinearRepresentationContinuousMap := by
  ext g i
  exact congrFun (se2_action_factors_through_SL3 g v) i

theorem homogeneousOrbitContinuousMap_apply
    (v : HomogeneousPoint) (g : SE2RotationCarrier) :
    homogeneousOrbitContinuousMap v g = homogeneousOrbitMap v g := rfl

def homogeneousOrbit (v : HomogeneousPoint) :
    Set HomogeneousPoint := Set.range (homogeneousOrbitMap v)

theorem homogeneousOrbit_subset_specialLinearOrbit
    (v : HomogeneousPoint) :
    homogeneousOrbit v ⊆ specialLinearOrbit v := by
  intro x hx
  rcases hx with ⟨g, rfl⟩
  refine ⟨se2SpecialLinearRepresentation g, ?_⟩
  exact se2_action_factors_through_SL3 g v

theorem homogeneousOrbit_nonempty (v : HomogeneousPoint) :
    (homogeneousOrbit v).Nonempty := by
  exact ⟨v, ⟨1, one_smul SE2RotationCarrier v⟩⟩

theorem homogeneousOrbitMap_mul (v : HomogeneousPoint)
    (g h : SE2RotationCarrier) :
    homogeneousOrbitMap v (g * h) =
      homogeneousOrbitMap (homogeneousOrbitMap v h) g := by
  simp [homogeneousOrbitMap, mul_smul]

end InfoGeometry.Canonical.SE2SouriauCocycle
